//! This pass implement vectorization of mir

use crate::simplify;
use itertools::Itertools;
use rustc_data_structures::fx::FxHashSet;
use rustc_data_structures::stable_map::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_index::vec::{Idx, IndexVec};
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::visit::{MutVisitor, MutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::BinOp;
use rustc_middle::mir::StatementKind::*;
use rustc_middle::mir::TerminatorKind::*;
use rustc_middle::mir::*;
use rustc_middle::ty::{self, Const, Ty, TyCtxt, TypeAndMut};
use rustc_span::symbol::sym;
use rustc_span::{Symbol, DUMMY_SP};
use std::io::{self, Write};
use ExtraStmt::*;
use LocalUse::*;
use VectorStmt::*;

pub struct Vectorize;

#[derive(Default, Debug)]
pub struct VectorResolver<'tcx> {
    vector_len: Option<u64>,
    loops: Vec<(Vec<BasicBlock> /* pre_loop */, Vec<BasicBlock> /* loop */)>,
    break_points: FxHashSet<BasicBlock>,
    break_blocks: Vec<BasicBlock>,

    conditions: FxHashSet<Local>,
    locals_use: IndexVec<Local, LocalUse>,

    loop_stmts: Vec<ExtraStmt<'tcx>>,

    temp_to_vector: FxHashMap<Local, Local>,
    no_read_after_vector: FxHashMap<Place<'tcx>, Local>,
    no_reset_after_vector: FxHashMap<Place<'tcx>, Local>,
    condi_vector: FxHashSet<Local>,
    range_condi: FxHashSet<Local>,

    resolved_stmts_pre: Vec<VectorStmt<'tcx>>,
    resolved_stmts: Vec<VectorStmt<'tcx>>,
}

#[derive(Debug, Copy, Clone, PartialOrd, Ord, Eq, PartialEq)]
enum LocalUse {
    InLoop,
    PreLoop,
    AfterLoop,
    Condition,
}

#[derive(Debug, Clone)]
enum ExtraStmt<'tcx> {
    CondiStorage(Location, BitSet<Local>),
    CondiGet(Place<'tcx>, Rvalue<'tcx>, BitSet<Local>),
    CondiSet(Place<'tcx>, Rvalue<'tcx>, BitSet<Local>),

    AfterGet(Place<'tcx>, Rvalue<'tcx>, BitSet<Local>, Location),
    AfterSet(Place<'tcx>, Rvalue<'tcx>, BitSet<Local>, Location),

    TempStorage(Location),
    TempAssign(Place<'tcx>, Rvalue<'tcx>, BitSet<Local>, Location),

    BreakTerminator(Location, BitSet<Local>),
    SetCondiTerminator(Location, BitSet<Local>),
    GetCondiTerminator(Location, BitSet<Local>),

    GotoTerminator(Location),
    EndLoopTerminator(Location),
    TempFuncTerminator(Location, Place<'tcx>, BitSet<Local>),

    OtherTerminator(Location),
    ResumeAfter(Place<'tcx>),
}

impl ExtraStmt<'_> {
    /*fn bitset(&self) -> Option<BitSet<Local>> {
        match self {
            CondiStorage(_, bitset)
            | CondiGet(_, bitset)
            | CondiSet(_, bitset)
            | BreakTerminator(_, bitset)
            | SetCondiTerminator(_, bitset)
            | GetCondiTerminator(_, bitset) => Some(bitset.clone()),
            _ => None,
        }
    }*/

    fn is_condi(&self) -> bool {
        match self {
            CondiStorage(..)
            | CondiGet(..)
            | CondiSet(..)
            | BreakTerminator(..)
            | SetCondiTerminator(..)
            | GetCondiTerminator(..) => true,
            _ => false,
        }
    }

    fn move_up(&self, above: &Self) -> bool {
        match (self, above) {
            (BreakTerminator(..), _) | (_, BreakTerminator(..)) => return false,
            _ => {}
        };
        if self.is_condi() {
            if above.is_condi() { false } else { true }
        } else {
            false
        }
    }
}

impl<'tcx> MirPass<'tcx> for Vectorize {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let vectorize = tcx
            .get_attrs(body.source.def_id())
            .into_iter()
            .find(|a| a.has_name(sym::vectorization))
            .is_some();
        if !vectorize {
            return;
        }
        let _: io::Result<()> = try {
            let mut file = create_dump_file(
                tcx,
                "txt",
                None,
                self.name().as_ref(),
                &"before".to_string(),
                body.source,
            )?;
            write!(file, "start vectorization")?;
            writeln!(file)?;

            let mut resolver = VectorResolver::default();

            resolver.resolve_loops(body);
            if resolver.loops.len() != 1 {
                unimplemented!("too many loops");
            }
            writeln!(file, "loops:{:?}", resolver.loops)?;

            resolver.resolve_conditions(body);
            if resolver.break_points.len() != 1 {
                unimplemented!("different break targets");
            }
            writeln!(file, "break points:{:?}", resolver.break_points)?;
            writeln!(file, "conditions:{:?}", resolver.conditions)?;

            writeln!(file, "local_use")?;
            resolver.resolve_locals(body);
            for (index, luse) in resolver.locals_use.iter().enumerate() {
                writeln!(file, "{:?} : {:?}", index, luse)?;
            }
            writeln!(file)?;

            writeln!(file, "before sorting:")?;
            resolver.resolve_stmts(body);
            for ex_stmt in &resolver.loop_stmts {
                writeln!(file, "{:?}", ex_stmt)?;
            }
            writeln!(file)?;

            writeln!(file, "after sorting:")?;
            resolver.resort_stmts();
            for ex_stmt in &resolver.loop_stmts {
                writeln!(file, "{:?}", ex_stmt)?;
            }
            writeln!(file)?;

            writeln!(file, "iter condi:")?;
            resolver.resolve_iter_condi(body, tcx);
            for local in &resolver.range_condi {
                writeln!(file, "{:?}", local)?;
            }
            writeln!(file)?;

            resolver.generate_blocks(tcx, body);

            writeln!(file, "temp to vectors:")?;
            for (key, val) in resolver.temp_to_vector.iter() {
                writeln!(file, "{:?} -> {:?}", key, val)?;
            }
            writeln!(file)?;

            writeln!(file, "no read temp vectors:")?;
            for (key, val) in resolver.no_read_after_vector.iter() {
                writeln!(file, "{:?} -> {:?}", key, val)?;
            }
            writeln!(file)?;

            writeln!(file, "no reset temp vectors:")?;
            for (key, val) in resolver.no_reset_after_vector.iter() {
                writeln!(file, "{:?} -> {:?}", key, val)?;
            }
            writeln!(file)?;

            writeln!(file, "resolved stmts before resort:")?;
            for stmt in &resolver.resolved_stmts_pre {
                writeln!(file, "{:?}", stmt)?;
            }
            writeln!(file)?;

            writeln!(file, "resolved stmts:")?;
            for stmt in &resolver.resolved_stmts {
                writeln!(file, "{:?}", stmt)?;
            }
            writeln!(file)?;
        };
        simplify::remove_dead_blocks(tcx, body);
        //simplify::simplify_locals(body, tcx);
    }
}

#[derive(Debug, Clone)]
enum VectorStmt<'tcx> {
    StraightStmt(Statement<'tcx>),
    StraightTerm(Terminator<'tcx>),

    BinOpAfterSet(Place<'tcx>, BinOp, Operand<'tcx>, Operand<'tcx>),
    BinOpAssign(Place<'tcx>, BinOp, Operand<'tcx>, Operand<'tcx>),
    Cast(Place<'tcx>, Operand<'tcx>, Ty<'tcx>),
    ReadVector(Place<'tcx>, Place<'tcx>, Local),

    VectorTerm(Symbol, Vec<Operand<'tcx>>, Place<'tcx>),

    UseAssign(Place<'tcx>, Operand<'tcx>),

    InnerLoopStmt(ExtraStmt<'tcx>),
}

#[derive(Debug, Clone)]
enum RemainStmt<'tcx> {
    InitAfterVector(Place<'tcx>, BinOp),
    SetAfterReduce(Place<'tcx>, BinOp),
    DeadAfter(Local),
}

pub struct PlaceToVector<'tcx> {
    tcx: TyCtxt<'tcx>,
    temp: Local,
    vector: Local,
    inner: Local,
}
impl<'tcx> MutVisitor<'tcx> for PlaceToVector<'tcx> {
    fn visit_place(
        &mut self,
        place: &mut Place<'tcx>,
        _context: PlaceContext,
        _location: Location,
    ) {
        if place.local == self.temp {
            let mut projection = vec![PlaceElem::Index(self.inner)];
            projection.extend(place.projection.iter());
            *place =
                Place { local: self.vector, projection: self.tcx.intern_place_elems(&projection) }
        }
    }

    fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

fn is_unreachable_block(bb: BasicBlock, body: &Body<'_>) -> bool {
    let block = &body[bb];
    block.statements.is_empty()
        && matches!(block.terminator, Some(Terminator { source_info: _, kind: Unreachable }))
}

impl<'tcx> VectorResolver<'tcx> {
    fn resolve_loops(&mut self, body: &Body<'_>) {
        let mut cur_bbs = vec![START_BLOCK];
        let mut successors = vec![body[START_BLOCK].terminator().successors()];

        while let Some(successor) = successors.last_mut() {
            if let Some(bb) = successor.next() {
                if let Some(pos) = cur_bbs.iter().find_position(|cur| *cur == bb) {
                    self.loops.push((cur_bbs[0..pos.0].to_vec(), cur_bbs[pos.0..].to_vec()));
                } else {
                    cur_bbs.push(*bb);
                    successors.push(body[*bb].terminator().successors());
                }
            } else {
                successors.pop();
                cur_bbs.pop();
            }
        }
    }

    fn resolve_conditions<'r>(&'r mut self, body: &Body<'tcx>) {
        let pre_lp = self.loops[0].0.clone();
        let lp = self.loops[0].1.clone();
        for bb in &lp {
            match &body[*bb].terminator().kind {
                SwitchInt { discr, switch_ty: _, targets } => {
                    let mut is_condi = false;
                    targets.all_targets().into_iter().for_each(|bb| {
                        if lp.iter().all(|target| target != bb) {
                            if !is_unreachable_block(*bb, body) {
                                self.break_points.insert(*bb);
                            }
                            is_condi = true;
                        }
                    });
                    if is_condi {
                        if let Some(local) = discr.place().map(|place| place.local) {
                            self.break_blocks.push(*bb);
                            self.conditions.insert(local);
                        }
                    }
                }
                _ => continue,
            }
        }
        pub struct ConditionResolver<'r, 'tcx> {
            r: &'r mut VectorResolver<'tcx>,
            changed: bool,
        }
        impl Visitor<'_> for ConditionResolver<'_, '_> {
            fn visit_statement(&mut self, statement: &Statement<'_>, location: Location) {
                if let Assign(assign) = &statement.kind {
                    let (place, rvalue) = assign.as_ref();
                    if self.r.conditions.contains(&place.local) {
                        self.visit_rvalue(rvalue, location);
                    }
                }
            }

            fn visit_terminator(&mut self, terminator: &Terminator<'_>, location: Location) {
                match &terminator.kind {
                    DropAndReplace { place, value, target: _, unwind: _ }
                        if self.r.conditions.contains(&place.local) =>
                    {
                        self.visit_operand(value, location);
                    }
                    Call {
                        func,
                        args,
                        destination: Some(place),
                        cleanup: _,
                        from_hir_call: _,
                        fn_span: _,
                    } if self.r.conditions.contains(&place.0.local) => {
                        self.visit_operand(func, location);
                        for op in args {
                            self.visit_operand(op, location);
                        }
                    }
                    _ => {}
                }
            }

            fn visit_local(&mut self, local: &Local, _context: PlaceContext, _location: Location) {
                self.changed = self.r.conditions.insert(*local);
            }
        }
        let mut con_resolver = ConditionResolver { changed: !self.conditions.is_empty(), r: self };
        while con_resolver.changed {
            con_resolver.changed = false;
            for bb in pre_lp.iter().chain(lp.iter()) {
                con_resolver.visit_basic_block_data(*bb, &body[*bb]);
            }
        }
    }

    fn resolve_locals<'r>(&'r mut self, body: &Body<'tcx>) {
        let pre_lp = FxHashSet::from_iter(self.loops[0].0.clone());
        let lp = FxHashSet::from_iter(self.loops[0].1.clone());
        let after_lp: FxHashSet<BasicBlock> = (0..body.basic_blocks().len())
            .map(|u| BasicBlock::new(u))
            .filter(|bb| !pre_lp.contains(bb) && !lp.contains(bb))
            .collect();

        self.locals_use = IndexVec::from_elem(InLoop, &body.local_decls);
        struct LocalResolver<'r, 'tcx> {
            r: &'r mut VectorResolver<'tcx>,
            local_use: LocalUse,
        }

        (1..1 + body.arg_count).for_each(|u| self.locals_use[Local::new(u)] = PreLoop);

        impl<'r, 'tcx> Visitor<'tcx> for LocalResolver<'r, 'tcx> {
            fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
                if let StorageLive(..) | StorageDead(..) = statement.kind {
                    // skip
                } else {
                    self.super_statement(statement, location);
                }
            }

            fn visit_local(&mut self, local: &Local, _context: PlaceContext, _location: Location) {
                self.r.locals_use[*local] = self.local_use;
            }
        }

        let mut pre_resolver = LocalResolver { r: self, local_use: PreLoop };
        for bb in pre_lp.into_iter() {
            pre_resolver.visit_basic_block_data(bb, &body[bb]);
        }

        self.locals_use[Local::new(0)] = AfterLoop;
        let mut after_resolver = LocalResolver { r: self, local_use: AfterLoop };
        for bb in after_lp.into_iter() {
            after_resolver.visit_basic_block_data(bb, &body[bb]);
        }

        for local in self.conditions.iter() {
            self.locals_use[*local] = Condition;
        }
        let mut changed = true;
        while changed {
            changed = false;
            for bb in lp.iter() {
                for stmt in &body[*bb].statements {
                    match &stmt.kind {
                        Assign(assign) => {
                            let (place, rvalue) = assign.as_ref();
                            if let Rvalue::Ref(_, BorrowKind::Mut { .. }, ref_place) = rvalue {
                                if self.locals_use[ref_place.local] == AfterLoop
                                    && self.locals_use[place.local] == InLoop
                                {
                                    changed = true;
                                    self.locals_use[place.local] = AfterLoop;
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    fn resolve_stmts<'r>(&'r mut self, body: &'r Body<'tcx>) {
        pub struct StmtResoler<'r, 'tcx> {
            r: &'r mut VectorResolver<'tcx>,
            current_use: LocalUse,
            locals: BitSet<Local>,
        }

        impl<'tcx> Visitor<'tcx> for StmtResoler<'_, 'tcx> {
            fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
                self.locals.clear();
                match &statement.kind {
                    StorageLive(local) | StorageDead(local) => {
                        self.locals.insert(*local);
                        match self.r.locals_use[*local] {
                            Condition => {
                                self.r.loop_stmts.push(CondiStorage(location, self.locals.clone()))
                            }
                            _ => self.r.loop_stmts.push(TempStorage(location)),
                        }
                    }
                    Assign(assign) => {
                        let (place, rvalue) = assign.as_ref();
                        self.current_use = InLoop;
                        self.visit_place(
                            place,
                            PlaceContext::MutatingUse(MutatingUseContext::Store),
                            location,
                        );
                        let left_use = self.current_use;
                        let mut left_locals = self.locals.clone();
                        self.locals.clear();

                        self.current_use = InLoop;
                        self.visit_rvalue(rvalue, location);
                        let right_use = self.current_use;
                        let right_locals = self.locals.clone();

                        match (left_use, right_use) {
                            (Condition, _) => {
                                left_locals.union(&right_locals);
                                self.r.loop_stmts.push(CondiSet(
                                    *place,
                                    rvalue.clone(),
                                    left_locals,
                                ))
                            }
                            (InLoop, Condition) => {
                                left_locals.union(&right_locals);
                                self.r.loop_stmts.push(CondiGet(
                                    *place,
                                    rvalue.clone(),
                                    left_locals,
                                ));
                            }
                            (InLoop, InLoop) => self.r.loop_stmts.push(TempAssign(
                                *place,
                                rvalue.clone(),
                                right_locals,
                                location,
                            )),
                            (InLoop, PreLoop | AfterLoop) => self.r.loop_stmts.push(AfterGet(
                                *place,
                                rvalue.clone(),
                                right_locals,
                                location,
                            )),
                            (PreLoop | AfterLoop, _) => self.r.loop_stmts.push(AfterSet(
                                *place,
                                rvalue.clone(),
                                right_locals,
                                location,
                            )),
                        }
                    }
                    _ => unimplemented!("stmt resolve fail on {:?}", location),
                }
            }

            fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
                self.locals.clear();
                match &terminator.kind {
                    SwitchInt { discr, switch_ty: _, targets: _ } => {
                        self.visit_operand(discr, location);
                        if self.r.break_blocks.contains(&location.block) {
                            self.r.loop_stmts.push(BreakTerminator(location, self.locals.clone()));
                        } else {
                            unimplemented!("switch resolve fail on {:?}", location)
                        }
                    }
                    Goto { target } => {
                        if target == &self.r.loops[0].1[0] {
                            self.r.loop_stmts.push(EndLoopTerminator(location))
                        } else {
                            self.r.loop_stmts.push(GotoTerminator(location))
                        }
                    }
                    Call { func, args, destination, cleanup: _, from_hir_call: _, fn_span: _ } => {
                        self.current_use = InLoop;
                        for op in args.iter().chain(Some(func)) {
                            self.visit_operand(op, location);
                        }
                        let right_locals = self.locals.clone();
                        let arg_use = self.current_use;

                        self.current_use = InLoop;
                        if let Some(place) = destination {
                            self.visit_place(
                                &place.0,
                                PlaceContext::MutatingUse(MutatingUseContext::Store),
                                location,
                            );
                        }
                        let return_use = self.current_use;

                        match (return_use, arg_use) {
                            (Condition, _) => self
                                .r
                                .loop_stmts
                                .push(SetCondiTerminator(location, self.locals.clone())),
                            (InLoop, Condition) => self
                                .r
                                .loop_stmts
                                .push(GetCondiTerminator(location, self.locals.clone())),
                            (InLoop, InLoop) => {
                                self.r.loop_stmts.push(TempFuncTerminator(
                                    location,
                                    destination.unwrap().0.clone(),
                                    right_locals,
                                ));
                            }
                            _ => {
                                unimplemented!(
                                    "call resolve fail on {:?},\n mir: {:?}",
                                    terminator.kind,
                                    location
                                )
                            }
                        }
                    }
                    _ => {
                        self.r.loop_stmts.push(OtherTerminator(location));
                    }
                }
            }

            fn visit_local(&mut self, local: &Local, _context: PlaceContext, _location: Location) {
                self.locals.insert(*local);
                if self.current_use < self.r.locals_use[*local] {
                    self.current_use = self.r.locals_use[*local];
                }
            }
        }
        let mut stmt_resolver = StmtResoler {
            r: self,
            current_use: InLoop,
            locals: BitSet::new_empty(body.local_decls.len()),
        };
        for bb in stmt_resolver.r.loops[0].1.clone() {
            stmt_resolver.visit_basic_block_data(bb, &body[bb])
        }
    }

    fn resolve_iter_condi<'r>(&'r mut self, body: &Body<'tcx>, tcx: TyCtxt<'tcx>) {
        let mut changed = true;
        while changed {
            changed = false;
            for stmt in &self.loop_stmts {
                match stmt {
                    SetCondiTerminator(location, _) => {
                        if let Call {
                            func,
                            args,
                            destination: Some(place),
                            cleanup: _,
                            from_hir_call: _,
                            fn_span: _,
                        } = &body[location.block].terminator().kind
                        {
                            let fn_ty = func.constant().unwrap().ty();
                            let func_str = if let ty::FnDef(def_id, _) = fn_ty.kind() {
                                tcx.def_path(*def_id).to_string_no_crate_verbose()
                            } else {
                                bug!("wrong func call")
                            };
                            if func_str.as_str() == "::iter::range::RangeIteratorImpl::spec_next" {
                                if let ty::Ref(_, ty, _) = args[0].ty(body, tcx).kind() {
                                    if let ty::Adt(adt, subs) = ty.kind() {
                                        let range_name =
                                            tcx.def_path(adt.did).to_string_no_crate_verbose();
                                        if range_name == "::ops::range::Range" {
                                            let item_type = subs[0].expect_ty();
                                            if item_type == tcx.types.usize {
                                                if self
                                                    .range_condi
                                                    .insert(place.0.as_local().unwrap())
                                                {
                                                    changed = true;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    CondiSet(place, rvalue, _)
                    | CondiGet(place, rvalue, _)
                    | TempAssign(place, rvalue, _, _) => match rvalue {
                        Rvalue::Discriminant(p) => {
                            if self.range_condi.contains(&p.as_local().unwrap())
                                && self.range_condi.insert(place.as_local().unwrap())
                            {
                                changed = true;
                            }
                        }
                        Rvalue::Use(op) => {
                            if let Some(p) = op.place() {
                                if self.range_condi.contains(&p.local)
                                    && self.range_condi.insert(place.as_local().unwrap())
                                {
                                    changed = true;
                                }
                            }
                        }
                        _ => {}
                    },
                    _ => {}
                }
            }
        }
    }

    fn resort_stmts<'r>(&'r mut self) {
        let mut index = 0;
        for i in (0..self.loop_stmts.len()).rev() {
            match &self.loop_stmts[i] {
                BreakTerminator(..) => {
                    index = i;
                    break;
                }
                _ => {}
            }
        }
        for i in index + 1..self.loop_stmts.len() {
            for j in (1..i + 1).rev() {
                if self.loop_stmts[j].move_up(&self.loop_stmts[j - 1]) {
                    self.loop_stmts.swap(j, j - 1);
                } else {
                    break;
                }
            }
        }
    }

    fn resolve_segments<'r>(&'r mut self) -> (Vec<ExtraStmt<'tcx>>, Vec<ExtraStmt<'tcx>>) {
        let mut index = 0;
        for i in (0..self.loop_stmts.len()).rev() {
            if self.loop_stmts[i].is_condi() {
                index = i + 1;
                break;
            }
        }
        let (inner, vect) = self.loop_stmts.split_at(index);
        (inner.to_vec(), vect.to_vec())
    }

    fn get_vector(&self, temp: &Place<'tcx>) -> Option<Local> {
        if let Some(vec) = self.temp_to_vector.get(&temp.local) {
            Some(*vec)
        } else if let Some(vec) = self.no_read_after_vector.get(temp) {
            Some(*vec)
        } else if let Some(vec) = self.no_reset_after_vector.get(temp) {
            Some(*vec)
        } else {
            None
        }
    }

    fn insert_vector(
        &mut self,
        temp: &Local,
        tcx: TyCtxt<'tcx>,
        body: &mut Body<'tcx>,
        is_condi: bool,
    ) -> bool {
        if self.temp_to_vector.get(temp).is_some() {
            false
        } else {
            let mut ty = body.local_decls[*temp].ty;
            if !self.condi_vector.contains(temp) {}
            if !is_condi {
                while !ty.is_primitive() {
                    match ty.kind() {
                        ty::Ref(_, ref_ty, _)
                        | ty::RawPtr(ty::TypeAndMut { ty: ref_ty, mutbl: _ })
                        | ty::Slice(ref_ty) => {
                            ty = ref_ty.clone();
                        }
                        _ => {
                            unimplemented!("not supported ty: {:?}", ty)
                        }
                    }
                }
            }
            let v = body
                .local_decls
                .push(LocalDecl::new(tcx.mk_array(ty, self.vector_len.unwrap()), DUMMY_SP));
            self.temp_to_vector.insert(*temp, v);
            if ty.is_primitive() {
                body.local_decls[v].vector = true;
            }
            true
        }
    }

    fn generate_condi_section<'r>(
        &'r mut self,
        tcx: TyCtxt<'tcx>,
        body: &mut Body<'tcx>,
        outer_loop: BasicBlock,
        inner: Local,
        condi_stmts: &Vec<ExtraStmt<'tcx>>,
        to_inner_break: &mut Vec<BasicBlock>,
        to_remain_init: &mut Vec<BasicBlock>,
    ) {
        let source_info = SourceInfo { span: DUMMY_SP, scope: OUTERMOST_SOURCE_SCOPE };
        let pre_loop = *self.loops[0].0.last().unwrap();
        let start_loop = self.loops[0].1[0];
        let term = body[pre_loop].terminator_mut();
        if let Goto { target } = term.kind {
            assert_eq!(target, start_loop);
            term.kind = Goto { target: outer_loop };
        } else {
            bug!("wrong pre loop");
        }
        body[outer_loop].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(inner),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    span: DUMMY_SP,
                    user_ty: None,
                    literal: Const::from_usize(tcx, 0).into(),
                }))),
            ))),
        });
        let inner_loop = body.basic_blocks_mut().push(BasicBlockData::new(None));
        body[outer_loop].terminator =
            Some(Terminator { source_info, kind: Goto { target: inner_loop } });

        let temp1 = body.local_decls.push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
        body[inner_loop].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(temp1),
                Rvalue::Use(Operand::Copy(Place::from(inner))),
            ))),
        });
        let temp2 = body.local_decls.push(LocalDecl::new(tcx.types.bool, DUMMY_SP));
        body[inner_loop].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(temp2),
                Rvalue::BinaryOp(
                    BinOp::Ge,
                    Box::new((
                        Operand::Move(Place::from(temp1)),
                        Operand::Constant(Box::new(Constant {
                            span: DUMMY_SP,
                            user_ty: None,
                            literal: Const::from_usize(tcx, self.vector_len.unwrap()).into(),
                        })),
                    )),
                ),
            ))),
        });
        let mut block = body.basic_blocks_mut().push(BasicBlockData::new(None));
        body[inner_loop].terminator = Some(Terminator {
            source_info,
            kind: SwitchInt {
                discr: Operand::Move(Place::from(temp2)),
                switch_ty: tcx.types.bool,
                targets: SwitchTargets::static_if(0, block, START_BLOCK),
            },
        });
        to_inner_break.push(inner_loop);

        for stmt in condi_stmts {
            match stmt {
                CondiStorage(location, _) | TempStorage(location) => {
                    let st = body[location.block].statements[location.statement_index].clone();
                    body[block].statements.push(st);
                }
                SetCondiTerminator(location, _) => {
                    let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    let kind = body[location.block].terminator().kind.clone();
                    if let Call {
                        func,
                        args,
                        destination: Some((place, _)),
                        cleanup,
                        from_hir_call,
                        fn_span,
                    } = kind
                    {
                        body[block].terminator = Some(Terminator {
                            source_info,
                            kind: Call {
                                func,
                                args,
                                destination: Some((place, next)),
                                cleanup,
                                from_hir_call,
                                fn_span,
                            },
                        });
                        block = next;
                    } else {
                        bug!("wrong set condi terminator: {:?}", stmt)
                    }
                }
                CondiSet(place, rvalue, _)
                | AfterGet(place, rvalue, _, _)
                | TempAssign(place, rvalue, _, _) => {
                    body[block].statements.push(Statement {
                        source_info,
                        kind: Assign(Box::new((*place, rvalue.clone()))),
                    });
                }
                BreakTerminator(location, _) => {
                    let term = body[location.block].terminator();
                    let pos = self.loops[0]
                        .1
                        .iter()
                        .enumerate()
                        .find(|(_, lp_bb)| **lp_bb == location.block)
                        .unwrap()
                        .0;
                    if let SwitchInt { discr, switch_ty, targets } = term.kind.clone() {
                        let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                        let mut new_targets = targets.clone();
                        for bb in new_targets.all_targets_mut() {
                            assert_ne!(*bb, START_BLOCK);
                            if self.break_points.get(bb).is_some() {
                                *bb = START_BLOCK;
                            } else if is_unreachable_block(*bb, body) {
                                // nothing to do
                            } else {
                                assert_eq!(self.loops[0].1[pos + 1], *bb);
                                *bb = next;
                            }
                        }
                        body[block].terminator = Some(Terminator {
                            source_info,
                            kind: SwitchInt {
                                discr: discr.clone(),
                                switch_ty,
                                targets: new_targets,
                            },
                        });
                        to_remain_init.push(block);
                        block = next;
                    } else {
                        unimplemented!("resolve break terminator failed: {:?}", stmt)
                    }
                }
                CondiGet(place, rvalue, _) => {
                    let temp_simd = self.get_vector(place).unwrap();
                    let des = Place {
                        local: temp_simd,
                        projection: tcx.intern_place_elems(&[PlaceElem::Index(inner)]),
                    };
                    body[block].statements.push(Statement {
                        source_info,
                        kind: Assign(Box::new((des, rvalue.clone()))),
                    })
                }
                _ => unimplemented!("resolve condi stmt failed: {:?}", stmt),
            }
        }

        body[block].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(inner),
                Rvalue::BinaryOp(
                    BinOp::Add,
                    Box::new((
                        Operand::Copy(Place::from(inner)),
                        Operand::Constant(Box::new(Constant {
                            span: DUMMY_SP,
                            user_ty: None,
                            literal: Const::from_usize(tcx, 1 as u64).into(),
                        })),
                    )),
                ),
            ))),
        });
        body[block].terminator =
            Some(Terminator { source_info, kind: Goto { target: inner_loop } });
    }

    fn new_inner_loop<'r>(
        &'r mut self,
        tcx: TyCtxt<'tcx>,
        body: &mut Body<'tcx>,
        current: BasicBlock,
        stmts: Vec<ExtraStmt<'tcx>>,
        inner: Local,
    ) -> BasicBlock {
        let source_info = SourceInfo { span: DUMMY_SP, scope: OUTERMOST_SOURCE_SCOPE };
        body[current].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(inner),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    span: DUMMY_SP,
                    user_ty: None,
                    literal: Const::from_usize(tcx, 0).into(),
                }))),
            ))),
        });
        let loop_start = body.basic_blocks_mut().push(BasicBlockData::new(None));
        body[current].terminator =
            Some(Terminator { source_info, kind: Goto { target: loop_start } });
        let temp1 = body.local_decls.push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
        body[loop_start].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(temp1),
                Rvalue::Use(Operand::Copy(Place::from(inner))),
            ))),
        });
        let temp2 = body.local_decls.push(LocalDecl::new(tcx.types.bool, DUMMY_SP));
        body[loop_start].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(temp2),
                Rvalue::BinaryOp(
                    BinOp::Ge,
                    Box::new((
                        Operand::Move(Place::from(temp1)),
                        Operand::Constant(Box::new(Constant {
                            span: DUMMY_SP,
                            user_ty: None,
                            literal: Const::from_usize(tcx, self.vector_len.unwrap()).into(),
                        })),
                    )),
                ),
            ))),
        });

        let loop_next = body.basic_blocks_mut().push(BasicBlockData::new(None));
        let mut current = loop_next;
        for stmt in stmts {
            match stmt {
                TempAssign(mut place, mut rvalue, bitset, location)
                | AfterGet(mut place, mut rvalue, bitset, location) => {
                    bitset.iter().for_each(|local| {
                        if let Some(simd_rhs) = self.get_vector(&Place::from(local)) {
                            let mut ptv =
                                PlaceToVector { tcx, temp: local, vector: simd_rhs, inner };
                            ptv.visit_rvalue(&mut rvalue, location);
                        };
                    });
                    if let Some(simd_lhs) = self.get_vector(&place) {
                        let mut ptv =
                            PlaceToVector { tcx, temp: place.local, vector: simd_lhs, inner };
                        ptv.visit_place(
                            &mut place,
                            PlaceContext::MutatingUse(MutatingUseContext::Store),
                            location,
                        )
                    }
                    body[current]
                        .statements
                        .push(Statement { source_info, kind: Assign(Box::new((place, rvalue))) });
                }
                TempFuncTerminator(location, _, _) => {
                    let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    if let Call { func, args, destination, cleanup, from_hir_call, fn_span } =
                        body[location.block].terminator().kind.clone()
                    {
                        args.iter().for_each(|operand| {
                            let local = operand.place().unwrap().as_local().unwrap();
                            if let Some(simd_rhs) = self.get_vector(&Place::from(local)) {
                                body[current].statements.push(Statement {
                                    source_info,
                                    kind: Assign(Box::new((
                                        Place::from(local),
                                        Rvalue::Use(Operand::Copy(Place {
                                            local: simd_rhs,
                                            projection: tcx
                                                .intern_place_elems(&[PlaceElem::Index(inner)]),
                                        })),
                                    ))),
                                })
                            };
                        });
                        let place = destination.unwrap().0;
                        let des = self.get_vector(&place).map_or(place, |lhs| Place {
                            local: lhs,
                            projection: tcx.intern_place_elems(&[PlaceElem::Index(inner)]),
                        });
                        body[current].terminator = Some(Terminator {
                            source_info,
                            kind: Call {
                                func,
                                args,
                                destination: Some((des, next)),
                                cleanup,
                                from_hir_call,
                                fn_span,
                            },
                        });
                        current = next;
                    } else {
                        bug!("wrong terminator stmt: {:?}", stmt)
                    }
                }
                AfterSet(place, mut rvalue, bitset, location) => {
                    bitset.iter().for_each(|local| {
                        if local != place.local {
                            if let Some(simd_rhs) = self.get_vector(&Place::from(local)) {
                                let mut ptv =
                                    PlaceToVector { tcx, temp: local, vector: simd_rhs, inner };
                                ptv.visit_rvalue(&mut rvalue, location);
                            };
                        }
                    });
                    body[current].statements.push(Statement {
                        source_info,
                        kind: Assign(Box::new((place.clone(), rvalue.clone()))),
                    });
                    if let Some(lhs) = self.no_reset_after_vector.get(&place) {
                        let p = Place {
                            local: *lhs,
                            projection: tcx.intern_place_elems(&[PlaceElem::Index(inner)]),
                        };
                        body[current].statements.push(Statement {
                            source_info,
                            kind: Assign(Box::new((p, Rvalue::Use(Operand::Copy(place))))),
                        });
                    }
                }
                ResumeAfter(place) => {
                    for proj in place.projection {
                        if let PlaceElem::Index(local) = proj {
                            if let Some(simd_rhs) = self.get_vector(&Place::from(local)) {
                                body[current].statements.push(Statement {
                                    source_info,
                                    kind: Assign(Box::new((
                                        Place::from(local),
                                        Rvalue::Use(Operand::Copy(Place {
                                            local: simd_rhs,
                                            projection: tcx
                                                .intern_place_elems(&[PlaceElem::Index(inner)]),
                                        })),
                                    ))),
                                })
                            };
                        }
                    }
                    body[current].statements.push(Statement {
                        source_info,
                        kind: Assign(Box::new((
                            place,
                            Rvalue::Use(Operand::Copy(Place {
                                local: self.get_vector(&place).unwrap(),
                                projection: tcx.intern_place_elems(&[PlaceElem::Index(inner)]),
                            })),
                        ))),
                    });
                }
                OtherTerminator(location) => {
                    let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    let term = body[location.block].terminator().clone();
                    match term.kind {
                        Assert {
                            cond,
                            expected,
                            msg: AssertKind::BoundsCheck { len: op1, index: op2 },
                            target: _,
                            cleanup,
                        } => {
                            if let Some(p) = op2.place() {
                                if let Some(rhs) = self.get_vector(&p) {
                                    body[current].statements.push(Statement {
                                        source_info,
                                        kind: Assign(Box::new((
                                            op2.place().unwrap(),
                                            Rvalue::Use(Operand::Copy(Place {
                                                local: rhs,
                                                projection: tcx
                                                    .intern_place_elems(&[PlaceElem::Index(inner)]),
                                            })),
                                        ))),
                                    });
                                }
                            }
                            body[current].terminator = Some(Terminator {
                                source_info,
                                kind: Assert {
                                    cond,
                                    expected,
                                    msg: AssertKind::BoundsCheck { len: op1, index: op2 },
                                    target: next,
                                    cleanup,
                                },
                            });
                            current = next;
                        }
                        _ => {
                            unimplemented!("terminator {:?} are not supported in inner loop", term)
                        }
                    }
                }
                _ => unimplemented!("stmt {:?} are not supported in inner loop", stmt),
            }
        }
        body[current].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(inner),
                Rvalue::BinaryOp(
                    BinOp::Add,
                    Box::new((
                        Operand::Copy(Place::from(inner)),
                        Operand::Constant(Box::new(Constant {
                            span: DUMMY_SP,
                            user_ty: None,
                            literal: Const::from_usize(tcx, 1 as u64).into(),
                        })),
                    )),
                ),
            ))),
        });
        body[current].terminator =
            Some(Terminator { source_info, kind: Goto { target: loop_start } });

        let loop_break = body.basic_blocks_mut().push(BasicBlockData::new(None));
        body[loop_start].terminator = Some(Terminator {
            source_info,
            kind: SwitchInt {
                discr: Operand::Move(Place::from(temp2)),
                switch_ty: tcx.types.bool,
                targets: SwitchTargets::static_if(0, loop_next, loop_break),
            },
        });
        loop_break
    }

    fn resolve_vector_section<'r>(
        &'r mut self,
        tcx: TyCtxt<'tcx>,
        body: &mut Body<'tcx>,
        outer_loop: BasicBlock,
        vect_stmts: Vec<ExtraStmt<'tcx>>,
    ) -> Vec<VectorStmt<'tcx>> {
        let source_info = SourceInfo { span: DUMMY_SP, scope: OUTERMOST_SOURCE_SCOPE };
        let mut resolved_stmts = Vec::new();
        for (index, stmt) in vect_stmts.iter().enumerate() {
            match stmt {
                TempStorage(location) => {
                    let kind =
                        body[location.block].statements[location.statement_index].kind.clone();
                    resolved_stmts.push(StraightStmt(Statement { source_info, kind }));
                }
                AfterSet(place, rvalue, _bitset, _) => match rvalue {
                    Rvalue::BinaryOp(binop, ops) | Rvalue::CheckedBinaryOp(binop, ops) => {
                        let after = place.local;
                        let (op1, op2) = ops.as_ref();
                        let mut after_use = false;
                        for i in index + 1..vect_stmts.len() {
                            match &vect_stmts[i] {
                                AfterSet(place2, rvalue, right_locals, _)
                                | AfterGet(place2, rvalue, right_locals, _) => {
                                    if right_locals.contains(after) {
                                        if let Some(local) = place2.as_local() {
                                            if local == after {
                                                continue;
                                            }
                                        }
                                        if let Rvalue::Ref(_, _, ref_place) = rvalue {
                                            if ref_place.local == after {
                                                continue;
                                            }
                                        }
                                        after_use = true;
                                        break;
                                    }
                                }
                                _ => {}
                            }
                        }
                        if !after_use {
                            resolved_stmts.push(BinOpAfterSet(
                                *place,
                                *binop,
                                op1.clone(),
                                op2.clone(),
                            ));
                        } else {
                            resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                        }
                    }
                    _ => {
                        resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                    }
                },
                TempAssign(place, rvalue, _, location) => match rvalue {
                    Rvalue::BinaryOp(bin_op, ops) | Rvalue::CheckedBinaryOp(bin_op, ops) => {
                        let (op1, op2) = ops.as_ref();
                        if index > 0 && index < vect_stmts.len() - 1 {
                            if let TempAssign(place_pre, Rvalue::Len(..), _, _)
                            | AfterGet(place_pre, Rvalue::Len(..), _, _) = &vect_stmts[index - 1]
                            {
                                if matches!(bin_op, BinOp::Lt)
                                    && Some(place_pre) == op2.place().as_ref()
                                {
                                    if let OtherTerminator(location) = &vect_stmts[index + 1] {
                                        if let TerminatorKind::Assert { cond, .. } =
                                            &body[location.block].terminator().kind
                                        {
                                            if cond.place().as_ref() == Some(place) {
                                                resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                            if matches!(bin_op, BinOp::Lt) {
                                unimplemented!("Lt binop in {:?}", location)
                            }
                        }
                        resolved_stmts.push(BinOpAssign(*place, *bin_op, op1.clone(), op2.clone()));
                    }
                    Rvalue::Cast(CastKind::Misc, op, ty2) => {
                        let ty1 = op.ty(body, tcx);
                        if ty1.is_integral() && ty2.is_integral() {
                            resolved_stmts.push(Cast(*place, op.clone(), ty2));
                        } else {
                            resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                        }
                    }
                    /*Rvalue::Len(..) => {
                        if index < vect_stmts.len() - 2 {
                            if let TempAssign(place_lt, Rvalue::BinaryOp(BinOp::Lt, ..), _, _) =
                                &vect_stmts[index + 1]
                            {
                                if let OtherTerminator(location) = &vect_stmts[index + 2] {
                                    if let TerminatorKind::Assert { cond, .. } =
                                        &body[location.block].terminator().kind
                                    {
                                        if cond.place().as_ref() == Some(place_lt) {
                                            // bounds check
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                        resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                    }*/
                    _ => {
                        resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                    }
                },
                AfterGet(place, rvalue, _, _) => match rvalue {
                    Rvalue::Use(op) => {
                        if let Some(p) = op.place() {
                            let proj = p.projection;
                            if proj.len() == 2 && matches!(proj[0], PlaceElem::Deref) {
                                if let PlaceElem::Index(local) = proj[1] {
                                    if self.range_condi.contains(&local) {
                                        resolved_stmts.push(ReadVector(*place, p, local));
                                        continue;
                                    }
                                }
                            }
                        }
                        resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                    }
                    /*Rvalue::Len(..) => {
                        if index < vect_stmts.len() - 2 {
                            if let TempAssign(place_lt, Rvalue::BinaryOp(BinOp::Lt, ..), _, _) =
                                &vect_stmts[index + 1]
                            {
                                if let OtherTerminator(location) = &vect_stmts[index + 2] {
                                    if let TerminatorKind::Assert { cond, .. } =
                                        &body[location.block].terminator().kind
                                    {
                                        if cond.place().as_ref() == Some(place_lt) {
                                            // bounds check
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                        resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                    }*/
                    _ => {
                        resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                    }
                },
                TempFuncTerminator(location, _, _) => {
                    if let Call {
                        func,
                        args,
                        destination,
                        cleanup: _,
                        from_hir_call: _,
                        fn_span: _,
                    } = body[location.block].terminator().kind.clone()
                    {
                        let fn_ty = func.constant().unwrap().ty();
                        let func_str = if let ty::FnDef(def_id, _) = fn_ty.kind() {
                            tcx.def_path(*def_id).to_string_no_crate_verbose()
                        } else {
                            bug!("wrong func call")
                        };
                        if func_str.as_str() == "::intrinsics::{extern#1}::sqrtf32"
                            || func_str.as_str() == "::f32::{impl#0}::sqrt"
                        {
                            let func = sym::simd_fsqrt;
                            let des = destination.unwrap().0;
                            resolved_stmts.push(VectorTerm(func, args, des));
                        } else {
                            resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                        }
                    } else {
                        bug!("wrong terminator stmt: {:?}", stmt)
                    }
                }
                EndLoopTerminator(_location) => {
                    resolved_stmts.push(StraightTerm(Terminator {
                        source_info,
                        kind: Goto { target: outer_loop },
                    }));
                }
                /*OtherTerminator(location) => {
                    if let TerminatorKind::Assert { msg: AssertKind::BoundsCheck { .. }, .. } =
                        &body[location.block].terminator().kind
                    {
                        // bounds check
                        continue;
                    }
                    resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                }*/
                _ => resolved_stmts.push(InnerLoopStmt(stmt.clone())),
            }
        }
        resolved_stmts
    }

    fn resolve_temp_to_vector<'r>(
        &'r mut self,
        tcx: TyCtxt<'tcx>,
        body: &mut Body<'tcx>,
        condi_stmts: &Vec<ExtraStmt<'tcx>>,
        resolved_stmts: &mut Vec<VectorStmt<'tcx>>,
    ) {
        for stmt in condi_stmts {
            match stmt {
                CondiGet(place, _, _) => {
                    self.insert_vector(&place.as_local().unwrap(), tcx, body, true);
                    self.condi_vector.insert(place.as_local().unwrap());
                }
                _ => {}
            }
        }
        let mut changed = true;
        // insert vector from vertical statements
        for stmt in resolved_stmts.iter() {
            match stmt {
                InnerLoopStmt(..) | StraightStmt(..) | StraightTerm(..) | UseAssign(..) => {}
                BinOpAssign(place, _, op1, op2) => {
                    self.insert_vector(&place.local, tcx, body, false);

                    if let Some(p1) = op1.place() {
                        self.insert_vector(&p1.local, tcx, body, false);
                    }
                    if let Some(p2) = op2.place() {
                        self.insert_vector(&p2.local, tcx, body, false);
                    }
                }
                BinOpAfterSet(place, _, op1, op2) => {
                    if self.get_vector(place).is_none() {
                        let ty = place.ty(body, tcx).ty;
                        let v = body.local_decls.push(LocalDecl::new(
                            tcx.mk_array(ty, self.vector_len.unwrap()),
                            DUMMY_SP,
                        ));
                        self.no_read_after_vector.insert(*place, v);
                        assert!(ty.is_primitive());
                        body.local_decls[v].vector = true;

                        for proj in place.projection {
                            if let PlaceElem::Index(local) = proj {
                                self.insert_vector(&local, tcx, body, false);
                            }
                        }
                    }

                    if let Some(p1) = op1.place() {
                        if self.locals_use[p1.local] == InLoop {
                            self.insert_vector(&p1.local, tcx, body, false);
                        }
                    }
                    if let Some(p2) = op2.place() {
                        if self.locals_use[p2.local] == InLoop {
                            self.insert_vector(&p2.local, tcx, body, false);
                        }
                    }
                }
                Cast(place, op, _) => {
                    self.insert_vector(&place.as_local().unwrap(), tcx, body, false);

                    if let Some(p) = op.place() {
                        self.insert_vector(&p.as_local().unwrap(), tcx, body, false);
                    }
                }
                ReadVector(place, _, local) => {
                    self.insert_vector(&place.as_local().unwrap(), tcx, body, false);
                    self.insert_vector(local, tcx, body, false);
                }
                VectorTerm(func, args, des) => match *func {
                    sym::simd_fsqrt => {
                        self.insert_vector(&des.as_local().unwrap(), tcx, body, false);
                        args.iter().for_each(|arg| {
                            self.insert_vector(&arg.place().unwrap().local, tcx, body, false);
                        });
                    }
                    _ => unimplemented!("unimplemented vector func"),
                },
            }
        }

        // insert vector from use rvalue
        while changed {
            changed = false;
            for index in 0..resolved_stmts.len() {
                match &resolved_stmts[index] {
                    InnerLoopStmt(TempAssign(place, Rvalue::Use(operand), _, _))
                    | InnerLoopStmt(AfterGet(place, Rvalue::Use(operand), _, _)) => {
                        if let (Some(lhs), Some(Some(rhs))) =
                            (place.as_local(), operand.place().map(|place| place.as_local()))
                        {
                            if self.get_vector(&Place::from(lhs)).is_some()
                                && self.get_vector(&Place::from(rhs)).is_some()
                            {
                                resolved_stmts[index] = UseAssign(*place, operand.clone());
                            }
                        }
                    }
                    InnerLoopStmt(AfterSet(place, Rvalue::BinaryOp(_, ops), _, _))
                    | InnerLoopStmt(AfterSet(place, Rvalue::CheckedBinaryOp(_, ops), _, _))=> {
                        let mut reset = false;
                        for j in index + 1..resolved_stmts.len() {
                            match &resolved_stmts[j] {
                                InnerLoopStmt(AfterSet(p, _, _, _)) => {
                                    if p.local == place.local {
                                        reset = true;
                                        break;
                                    }
                                }
                                _ => {}
                            }
                        }
                        if !reset {
                            let ty = place.ty(body, tcx).ty;
                            let v = body.local_decls.push(LocalDecl::new(
                                tcx.mk_array(ty, self.vector_len.unwrap()),
                                DUMMY_SP,
                            ));
                            self.no_reset_after_vector.insert(*place, v);
                            assert!(ty.is_primitive());
                            body.local_decls[v].vector = true;
                            for proj in place.projection {
                                if let PlaceElem::Index(local) = proj {
                                    self.insert_vector(&local, tcx, body, false);
                                }
                            }

                            let (op1, op2) = ops.as_ref();
                            if let Some(p1) = op1.place() {
                                if self.locals_use[p1.local] == InLoop {
                                    if self.insert_vector(&p1.local, tcx, body, false) {
                                        changed = true;
                                    };
                                }
                            }
                            if let Some(p2) = op2.place() {
                                if self.locals_use[p2.local] == InLoop {
                                    if self.insert_vector(&p2.local, tcx, body, false) {
                                        changed = true;
                                    };
                                }
                            }
                        }
                    }
                    InnerLoopStmt(AfterGet(place, Rvalue::BinaryOp(bin_op, ops), _, _))
                    | InnerLoopStmt(AfterGet(place, Rvalue::CheckedBinaryOp(bin_op, ops), _, _))=> {
                        let mut all_vec_after = true;
                        let (op1, op2) = ops.as_ref();
                        if let Some(p1) = op1.place() {
                            if self.locals_use[p1.local] == AfterLoop
                                && self.no_reset_after_vector.get(&p1).is_none()
                            {
                                all_vec_after = false;
                            }
                        }
                        if let Some(p2) = op2.place() {
                            if self.locals_use[p2.local] == AfterLoop
                                && self.no_reset_after_vector.get(&p2).is_none()
                            {
                                all_vec_after = false;
                            }
                        }
                        if all_vec_after {
                            changed = true;
                            self.insert_vector(&place.local, tcx, body, false);
                            if let Some(p1) = op1.place() {
                                if self.locals_use[p1.local] == InLoop {
                                    self.insert_vector(&p1.local, tcx, body, false);
                                }
                            }
                            if let Some(p2) = op2.place() {
                                if self.locals_use[p2.local] == InLoop {
                                    self.insert_vector(&p2.local, tcx, body, false);
                                }
                            }
                            resolved_stmts[index] =
                                BinOpAssign(*place, *bin_op, op1.clone(), op2.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    fn resort_storage<'r>(&'r mut self, resolved_stmts: &mut Vec<VectorStmt<'tcx>>) {
        let mut changed = true;
        'changed: while changed {
            changed = false;
            'outer: for i in 1..resolved_stmts.len() - 1 {
                if let StraightStmt(statment) = &resolved_stmts[i] {
                    let mut up = None;
                    let mut down = None;
                    for j in (0..i).rev() {
                        match &resolved_stmts[j] {
                            InnerLoopStmt(..) => {
                                up = Some(j);
                                break;
                            }
                            StraightStmt(..) => continue,
                            _ => continue 'outer,
                        }
                    }
                    for j in i + 1..resolved_stmts.len() {
                        match &resolved_stmts[j] {
                            InnerLoopStmt(..) => {
                                down = Some(j);
                                break;
                            }
                            StraightStmt(..) => continue,
                            _ => continue 'outer,
                        }
                    }
                    if let (Some(up), Some(down)) = (up, down) {
                        match &statment.kind {
                            StorageLive(..) => {
                                changed = true;
                                for j in (up..i).rev() {
                                    resolved_stmts.swap(j, j + 1);
                                }
                                for j in (0..up).rev() {
                                    if matches!(resolved_stmts[j], InnerLoopStmt(..)) {
                                        resolved_stmts.swap(j, j + 1);
                                    } else {
                                        break;
                                    }
                                }
                                continue 'changed;
                            }
                            StorageDead(..) => {
                                changed = true;
                                for j in i..down {
                                    resolved_stmts.swap(j, j + 1);
                                }
                                for j in down..resolved_stmts.len() - 1 {
                                    if matches!(resolved_stmts[j + 1], InnerLoopStmt(..)) {
                                        resolved_stmts.swap(j, j + 1);
                                    } else {
                                        break;
                                    }
                                }
                                continue 'changed;
                            }
                            _ => bug!("wrong temp storage stmt: {:?}", statment),
                        }
                    }
                }
            }
        }
    }

    fn resolve_vector_len<'r>(
        &'r mut self,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        resolved_stmts: &Vec<VectorStmt<'tcx>>,
    ) {
        let mut vector_type = None;
        for stmt in resolved_stmts {
            match stmt {
                StraightStmt(..) | StraightTerm(..) | InnerLoopStmt(..) | UseAssign(..)
                | Cast(..) | ReadVector(..) => {}
                BinOpAssign(_, _, op1, _) | BinOpAfterSet(_, _, op1, _) => {
                    let op_ty = op1.ty(body, tcx);
                    if let Some(vec_ty) = vector_type {
                        if op_ty != vec_ty {
                            if op_ty == tcx.types.u8 || vec_ty == tcx.types.u8 {
                                vector_type = Some(tcx.types.u8)
                            } else if op_ty == tcx.types.u32 || vec_ty == tcx.types.u32 {
                                vector_type = Some(tcx.types.u32)
                            } else {
                                unimplemented!(
                                    "different vector element: {:?} and {:?}",
                                    vec_ty,
                                    op_ty
                                )
                            }
                        }
                    } else {
                        vector_type = Some(op_ty)
                    }
                }
                VectorTerm(_, args, _) => {
                    let op_ty = args[0].ty(body, tcx);
                    if let Some(vec_ty) = vector_type {
                        if op_ty == tcx.types.u32 || vec_ty == tcx.types.u32 {
                            vector_type = Some(tcx.types.u32)
                        } else if op_ty == tcx.types.u8 || vec_ty == tcx.types.u8 {
                            vector_type = Some(tcx.types.u8)
                        } else {
                            unimplemented!("different vector element: {:?} and {:?}", vec_ty, op_ty)
                        }
                    } else {
                        vector_type = Some(op_ty)
                    }
                }
            }
        }
        let ty = vector_type.unwrap();
        let len = if ty == tcx.types.f32 {
            if tcx.sess.target.arch == "x86_64" { 32 } else { 8 }
        } else if ty == tcx.types.u8 {
            32
        } else if ty == tcx.types.u32 {
            16 
        } else {
            unimplemented!("unimplemented vector element type: {:?}", ty)
        };
        self.vector_len = Some(len);
    }

    fn generate_vector_section<'r>(
        &'r mut self,
        tcx: TyCtxt<'tcx>,
        body: &mut Body<'tcx>,
        mut current: BasicBlock,
        inner: Local,
        resolved_stmts: Vec<VectorStmt<'tcx>>,
    ) -> (Vec<RemainStmt<'tcx>>, BasicBlock) {
        let source_info = SourceInfo { span: DUMMY_SP, scope: OUTERMOST_SOURCE_SCOPE };
        let mut remain_stmt = Vec::new();

        let mut inner_stmts = Vec::new();
        for stmt in resolved_stmts.into_iter() {
            if let InnerLoopStmt(stmt) = stmt {
                inner_stmts.push(stmt);
            } else {
                if !inner_stmts.is_empty() {
                    current = self.new_inner_loop(tcx, body, current, inner_stmts.clone(), inner);
                    inner_stmts.clear();
                }
                match stmt {
                    StraightStmt(stmt) => {
                        if let StorageDead(local) = &stmt.kind {
                            if self.locals_use[*local] == AfterLoop {
                                remain_stmt.push(RemainStmt::DeadAfter(*local));
                                continue;
                            }
                        }
                        body[current].statements.push(stmt);
                    }
                    BinOpAfterSet(place, bin_op, op1, op2) => {
                        let p1 = op1.place().unwrap();
                        let p2 = op2.place().unwrap();
                        let l1 = p1.local;
                        let l2 = p2.local;
                        match (self.locals_use.get(l1), self.locals_use.get(l2)) {
                            (Some(AfterLoop), Some(InLoop)) => {
                                let lhs = self.get_vector(&place).unwrap();
                                let func = match bin_op {
                                    BinOp::Add => sym::simd_add,
                                    BinOp::Shr => sym::simd_shr,
                                    BinOp::BitAnd => sym::simd_and,
                                    _ => {
                                        unimplemented!("unimplemented binop: {:?}", bin_op)
                                    }
                                };

                                let simd_rhs1 = self.get_vector(&p1).unwrap();
                                let simd_rhs2 = self.get_vector(&p2).unwrap();

                                let args = vec![
                                    if lhs == simd_rhs1 {
                                        let mut inited = false;
                                        for rest in &remain_stmt {
                                            match rest {
                                                RemainStmt::InitAfterVector(l, b)
                                                    if l == &place =>
                                                {
                                                    inited = true;
                                                    if b != &bin_op {
                                                        unimplemented!("different init for {:?}", l)
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                        if !inited {
                                            remain_stmt
                                                .push(RemainStmt::InitAfterVector(place, bin_op));
                                        }
                                        Operand::Copy(Place::from(simd_rhs1))
                                    } else {
                                        Operand::Move(Place::from(simd_rhs1))
                                    },
                                    if lhs == simd_rhs2 {
                                        let mut inited = false;
                                        for rest in &remain_stmt {
                                            match rest {
                                                RemainStmt::InitAfterVector(l, b)
                                                    if l == &place =>
                                                {
                                                    inited = true;
                                                    if b != &bin_op {
                                                        unimplemented!("different init for {:?}", l)
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                        if !inited {
                                            remain_stmt
                                                .push(RemainStmt::InitAfterVector(place, bin_op));
                                        }
                                        remain_stmt
                                            .push(RemainStmt::InitAfterVector(place, bin_op));
                                        Operand::Copy(Place::from(simd_rhs2))
                                    } else {
                                        Operand::Move(Place::from(simd_rhs2))
                                    },
                                ];

                                let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                                body[current].terminator = Some(Terminator {
                                    source_info,
                                    kind: VectorFunc {
                                        func,
                                        args,
                                        destination: Some((Place::from(lhs), next)),
                                    },
                                });
                                current = next;

                                let mut seted = false;
                                for rest in &remain_stmt {
                                    match rest {
                                        RemainStmt::SetAfterReduce(p, b)
                                            if p == &place && b == &bin_op =>
                                        {
                                            seted = true;
                                        }
                                        _ => {}
                                    }
                                }
                                if !seted {
                                    remain_stmt.push(RemainStmt::SetAfterReduce(place, bin_op))
                                }
                            }
                            (Some(InLoop), Some(InLoop)) => {
                                let func = match bin_op {
                                    BinOp::Add => sym::simd_add,
                                    BinOp::Shr => sym::simd_shr,
                                    BinOp::Mul => sym::simd_mul,
                                    BinOp::BitAnd => sym::simd_and,
                                    _ => unimplemented!("unimplemented binop: {:?}", bin_op),
                                };
                                let (simd_rhs1, simd_rhs2) = (
                                    self.get_vector(&op1.place().unwrap()).unwrap(),
                                    self.get_vector(&op2.place().unwrap()).unwrap(),
                                );
                                let args = vec![
                                    Operand::Move(Place::from(simd_rhs1)),
                                    Operand::Move(Place::from(simd_rhs2)),
                                ];
                                let simd_des = self.get_vector(&place).unwrap();

                                let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                                body[current].terminator = Some(Terminator {
                                    source_info,
                                    kind: VectorFunc {
                                        func,
                                        args,
                                        destination: Some((Place::from(simd_des), next)),
                                    },
                                });
                                current = next;
                                let proj = place.projection;
                                if proj.len() == 2 && matches!(proj[0], PlaceElem::Deref) {
                                    if let PlaceElem::Index(local) = proj[1] {
                                        if self.range_condi.contains(&local) {
                                            body[current].statements.push(Statement {
                                                source_info,
                                                kind: Assign(Box::new((
                                                    Place::from(inner),
                                                    Rvalue::Use(Operand::Constant(Box::new(
                                                        Constant {
                                                            span: DUMMY_SP,
                                                            user_ty: None,
                                                            literal: Const::from_usize(tcx, 0)
                                                                .into(),
                                                        },
                                                    ))),
                                                ))),
                                            });
                                            body[current].statements.push(Statement {
                                                source_info,
                                                kind: Assign(Box::new((
                                                    Place::from(local),
                                                    Rvalue::Use(Operand::Copy(Place {
                                                        local: self
                                                            .get_vector(&Place::from(local))
                                                            .unwrap(),
                                                        projection: tcx.intern_place_elems(&[
                                                            PlaceElem::Index(inner),
                                                        ]),
                                                    })),
                                                ))),
                                            });

                                            let elem_ty = place.ty(body, tcx).ty;
                                            let head_ptr = body.local_decls.push(LocalDecl::new(
                                                tcx.mk_ptr(TypeAndMut {
                                                    ty: elem_ty,
                                                    mutbl: Mutability::Not,
                                                }),
                                                DUMMY_SP,
                                            ));
                                            body[current].statements.push(Statement {
                                                source_info,
                                                kind: Assign(Box::new((
                                                    Place::from(head_ptr),
                                                    Rvalue::AddressOf(
                                                        Mutability::Not,
                                                        Place {
                                                            local: simd_des,
                                                            projection: tcx.intern_place_elems(&[
                                                                PlaceElem::Index(inner),
                                                            ]),
                                                        },
                                                    ),
                                                ))),
                                            });
                                            let u8_ptr = tcx.mk_ptr(TypeAndMut {
                                                ty: tcx.types.u8,
                                                mutbl: Mutability::Not,
                                            });
                                            let head_ptr_u8 = body
                                                .local_decls
                                                .push(LocalDecl::new(u8_ptr, DUMMY_SP));
                                            body[current].statements.push(Statement {
                                                source_info,
                                                kind: Assign(Box::new((
                                                    Place::from(head_ptr_u8),
                                                    Rvalue::Cast(
                                                        CastKind::Misc,
                                                        Operand::Move(Place::from(head_ptr)),
                                                        u8_ptr,
                                                    ),
                                                ))),
                                            });

                                            let des_ptr = body.local_decls.push(LocalDecl::new(
                                                tcx.mk_ptr(TypeAndMut {
                                                    ty: elem_ty,
                                                    mutbl: Mutability::Mut,
                                                }),
                                                DUMMY_SP,
                                            ));
                                            body[current].statements.push(Statement {
                                                source_info,
                                                kind: Assign(Box::new((
                                                    Place::from(des_ptr),
                                                    Rvalue::AddressOf(Mutability::Mut, place),
                                                ))),
                                            });
                                            let u8_ptr_mut = tcx.mk_ptr(TypeAndMut {
                                                ty: tcx.types.u8,
                                                mutbl: Mutability::Mut,
                                            });
                                            let des_ptr_u8 = body
                                                .local_decls
                                                .push(LocalDecl::new(u8_ptr_mut, DUMMY_SP));
                                            body[current].statements.push(Statement {
                                                source_info,
                                                kind: Assign(Box::new((
                                                    Place::from(des_ptr_u8),
                                                    Rvalue::Cast(
                                                        CastKind::Misc,
                                                        Operand::Move(Place::from(des_ptr)),
                                                        u8_ptr_mut,
                                                    ),
                                                ))),
                                            });
                                            let elem_len = if elem_ty == tcx.types.u8 {
                                                1
                                            } else if elem_ty == tcx.types.u32 {
                                                4
                                            } else if elem_ty == tcx.types.f32 {
                                                4
                                            } else {
                                                unimplemented!("unknown elem len: {:?}", elem_ty)
                                            };
                                            let count = Operand::Constant(Box::new(Constant {
                                                span: DUMMY_SP,
                                                user_ty: None,
                                                literal: ConstantKind::Val(
                                                    ConstValue::from_u64(
                                                        self.vector_len.unwrap() * elem_len,
                                                    ),
                                                    tcx.types.usize,
                                                ),
                                            }));
                                            body[current].statements.push(Statement {
                                                source_info,
                                                kind: CopyNonOverlapping(Box::new(
                                                    rustc_middle::mir::CopyNonOverlapping {
                                                        src: Operand::Move(Place::from(
                                                            head_ptr_u8,
                                                        )),
                                                        dst: Operand::Move(Place::from(des_ptr_u8)),
                                                        count,
                                                    },
                                                )),
                                            });
                                            continue;
                                        }
                                    }
                                }
                                inner_stmts.push(ResumeAfter(place));
                            }
                            _ => unimplemented!("set after ops local use: {:?} with {:?}", l1, l2),
                        }
                    }
                    UseAssign(place, operand) => {
                        let (lhs, rhs) = (
                            place.as_local().unwrap(),
                            operand.place().unwrap().as_local().unwrap(),
                        );
                        let (simd_lhs, simd_rhs) = (
                            self.get_vector(&Place::from(lhs)).unwrap(),
                            self.get_vector(&Place::from(rhs)).unwrap(),
                        );
                        body[current].statements.push(Statement {
                            source_info,
                            kind: Assign(Box::new((
                                Place::from(simd_lhs),
                                Rvalue::Use(Operand::Copy(Place::from(simd_rhs))),
                            ))),
                        });
                    }
                    BinOpAssign(place, bin_op, op1, op2) => {
                        let func = match bin_op {
                            BinOp::Add => sym::simd_add,
                            BinOp::Shr => sym::simd_shr,
                            BinOp::Mul => sym::simd_mul,
                            BinOp::BitAnd => sym::simd_and,
                            _ => unimplemented!("unimplemented binop: {:?}", bin_op),
                        };

                        let (simd_rhs1, simd_rhs2) = match (&op1.place(), &op2.place()) {
                            (Some(p1), Some(p2)) => {
                                (self.get_vector(&p1).unwrap(), self.get_vector(&p2).unwrap())
                            }
                            (Some(p1), None) => {
                                let simd_rhs1 = self.get_vector(&p1).unwrap();
                                let ty = op1.ty(body, tcx);
                                let ty2 = op2.ty(body, tcx);

                                let val_pre =
                                    op2.constant().unwrap().literal.try_to_value().unwrap();

                                let val = if ty == ty2 {
                                    val_pre
                                } else {
                                    if ty == tcx.types.u8 && ty2 == tcx.types.i32 {
                                        let con =
                                            val_pre.try_to_scalar().unwrap().to_i32().unwrap();
                                        ConstValue::Scalar(Scalar::from_u8(con as u8))
                                    } else {
                                        unimplemented!(
                                            "unimplemented vector element type: {:?} and {:?}",
                                            ty,
                                            ty
                                        )
                                    }
                                };

                                let temp = body.local_decls.push(LocalDecl::new(
                                    tcx.mk_array(ty, self.vector_len.unwrap()),
                                    DUMMY_SP,
                                ));
                                assert!(ty.is_primitive());
                                body.local_decls[temp].vector = true;
                                body[current].statements.push(Statement {
                                    source_info,
                                    kind: Assign(Box::new((
                                        Place::from(temp),
                                        Rvalue::Repeat(
                                            Operand::Constant(Box::new(Constant {
                                                span: DUMMY_SP,
                                                user_ty: None,
                                                literal: ConstantKind::Val(val, ty),
                                            })),
                                            Const::from_usize(tcx, self.vector_len.unwrap()),
                                        ),
                                    ))),
                                });
                                (simd_rhs1, temp)
                            }
                            (None, Some(p2)) => {
                                let simd_rhs2 = self.get_vector(&p2).unwrap();
                                let ty = op2.ty(body, tcx);
                                let ty1 = op1.ty(body, tcx);

                                let val_pre =
                                    op1.constant().unwrap().literal.try_to_value().unwrap();

                                let val = if ty == ty1 {
                                    val_pre
                                } else {
                                    unimplemented!(
                                        "unimplemented vector element type: {:?} and {:?}",
                                        ty1,
                                        ty
                                    )
                                };

                                let temp = body.local_decls.push(LocalDecl::new(
                                    tcx.mk_array(ty, self.vector_len.unwrap()),
                                    DUMMY_SP,
                                ));
                                assert!(ty.is_primitive());
                                body.local_decls[temp].vector = true;
                                body[current].statements.push(Statement {
                                    source_info,
                                    kind: Assign(Box::new((
                                        Place::from(temp),
                                        Rvalue::Repeat(
                                            Operand::Constant(Box::new(Constant {
                                                span: DUMMY_SP,
                                                user_ty: None,
                                                literal: ConstantKind::Val(val, ty),
                                            })),
                                            Const::from_usize(tcx, self.vector_len.unwrap()),
                                        ),
                                    ))),
                                });
                                (temp, simd_rhs2)
                            }
                            _ => bug!("wrong binop assign operands: {:?} and {:?}", &op1, &op2),
                        };

                        let args = vec![
                            Operand::Move(Place::from(simd_rhs1)),
                            Operand::Move(Place::from(simd_rhs2)),
                        ];
                        //let des = place.as_local().unwrap();
                        let simd_des = self.get_vector(&place).unwrap();

                        let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                        body[current].terminator = Some(Terminator {
                            source_info,
                            kind: VectorFunc {
                                func,
                                args,
                                destination: Some((Place::from(simd_des), next)),
                            },
                        });
                        current = next;
                    }
                    Cast(place, op, _ty2) => {
                        let func = sym::simd_cast;
                        let simd_rhs = self.get_vector(&op.place().unwrap()).unwrap();
                        let args = vec![Operand::Move(Place::from(simd_rhs))];

                        let simd_lhs = self.get_vector(&place).unwrap();

                        let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                        body[current].terminator = Some(Terminator {
                            source_info,
                            kind: VectorFunc {
                                func,
                                args,
                                destination: Some((Place::from(simd_lhs), next)),
                            },
                        });
                        current = next;
                    }
                    ReadVector(place, p, local) => {
                        body[current].statements.push(Statement {
                            source_info,
                            kind: Assign(Box::new((
                                Place::from(inner),
                                Rvalue::Use(Operand::Constant(Box::new(Constant {
                                    span: DUMMY_SP,
                                    user_ty: None,
                                    literal: Const::from_usize(tcx, 0).into(),
                                }))),
                            ))),
                        });
                        body[current].statements.push(Statement {
                            source_info,
                            kind: Assign(Box::new((
                                Place::from(local),
                                Rvalue::Use(Operand::Move(Place {
                                    local: self.get_vector(&Place::from(local)).unwrap(),
                                    projection: tcx.intern_place_elems(&[PlaceElem::Index(inner)]),
                                })),
                            ))),
                        });

                        let elem_ty = place.ty(body, tcx).ty;
                        let head_ptr = body.local_decls.push(LocalDecl::new(
                            tcx.mk_ptr(TypeAndMut { ty: elem_ty, mutbl: Mutability::Not }),
                            DUMMY_SP,
                        ));
                        body[current].statements.push(Statement {
                            source_info,
                            kind: Assign(Box::new((
                                Place::from(head_ptr),
                                Rvalue::AddressOf(Mutability::Not, p),
                            ))),
                        });
                        let u8_ptr =
                            tcx.mk_ptr(TypeAndMut { ty: tcx.types.u8, mutbl: Mutability::Not });
                        let head_ptr_u8 = body.local_decls.push(LocalDecl::new(u8_ptr, DUMMY_SP));
                        body[current].statements.push(Statement {
                            source_info,
                            kind: Assign(Box::new((
                                Place::from(head_ptr_u8),
                                Rvalue::Cast(
                                    CastKind::Misc,
                                    Operand::Move(Place::from(head_ptr)),
                                    u8_ptr,
                                ),
                            ))),
                        });

                        let des = self.get_vector(&place).unwrap();
                        let des_ptr = body.local_decls.push(LocalDecl::new(
                            tcx.mk_ptr(TypeAndMut {
                                ty: body.local_decls[des].ty,
                                mutbl: Mutability::Mut,
                            }),
                            DUMMY_SP,
                        ));
                        body[current].statements.push(Statement {
                            source_info,
                            kind: Assign(Box::new((
                                Place::from(des_ptr),
                                Rvalue::AddressOf(Mutability::Mut, Place::from(des)),
                            ))),
                        });
                        let u8_ptr_mut =
                            tcx.mk_ptr(TypeAndMut { ty: tcx.types.u8, mutbl: Mutability::Mut });
                        let des_ptr_u8 =
                            body.local_decls.push(LocalDecl::new(u8_ptr_mut, DUMMY_SP));
                        body[current].statements.push(Statement {
                            source_info,
                            kind: Assign(Box::new((
                                Place::from(des_ptr_u8),
                                Rvalue::Cast(
                                    CastKind::Misc,
                                    Operand::Move(Place::from(des_ptr)),
                                    u8_ptr_mut,
                                ),
                            ))),
                        });

                        let elem_len = if elem_ty == tcx.types.u8 {
                            1
                        } else if elem_ty == tcx.types.u32 {
                            4
                        } else if elem_ty == tcx.types.f32 {
                            4
                        } else {
                            unimplemented!("unknown elem len: {:?}", elem_ty)
                        };
                        let count = Operand::Constant(Box::new(Constant {
                            span: DUMMY_SP,
                            user_ty: None,
                            literal: ConstantKind::Val(
                                ConstValue::from_u64(self.vector_len.unwrap() * elem_len),
                                tcx.types.usize,
                            ),
                        }));
                        body[current].statements.push(Statement {
                            source_info,
                            kind: CopyNonOverlapping(Box::new(
                                rustc_middle::mir::CopyNonOverlapping {
                                    src: Operand::Move(Place::from(head_ptr_u8)),
                                    dst: Operand::Move(Place::from(des_ptr_u8)),
                                    count,
                                },
                            )),
                        })
                    }
                    VectorTerm(func, args, des) => {
                        let local = des.as_local().unwrap();
                        let simd_des = self.get_vector(&Place::from(local)).unwrap_or(local);
                        let args: Vec<_> = args
                            .iter()
                            .map(|arg| {
                                Operand::Move(Place::from(
                                    self.get_vector(&arg.place().unwrap()).unwrap(),
                                ))
                            })
                            .collect();
                        let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                        body[current].terminator = Some(Terminator {
                            source_info,
                            kind: VectorFunc {
                                func,
                                args,
                                destination: Some((Place::from(simd_des), next)),
                            },
                        });
                        current = next;
                    }
                    StraightTerm(term) => {
                        body[current].terminator = Some(term);
                    }
                    InnerLoopStmt(..) => {
                        unreachable!()
                    }
                }
            }
        }
        if !inner_stmts.is_empty() {
            current = self.new_inner_loop(tcx, body, current, inner_stmts.clone(), inner);
            inner_stmts.clear();
        }
        (remain_stmt, current)
    }

    fn generate_remain_section<'r>(
        &'r mut self,
        tcx: TyCtxt<'tcx>,
        body: &mut Body<'tcx>,
        vect_stmts: &Vec<ExtraStmt<'tcx>>,
        inner: Local,
        mut remain_init: BasicBlock,
        pre_remain_stmts: Vec<RemainStmt<'tcx>>,
    ) {
        let source_info = SourceInfo { span: DUMMY_SP, scope: OUTERMOST_SOURCE_SCOPE };
        let pre_loop = *self.loops[0].0.last().unwrap();
        for stmt in pre_remain_stmts {
            match stmt {
                RemainStmt::InitAfterVector(place, bin_op) => {
                    let vector = self.get_vector(&place).unwrap();
                    let ty = place.ty(body, tcx).ty;

                    let val = if ty == tcx.types.f32 {
                        match bin_op {
                            BinOp::Add => ConstValue::Scalar(Scalar::from_i32(0)),
                            _ => unimplemented!(
                                "unsupported after set op: {:?} for {:?}",
                                bin_op,
                                ty
                            ),
                        }
                    } else if ty == tcx.types.u8 {
                        match bin_op {
                            BinOp::Add => ConstValue::Scalar(Scalar::from_u8(0)),
                            BinOp::Mul => ConstValue::Scalar(Scalar::from_u8(1)),
                            _ => unimplemented!(
                                "unsupported after set op: {:?} for {:?}",
                                bin_op,
                                ty
                            ),
                        }
                    } else if ty == tcx.types.u32 {
                        match bin_op {
                            BinOp::Add => ConstValue::Scalar(Scalar::from_u32(0)),
                            BinOp::Mul => ConstValue::Scalar(Scalar::from_u32(1)),
                            _ => unimplemented!(
                                "unsupported after set op: {:?} for {:?}",
                                bin_op,
                                ty
                            ),
                        }
                    } else {
                        unimplemented!("unimplemented vector element type: {:?}", ty,)
                    };

                    body[pre_loop].statements.push(Statement {
                        source_info,
                        kind: Assign(Box::new((
                            Place::from(vector),
                            Rvalue::Repeat(
                                Operand::Constant(Box::new(Constant {
                                    span: DUMMY_SP,
                                    user_ty: None,
                                    literal: ConstantKind::Val(val, ty),
                                })),
                                Const::from_usize(tcx, self.vector_len.unwrap()),
                            ),
                        ))),
                    });
                }
                RemainStmt::SetAfterReduce(place, bin_op) => {
                    let rhs = self.get_vector(&place).unwrap();
                    let func = match bin_op {
                        BinOp::Add => sym::simd_reduce_add_unordered,
                        _ => unimplemented!("unimplemented after set bin op: {:?}", bin_op),
                    };
                    let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    let args = vec![Operand::Move(Place::from(rhs))];
                    body[remain_init].terminator = Some(Terminator {
                        source_info,
                        kind: VectorFunc { func, args, destination: Some((place, next)) },
                    });
                    remain_init = next;
                }
                RemainStmt::DeadAfter(local) => {
                    body[remain_init]
                        .statements
                        .push(Statement { source_info, kind: StorageDead(local) });
                }
            }
        }

        let break_point = *self.break_points.iter().next().unwrap();
        let inside = body.local_decls.push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
        body[remain_init].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(inside),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    span: DUMMY_SP,
                    user_ty: None,
                    literal: Const::from_usize(tcx, 0).into(),
                }))),
            ))),
        });
        let remain_start = body.basic_blocks_mut().push(BasicBlockData::new(None));
        body[remain_init].terminator =
            Some(Terminator { source_info, kind: Goto { target: remain_start } });
        let temp1 = body.local_decls.push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
        body[remain_start].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(temp1),
                Rvalue::Use(Operand::Copy(Place::from(inside))),
            ))),
        });
        let temp2 = body.local_decls.push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
        body[remain_start].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(temp2),
                Rvalue::Use(Operand::Copy(Place::from(inner))),
            ))),
        });
        let temp3 = body.local_decls.push(LocalDecl::new(tcx.types.bool, DUMMY_SP));
        body[remain_start].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(temp3),
                Rvalue::BinaryOp(
                    BinOp::Ge,
                    Box::new((
                        Operand::Move(Place::from(temp1)),
                        Operand::Move(Place::from(temp2)),
                    )),
                ),
            ))),
        });
        let remain_next = body.basic_blocks_mut().push(BasicBlockData::new(None));
        body[remain_start].terminator = Some(Terminator {
            source_info,
            kind: SwitchInt {
                discr: Operand::Move(Place::from(temp3)),
                switch_ty: tcx.types.bool,
                targets: SwitchTargets::static_if(0, remain_next, break_point),
            },
        });
        let mut block = remain_next;

        for stmt in vect_stmts {
            match stmt {
                TempStorage(location) => {
                    let kind =
                        body[location.block].statements[location.statement_index].kind.clone();
                    body[block].statements.push(Statement { source_info, kind });
                }
                AfterSet(place, rvalue, _, _) | AfterGet(place, rvalue, _, _) => {
                    body[block].statements.push(Statement {
                        source_info,
                        kind: Assign(Box::new((*place, rvalue.clone()))),
                    });
                }
                TempAssign(place, rvalue, bitset, location) => {
                    let mut place = place.clone();
                    let mut rvalue = rvalue.clone();
                    bitset.iter().for_each(|local| {
                        if self.condi_vector.contains(&local) {
                            let v = self.get_vector(&Place::from(local)).unwrap();
                            let mut ptv =
                                PlaceToVector { tcx, temp: local, vector: v, inner: inside };
                            ptv.visit_rvalue(&mut rvalue, *location);
                        }
                    });
                    if self.condi_vector.contains(&place.local) {
                        let v = self.get_vector(&place).unwrap();
                        let mut ptv =
                            PlaceToVector { tcx, temp: place.local, vector: v, inner: inside };
                        ptv.visit_place(
                            &mut place,
                            PlaceContext::MutatingUse(MutatingUseContext::Store),
                            *location,
                        );
                    }
                    body[block]
                        .statements
                        .push(Statement { source_info, kind: Assign(Box::new((place, rvalue))) });
                }
                TempFuncTerminator(location, _, _) => {
                    let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    if let Call { func, args, destination, cleanup, from_hir_call, fn_span } =
                        body[location.block].terminator().kind.clone()
                    {
                        body[block].terminator = Some(Terminator {
                            source_info,
                            kind: Call {
                                func,
                                args,
                                destination: destination.map(|(place, _)| (place, next)),
                                cleanup,
                                from_hir_call,
                                fn_span,
                            },
                        });
                        block = next;
                    } else {
                        bug!("wrong terminator stmt: {:?}", stmt)
                    }
                }
                EndLoopTerminator(_location) => {
                    body[block].statements.push(Statement {
                        source_info,
                        kind: Assign(Box::new((
                            Place::from(inside),
                            Rvalue::BinaryOp(
                                BinOp::Add,
                                Box::new((
                                    Operand::Copy(Place::from(inside)),
                                    Operand::Constant(Box::new(Constant {
                                        span: DUMMY_SP,
                                        user_ty: None,
                                        literal: Const::from_usize(tcx, 1 as u64).into(),
                                    })),
                                )),
                            ),
                        ))),
                    });
                    body[block].terminator =
                        Some(Terminator { source_info, kind: Goto { target: remain_start } });
                }
                OtherTerminator(location) => {
                    let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    let kind = body[location.block].terminator().kind.clone();
                    match kind {
                        Assert { cond, expected, msg, target: _, cleanup } => {
                            body[block].terminator = Some(Terminator {
                                source_info,
                                kind: Assert { cond, expected, msg, target: next, cleanup },
                            });
                            block = next;
                        }
                        _ => unimplemented!(
                            "terminator {:?} are not supported in remain section",
                            kind
                        ),
                    }
                }
                _ => unimplemented!("resolve vertical stmt failed: {:?}", stmt),
            }
        }
    }

    fn generate_blocks<'r>(&'r mut self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let (condi_stmts, vect_stmts) = self.resolve_segments();
        let inner = body.local_decls.push(LocalDecl::new(tcx.types.usize, DUMMY_SP));

        let outer_loop = body.basic_blocks_mut().push(BasicBlockData::new(None));

        let mut resolved_stmts =
            self.resolve_vector_section(tcx, body, outer_loop, vect_stmts.clone());
        self.resolve_vector_len(body, tcx, &resolved_stmts);
        self.resolve_temp_to_vector(tcx, body, &condi_stmts, &mut resolved_stmts);

        self.resolved_stmts_pre = resolved_stmts.clone();
        self.resort_storage(&mut resolved_stmts);

        self.resolved_stmts = resolved_stmts.clone();

        let mut to_inner_break = Vec::<BasicBlock>::new();
        let mut to_remain_init = Vec::<BasicBlock>::new();

        // FIXME: Add Storage statement for newly generated locals

        // FIXME: Keep source_info as much as possible

        self.generate_condi_section(
            tcx,
            body,
            outer_loop,
            inner,
            &condi_stmts,
            &mut to_inner_break,
            &mut to_remain_init,
        );

        // vector section
        let inner_break = body.basic_blocks_mut().push(BasicBlockData::new(None));
        for bb in &to_inner_break {
            match &mut body[*bb].terminator_mut().kind {
                SwitchInt { targets, .. } => {
                    assert_eq!(targets.otherwise(), START_BLOCK);
                    *targets.all_targets_mut().last_mut().unwrap() = inner_break;
                }
                _ => unimplemented!("wrong to inner break block stmt: {:?}", bb),
            }
        }

        let (pre_remain_stmt, _) =
            self.generate_vector_section(tcx, body, inner_break, inner, resolved_stmts);

        // remain section
        let remain_init = body.basic_blocks_mut().push(BasicBlockData::new(None));
        for bb in &to_remain_init {
            match &mut body[*bb].terminator_mut().kind {
                SwitchInt { targets, .. } => {
                    for bb in targets.all_targets_mut() {
                        if *bb == START_BLOCK {
                            *bb = remain_init;
                        }
                    }
                }
                _ => unimplemented!("wrong to inner break block stmt: {:?}", bb),
            }
        }
        self.generate_remain_section(tcx, body, &vect_stmts, inner, remain_init, pre_remain_stmt);
    }
}
