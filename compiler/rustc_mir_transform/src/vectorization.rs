//! This pass implement vectorization of mir

use crate::simplify;
use itertools::Itertools;
use rustc_data_structures::fx::FxHashSet;
use rustc_data_structures::stable_map::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_index::vec::{Idx, IndexVec};
use rustc_middle::mir::visit::{MutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::BinOp;
use rustc_middle::mir::StatementKind::*;
use rustc_middle::mir::TerminatorKind::*;
use rustc_middle::mir::*;
use rustc_middle::ty::{Const, TyCtxt};
use rustc_span::symbol::sym;
use rustc_span::DUMMY_SP;
use std::io::{self, Write};
use ExtraStmt::*;
use LocalUse::*;
use Segment::*;

pub struct Vectorize;

#[derive(Default, Debug)]
pub struct VectorResolver {
    vector_len: usize,
    loops: Vec<(Vec<BasicBlock> /* pre_loop */, Vec<BasicBlock> /* loop */)>,
    break_points: FxHashSet<BasicBlock>,
    break_blocks: Vec<BasicBlock>,

    conditions: FxHashSet<Local>,
    locals_use: IndexVec<Local, LocalUse>,

    loop_stmts: Vec<ExtraStmt>,

    segments: Vec<Segment>,
    temp_to_simd: FxHashMap<Local, Local>,
}

#[derive(Debug, Copy, Clone, PartialOrd, Ord, Eq, PartialEq)]
enum LocalUse {
    InLoop,
    PreLoop,
    AfterLoop,
    Condition,
}

#[derive(Debug, Clone)]
enum ExtraStmt {
    CondiStorage(Location, BitSet<Local>),
    CondiGet(Location, BitSet<Local>),
    CondiSet(Location, BitSet<Local>),

    PreGet(Location),
    AfterSet(Location),

    TempStorage(Location),
    TempAssign(Location, BitSet<Local>),

    BreakTerminator(Location, BitSet<Local>),
    SetCondiTerminator(Location, BitSet<Local>),
    GetCondiTerminator(Location, BitSet<Local>),

    GotoTerminator(Location),
    EndLoopTerminator(Location),
    TempFuncTerminator(Location),
}

#[derive(Debug)]
enum Segment {
    Condi(Vec<ExtraStmt>),
    Vertical(Vec<ExtraStmt>),
}

impl ExtraStmt {
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
            resolver.vector_len = if tcx.sess.target.arch == "x86_64" { 16 } else { 4 };
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

            resolver.resolve_locals(body);
            writeln!(file, "local_use:{:?}", resolver.locals_use)?;

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

            writeln!(file, "Segments:")?;
            resolver.resolve_segments();
            for seg in &resolver.segments {
                match seg {
                    Condi(v) => {
                        writeln!(file, "condi loop:")?;
                        for ex_stmt in v {
                            writeln!(file, "{:?}", ex_stmt)?;
                        }
                        writeln!(file)?;
                    }
                    Vertical(v) => {
                        writeln!(file, "vectical:")?;
                        for ex_stmt in v {
                            writeln!(file, "{:?}", ex_stmt)?;
                        }
                        writeln!(file)?;
                    }
                }
            }

            resolver.generate_blocks(tcx, body);
        };
        simplify::remove_dead_blocks(tcx, body);
    }
}

impl VectorResolver {
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

    fn resolve_conditions(&mut self, body: &Body<'_>) {
        let pre_lp = self.loops[0].0.clone();
        let lp = self.loops[0].1.clone();
        for bb in &lp {
            match &body[*bb].terminator().kind {
                SwitchInt { discr, switch_ty: _, targets } => {
                    let mut is_condi = false;
                    targets.all_targets().into_iter().for_each(|bb| {
                        if lp.iter().all(|target| target != bb) {
                            self.break_points.insert(*bb);
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
        pub struct ConditionResolver<'r> {
            r: &'r mut VectorResolver,
            changed: bool,
        }
        impl Visitor<'_> for ConditionResolver<'_> {
            fn visit_local(&mut self, local: &Local, _context: PlaceContext, _location: Location) {
                self.changed = self.r.conditions.insert(*local);
            }

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
        }
        let mut con_resolver = ConditionResolver { changed: !self.conditions.is_empty(), r: self };
        while con_resolver.changed {
            con_resolver.changed = false;
            for bb in pre_lp.iter().chain(lp.iter()) {
                con_resolver.visit_basic_block_data(*bb, &body[*bb]);
            }
        }
    }

    fn resolve_locals(&mut self, body: &Body<'_>) {
        let pre_lp = FxHashSet::from_iter(self.loops[0].0.clone());
        let lp = FxHashSet::from_iter(self.loops[0].1.clone());
        let after_lp: FxHashSet<BasicBlock> = (0..body.basic_blocks().len())
            .map(|u| BasicBlock::new(u))
            .filter(|bb| !pre_lp.contains(bb) && !lp.contains(bb))
            .collect();

        self.locals_use = IndexVec::from_elem(InLoop, &body.local_decls);
        struct LocalResolver<'r> {
            r: &'r mut VectorResolver,
            local_use: LocalUse,
        }

        (1..1 + body.arg_count).for_each(|u| self.locals_use[Local::new(u)] = PreLoop);
        impl Visitor<'_> for LocalResolver<'_> {
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
    }

    fn resolve_stmts(&mut self, body: &Body<'_>) {
        pub struct StmtResoler<'r> {
            r: &'r mut VectorResolver,
            current_use: LocalUse,
            locals: BitSet<Local>,
        }

        impl Visitor<'_> for StmtResoler<'_> {
            fn visit_statement(&mut self, statement: &Statement<'_>, location: Location) {
                self.locals.clear();
                match &statement.kind {
                    StorageLive(local) | StorageDead(local) => {
                        self.locals.insert(*local);
                        match self.r.locals_use[*local] {
                            Condition => {
                                self.r.loop_stmts.push(CondiStorage(location, self.locals.clone()))
                            }
                            InLoop => self.r.loop_stmts.push(TempStorage(location)),
                            _ => unimplemented!("storage resolve fail on {:?}", location),
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

                        self.current_use = InLoop;
                        self.visit_rvalue(rvalue, location);
                        let right_use = self.current_use;

                        match (left_use, right_use) {
                            (Condition, _) => {
                                self.r.loop_stmts.push(CondiSet(location, self.locals.clone()))
                            }
                            (InLoop, Condition) => {
                                self.r.loop_stmts.push(CondiGet(location, self.locals.clone()))
                            }
                            (InLoop, InLoop) => {
                                self.r.loop_stmts.push(TempAssign(location, self.locals.clone()))
                            }
                            (InLoop, PreLoop) => self.r.loop_stmts.push(PreGet(location)),
                            (AfterLoop, _) => self.r.loop_stmts.push(AfterSet(location)),
                            _ => unimplemented!("assign resolve fail on {:?}", location),
                        }
                    }
                    _ => unimplemented!("stmt resolve fail on {:?}", location),
                }
            }

            fn visit_local(&mut self, local: &Local, _context: PlaceContext, _location: Location) {
                self.locals.insert(*local);
                if self.current_use < self.r.locals_use[*local] {
                    self.current_use = self.r.locals_use[*local];
                }
            }

            fn visit_terminator(&mut self, terminator: &Terminator<'_>, location: Location) {
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
                                self.r.loop_stmts.push(TempFuncTerminator(location));
                            }
                            _ => unimplemented!("call resolve fail on {:?}", location),
                        }
                    }
                    _ => {
                        unimplemented!("terminator {:?} resolve fail on {:?}", terminator, location)
                    }
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

    fn resort_stmts(&mut self) {
        for i in 0..self.loop_stmts.len() {
            for j in (1..i + 1).rev() {
                if self.loop_stmts[j].move_up(&self.loop_stmts[j - 1]) {
                    self.loop_stmts.swap(j, j - 1);
                } else {
                    break;
                }
            }
        }
    }

    fn resolve_segments(&mut self) {
        let mut index = 0;
        for i in (0..self.loop_stmts.len()).rev() {
            if self.loop_stmts[i].is_condi() {
                index = i + 1;
                break;
            }
        }
        let (inner, vect) = self.loop_stmts.split_at(index);
        self.segments.push(Condi(inner.to_vec()));
        self.segments.push(Vertical(vect.to_vec()));
    }

    fn generate_blocks<'tcx>(&mut self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let outer_loop = body.basic_blocks_mut().push(BasicBlockData::new(None));
        let pre_loop = *self.loops[0].0.last().unwrap();
        let start_loop = self.loops[0].1[0];
        let break_point = *self.break_points.iter().next().unwrap();
        let inner = body.local_decls.push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
        let inside = body.local_decls.push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
        let mut cur_inner_loop = None;

        let mut block;

        let mut to_inner_break = Vec::<BasicBlock>::new();
        let mut to_remain_init = Vec::<BasicBlock>::new();

        let source_info = SourceInfo { span: DUMMY_SP, scope: OUTERMOST_SOURCE_SCOPE };
        /*body[pre_loop].statements.push(Statement {
            source_info, kind: StorageLive(inner),
        });
        body[break_point].statements.push(Statement {
            source_info,
            kind: StorageDead(inner),
        });*/
        for seg in &self.segments {
            match seg {
                Condi(extra_stmts) => {
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
                                        literal: Const::from_usize(tcx, self.vector_len as u64)
                                            .into(),
                                    })),
                                )),
                            ),
                        ))),
                    });
                    block = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    body[inner_loop].terminator = Some(Terminator {
                        source_info,
                        kind: SwitchInt {
                            discr: Operand::Move(Place::from(temp2)),
                            switch_ty: tcx.types.bool,
                            targets: SwitchTargets::static_if(0, block, START_BLOCK),
                        },
                    });
                    to_inner_break.push(inner_loop);

                    for stmt in extra_stmts {
                        match stmt {
                            CondiStorage(location, _) | CondiSet(location, _) => {
                                let st = body[location.block].statements[location.statement_index]
                                    .clone();
                                body[block].statements.push(st)
                            }
                            BreakTerminator(location, _) => {
                                let term = body[location.block].terminator();
                                if let SwitchInt { discr, switch_ty, targets } = term.kind.clone() {
                                    let t = targets.all_targets();
                                    if switch_ty != tcx.types.bool
                                        || t.len() != 2
                                        || t[1] != break_point
                                    {
                                        unimplemented!("unimplemented break terminator:{:?}", term)
                                    }
                                    let next =
                                        body.basic_blocks_mut().push(BasicBlockData::new(None));
                                    body[block].terminator = Some(Terminator {
                                        source_info,
                                        kind: SwitchInt {
                                            discr: discr.clone(),
                                            switch_ty,
                                            targets: SwitchTargets::static_if(0, next, START_BLOCK),
                                        },
                                    });
                                    to_remain_init.push(block);
                                    block = next;
                                } else {
                                    unimplemented!("resolve break terminator failed: {:?}", stmt)
                                }
                            }
                            CondiGet(location, _) => {
                                if let Assign(assign) = body[location.block].statements
                                    [location.statement_index]
                                    .kind
                                    .clone()
                                {
                                    let (place, rvalue) = assign.as_ref();
                                    if let Some(local) = place.as_local() {
                                        if body.local_decls[local].ty == tcx.types.usize {
                                            let temp_simd = if let Some(temp_simd) =
                                                self.temp_to_simd.get(&local)
                                            {
                                                *temp_simd
                                            } else {
                                                let temp_simd =
                                                    body.local_decls.push(LocalDecl::new(
                                                        tcx.mk_array(
                                                            tcx.types.usize,
                                                            self.vector_len as u64,
                                                        ),
                                                        DUMMY_SP,
                                                    ));
                                                self.temp_to_simd.insert(local, temp_simd);
                                                body.vector.push(temp_simd);
                                                temp_simd
                                            };
                                            let des = Place {
                                                local: temp_simd,
                                                projection: tcx
                                                    .intern_place_elems(&[PlaceElem::Index(inner)]),
                                            };
                                            body[block].statements.push(Statement {
                                                source_info,
                                                kind: Assign(Box::new((des, rvalue.clone()))),
                                            })
                                        } else {
                                            unimplemented!(
                                                "unimplemented condi type: {:?}",
                                                body.local_decls[local].ty
                                            )
                                        }
                                    } else {
                                        unimplemented!("cannot put condi to a non-local")
                                    }
                                } else {
                                    bug!("wrong condi getting stmt: {:?}", stmt)
                                }
                            }
                            _ => unimplemented!("resolve condi stmt failed: {:?}", stmt),
                        }
                    }

                    let inner_loop_end = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    body[block].terminator =
                        Some(Terminator { source_info, kind: Goto { target: inner_loop_end } });
                    body[inner_loop_end].statements.push(Statement {
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
                    body[inner_loop_end].terminator =
                        Some(Terminator { source_info, kind: Goto { target: inner_loop } });
                    cur_inner_loop = Some(block);
                }
                Vertical(extra_stmts) => {
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

                    block = inner_break;
                    for stmt in extra_stmts {
                        match stmt {
                            TempStorage(location) => {
                                let kind = body[location.block].statements
                                    [location.statement_index]
                                    .kind
                                    .clone();
                                body[cur_inner_loop.unwrap()].statements.push(Statement { source_info, kind });
                            }
                            AfterSet(location) => {
                                if let Assign(assign) = body[location.block].statements
                                    [location.statement_index]
                                    .kind
                                    .clone()
                                {
                                    let (place, rvalue) = assign.as_ref();
                                    match rvalue {
                                        Rvalue::BinaryOp(_, bin) => {
                                            let (_, temp) = bin.as_ref();
                                            let simd = self
                                                .temp_to_simd
                                                .get(&temp.place().unwrap().as_local().unwrap())
                                                .unwrap();
                                            body[cur_inner_loop.unwrap()].statements.push(
                                                Statement {
                                                    source_info,
                                                    kind: Assign(Box::new((
                                                        temp.place().unwrap(),
                                                        Rvalue::Use(Operand::Copy(Place {
                                                            local: *simd,
                                                            projection: tcx.intern_place_elems(&[
                                                                PlaceElem::Index(inner),
                                                            ]),
                                                        })),
                                                    ))),
                                                },
                                            );
                                            body[cur_inner_loop.unwrap()].statements.push(
                                                Statement {
                                                    source_info,
                                                    kind: Assign(Box::new((
                                                        place.clone(),
                                                        rvalue.clone(),
                                                    ))),
                                                },
                                            );
                                        }
                                        _ => unimplemented!("set after failed"),
                                    }
                                }
                            }
                            TempAssign(location, _bitset) => {
                                if let Assign(assign) = body[location.block].statements
                                    [location.statement_index]
                                    .kind
                                    .clone()
                                {
                                    let (place, rvalue) = assign.as_ref();
                                    match rvalue {
                                        Rvalue::Cast(_, operand, _)
                                        | Rvalue::Use(operand) => {
                                            let simd = self
                                                .temp_to_simd
                                                .get(&operand.place().unwrap().as_local().unwrap())
                                                .unwrap();
                                            body[cur_inner_loop.unwrap()].statements.push(
                                                Statement {
                                                    source_info,
                                                    kind: Assign(Box::new((
                                                        operand.place().unwrap(),
                                                        Rvalue::Use(Operand::Copy(Place {
                                                            local: *simd,
                                                            projection: tcx.intern_place_elems(&[
                                                                PlaceElem::Index(inner),
                                                            ]),
                                                        })),
                                                    ))),
                                                },
                                            );
                                            let ty = place.ty(body, tcx).ty;
                                            let local = place.as_local().unwrap();
                                            let temp_simd = if let Some(temp_simd) =
                                                self.temp_to_simd.get(&local)
                                            {
                                                *temp_simd
                                            } else {
                                                let temp_simd =
                                                    body.local_decls.push(LocalDecl::new(
                                                        tcx.mk_array(ty, self.vector_len as u64),
                                                        DUMMY_SP,
                                                    ));
                                                self.temp_to_simd.insert(local, temp_simd);
                                                body.vector.push(temp_simd);
                                                temp_simd
                                            };
                                            let des = Place {
                                                local: temp_simd,
                                                projection: tcx
                                                    .intern_place_elems(&[PlaceElem::Index(inner)]),
                                            };
                                            body[cur_inner_loop.unwrap()].statements.push(
                                                Statement {
                                                    source_info,
                                                    kind: Assign(Box::new((des, rvalue.clone()))),
                                                },
                                            )
                                        }
                                        _ => unimplemented!(),
                                    }
                                } else {
                                    bug!("wrong assign stmt")
                                }
                            }
                            TempFuncTerminator(location) => {
                                let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                                if let Call {
                                    func,
                                    args,
                                    destination,
                                    cleanup: _,
                                    from_hir_call: _,
                                    fn_span: _,
                                } = body[location.block].terminator().kind.clone()
                                {
                                    let des = destination.unwrap().0.as_local().unwrap();
                                    let ty = body.local_decls[des].ty;
                                    let simd_des =
                                        if let Some(temp_simd) = self.temp_to_simd.get(&des) {
                                            *temp_simd
                                        } else {
                                            let temp_simd = body.local_decls.push(LocalDecl::new(
                                                tcx.mk_array(ty, self.vector_len as u64),
                                                DUMMY_SP,
                                            ));
                                            self.temp_to_simd.insert(des, temp_simd);
                                            body.vector.push(temp_simd);
                                            temp_simd
                                        };
                                    args.iter().for_each(|arg| {
                                        let temp_simd = self
                                            .temp_to_simd
                                            .get(&arg.place().unwrap().as_local().unwrap())
                                            .unwrap();
                                        body[cur_inner_loop.unwrap()].statements.push(Statement {
                                            source_info,
                                            kind: Assign(Box::new((
                                                arg.place().unwrap(),
                                                Rvalue::Use(Operand::Copy(Place {
                                                    local: *temp_simd,
                                                    projection: tcx.intern_place_elems(&[
                                                        PlaceElem::Index(inner),
                                                    ]),
                                                })),
                                            ))),
                                        });
                                    });
                                    let pre_term =
                                        body[cur_inner_loop.unwrap()].terminator().clone();
                                    body[cur_inner_loop.unwrap()].terminator = Some(Terminator {
                                        source_info,
                                        kind: Call {
                                            func,
                                            args,
                                            destination: Some((
                                                Place {
                                                    local: simd_des,
                                                    projection: tcx.intern_place_elems(&[
                                                        PlaceElem::Index(inner),
                                                    ]),
                                                },
                                                next,
                                            )),
                                            cleanup: None,
                                            from_hir_call: false,
                                            fn_span: DUMMY_SP,
                                        },
                                    });
                                    body[next].terminator = Some(pre_term);
                                    cur_inner_loop = Some(next);
                                } else {
                                    bug!("wrong terminator stmt: {:?}", stmt)
                                }
                            }
                            EndLoopTerminator(_location) => {
                                body[block].terminator = Some(Terminator {
                                    source_info,
                                    kind: Goto { target: outer_loop },
                                });
                            }
                            _ => unimplemented!("resolve vertical stmt failed: {:?}", stmt),
                        }
                    }

                    // remain section
                    let remain_init = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    for bb in &to_remain_init {
                        match &mut body[*bb].terminator_mut().kind {
                            SwitchInt { targets, .. } => {
                                assert_eq!(targets.otherwise(), START_BLOCK);
                                *targets.all_targets_mut().last_mut().unwrap() = remain_init;
                            }
                            _ => unimplemented!("wrong to inner break block stmt: {:?}", bb),
                        }
                    }
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
                    block = remain_next;

                    for stmt in extra_stmts {
                        match stmt {
                            TempStorage(location) | AfterSet(location) => {
                                let kind = body[location.block].statements
                                    [location.statement_index]
                                    .kind
                                    .clone();
                                body[block].statements.push(Statement { source_info, kind });
                            }
                            TempAssign(location, bitset) => {
                                bitset.iter().for_each(|local| {
                                    if let Some(simd) = self.temp_to_simd.get(&local) {
                                        body[block].statements.push(Statement {
                                            source_info,
                                            kind: Assign(Box::new((
                                                Place::from(local),
                                                Rvalue::Use(Operand::Copy(Place {
                                                    local: *simd,
                                                    projection: tcx.intern_place_elems(&[
                                                        PlaceElem::Index(inside),
                                                    ]),
                                                })),
                                            ))),
                                        })
                                    }
                                });
                                let kind = body[location.block].statements
                                    [location.statement_index]
                                    .kind
                                    .clone();
                                body[block].statements.push(Statement { source_info, kind: kind });
                            }
                            TempFuncTerminator(location) => {
                                let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                                if let Call {
                                    func,
                                    args,
                                    destination,
                                    cleanup,
                                    from_hir_call,
                                    fn_span,
                                } = body[location.block].terminator().kind.clone()
                                {
                                    body[block].terminator = Some(Terminator {
                                        source_info,
                                        kind: Call {
                                            func,
                                            args,
                                            destination: destination
                                                .map(|(place, _)| (place, next)),
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
                                                    literal: Const::from_usize(tcx, 1 as u64)
                                                        .into(),
                                                })),
                                            )),
                                        ),
                                    ))),
                                });
                                body[block].terminator = Some(Terminator {
                                    source_info,
                                    kind: Goto { target: remain_start },
                                });
                            }
                            _ => unimplemented!("resolve vertical stmt failed: {:?}", stmt),
                        }
                    }
                }
            }
        }
    }
}
