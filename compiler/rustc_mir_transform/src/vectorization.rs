//! This pass implement vectorization of mir

use crate::simplify;
use itertools::Itertools;
use rustc_data_structures::fx::FxHashSet;
use rustc_data_structures::stable_map::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_index::vec::{Idx, IndexVec};
use rustc_middle::mir::visit::{MutatingUseContext, PlaceContext, TyContext, Visitor};
use rustc_middle::mir::BinOp;
use rustc_middle::mir::StatementKind::*;
use rustc_middle::mir::TerminatorKind::*;
use rustc_middle::mir::*;
use rustc_middle::ty;
use rustc_middle::ty::subst::SubstsRef;
use rustc_middle::ty::{
    CanonicalUserTypeAnnotation, Const, Region, Ty, TyCtxt, UserTypeAnnotationIndex, Variance,
};
use rustc_span::symbol::sym;
use rustc_span::{Span, Symbol, DUMMY_SP};
use std::io::{self, Write};
use ExtraStmt::*;
use LocalUse::*;
use VectorStmt::*;

pub struct Vectorize;

#[derive(Default, Debug)]
pub struct VectorResolver<'tcx> {
    vector_len: Option<u64>,
    loops: Vec<(
        Vec<BasicBlock>, /* pre_loop */
        Vec<BasicBlock>, /* loop */
    )>,
    break_points: FxHashSet<BasicBlock>,
    break_blocks: Vec<BasicBlock>,

    conditions: FxHashSet<Local>,
    locals_use: IndexVec<Local, LocalUse>,

    loop_stmts: Vec<ExtraStmt<'tcx>>,

    temp_to_vector: FxHashMap<Local, Local>,
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

    PreGet(Place<'tcx>, Rvalue<'tcx>),
    AfterGet(Place<'tcx>, Rvalue<'tcx>),
    AfterSet(Place<'tcx>, Rvalue<'tcx>, BitSet<Local>),

    TempStorage(Location),
    TempAssign(Place<'tcx>, Rvalue<'tcx>, BitSet<Local>),

    BreakTerminator(Location, BitSet<Local>),
    SetCondiTerminator(Location, BitSet<Local>),
    GetCondiTerminator(Location, BitSet<Local>),

    GotoTerminator(Location),
    EndLoopTerminator(Location),
    TempFuncTerminator(Location),
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
            if above.is_condi() {
                false
            } else {
                true
            }
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

            resolver.generate_blocks(tcx, body);
        };
        simplify::remove_dead_blocks(tcx, body);
        simplify::simplify_locals(body, tcx);
    }
}

#[derive(Debug, Clone)]
enum VectorStmt<'tcx> {
    StraightStmt(Statement<'tcx>),
    StraightTerm(Terminator<'tcx>),
    BinOpAfterSet(Place<'tcx>, BinOp, Operand<'tcx>, Operand<'tcx>),
    UseAssign(Place<'tcx>, Operand<'tcx>),
    BinOpAssign(Place<'tcx>, BinOp, Operand<'tcx>, Operand<'tcx>),
    VectorTerm(Symbol, Vec<Operand<'tcx>>, Place<'tcx>),

    InnerLoopStmt(ExtraStmt<'tcx>),
}

impl<'tcx> VectorResolver<'tcx> {
    fn resolve_loops(&mut self, body: &Body<'_>) {
        let mut cur_bbs = vec![START_BLOCK];
        let mut successors = vec![body[START_BLOCK].terminator().successors()];

        while let Some(successor) = successors.last_mut() {
            if let Some(bb) = successor.next() {
                if let Some(pos) = cur_bbs.iter().find_position(|cur| *cur == bb) {
                    self.loops
                        .push((cur_bbs[0..pos.0].to_vec(), cur_bbs[pos.0..].to_vec()));
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

    fn is_unreachable_block(bb: BasicBlock, body: &Body<'_>) -> bool {
        let block = &body[bb];
        block.statements.is_empty()
            && matches!(
                block.terminator,
                Some(Terminator {
                    source_info: _,
                    kind: Unreachable
                })
            )
    }

    fn resolve_conditions<'r>(&'r mut self, body: &Body<'tcx>) {
        let pre_lp = self.loops[0].0.clone();
        let lp = self.loops[0].1.clone();
        for bb in &lp {
            match &body[*bb].terminator().kind {
                SwitchInt {
                    discr,
                    switch_ty: _,
                    targets,
                } => {
                    let mut is_condi = false;
                    targets.all_targets().into_iter().for_each(|bb| {
                        if lp.iter().all(|target| target != bb) {
                            if !Self::is_unreachable_block(*bb, body) {
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
                    DropAndReplace {
                        place,
                        value,
                        target: _,
                        unwind: _,
                    } if self.r.conditions.contains(&place.local) => {
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
        let mut con_resolver = ConditionResolver {
            changed: !self.conditions.is_empty(),
            r: self,
        };
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

        let mut pre_resolver = LocalResolver {
            r: self,
            local_use: PreLoop,
        };
        for bb in pre_lp.into_iter() {
            pre_resolver.visit_basic_block_data(bb, &body[bb]);
        }

        self.locals_use[Local::new(0)] = AfterLoop;
        let mut after_resolver = LocalResolver {
            r: self,
            local_use: AfterLoop,
        };
        for bb in after_lp.into_iter() {
            after_resolver.visit_basic_block_data(bb, &body[bb]);
        }

        for local in self.conditions.iter() {
            self.locals_use[*local] = Condition;
        }
    }

    fn resolve_stmts<'r>(&'r mut self, body: &Body<'tcx>) {
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
                            Condition => self
                                .r
                                .loop_stmts
                                .push(CondiStorage(location, self.locals.clone())),
                            InLoop => self.r.loop_stmts.push(TempStorage(location)),
                            _ => unimplemented!(
                                "local {:?} is {:?}",
                                local,
                                self.r.locals_use[*local]
                            ),
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
                                ))
                            }
                            (InLoop, InLoop) => self.r.loop_stmts.push(TempAssign(
                                *place,
                                rvalue.clone(),
                                right_locals,
                            )),
                            (InLoop, PreLoop) => {
                                self.r.loop_stmts.push(PreGet(*place, rvalue.clone()))
                            }
                            (InLoop, AfterLoop) => {
                                self.r.loop_stmts.push(AfterGet(*place, rvalue.clone()))
                            }
                            (AfterLoop, _) => self.r.loop_stmts.push(AfterSet(
                                *place,
                                rvalue.clone(),
                                right_locals,
                            )),
                            _ => unimplemented!("assign resolve fail on {:?}", location),
                        }
                    }
                    _ => unimplemented!("stmt resolve fail on {:?}", location),
                }
            }

            fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
                self.locals.clear();
                match &terminator.kind {
                    SwitchInt {
                        discr,
                        switch_ty: _,
                        targets: _,
                    } => {
                        self.visit_operand(discr, location);
                        if self.r.break_blocks.contains(&location.block) {
                            self.r
                                .loop_stmts
                                .push(BreakTerminator(location, self.locals.clone()));
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
                    Call {
                        func,
                        args,
                        destination,
                        cleanup: _,
                        from_hir_call: _,
                        fn_span: _,
                    } => {
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

    fn resort_stmts<'r>(&'r mut self) {
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

    fn resolve_vector_len<'r>(
        &'r mut self,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        vect_stmts: &Vec<ExtraStmt<'tcx>>,
    ) {
        let mut vector_type = None;
        for stmt in vect_stmts {
            match stmt {
                AfterSet(_place, rvalue, _) | TempAssign(_place, rvalue, _) => match rvalue {
                    Rvalue::BinaryOp(_, ops) => {
                        let (op1, _op2) = ops.as_ref();
                        let ty = op1.ty(body, tcx);
                        if vector_type.is_none() {
                            vector_type = Some(ty)
                        } else if vector_type.unwrap() != ty {
                            unimplemented!(
                                "different vector type: {:?}, {:?}",
                                vector_type.unwrap(),
                                ty
                            )
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        if let Some(ty) = vector_type {
            let total_len = if tcx.sess.target.arch == "x86_64" {
                1024
            } else {
                256
            };
            let elem_len = if ty == tcx.types.f32 {
                32
            } else if ty == tcx.types.u8 {
                8
            } else {
                unimplemented!("unimplemented vector element type: {:?}", ty)
            };
            self.vector_len = Some(total_len / elem_len);
        }
    }

    fn get_vector(&self, temp: &Local) -> Option<Local> {
        *self.temp_to_vector.get(temp)
    }

    fn insert_vector(&mut self, temp: &Local, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) -> bool {
        if let Some(v) = self.temp_to_vector.get(temp) {
            false
        } else {
            let ty = body.local_decls[*temp].ty;
            let v = body.local_decls.push(LocalDecl::new(
                tcx.mk_array(ty, self.vector_len.unwrap()),
                DUMMY_SP,
            ));
            self.temp_to_vector.insert(*temp, v);
            if ty.is_primitive() {
                body.vector.push(v);
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
        let source_info = SourceInfo {
            span: DUMMY_SP,
            scope: OUTERMOST_SOURCE_SCOPE,
        };
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
        body[outer_loop].terminator = Some(Terminator {
            source_info,
            kind: Goto { target: inner_loop },
        });

        let temp1 = body
            .local_decls
            .push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
        body[inner_loop].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(temp1),
                Rvalue::Use(Operand::Copy(Place::from(inner))),
            ))),
        });
        let temp2 = body
            .local_decls
            .push(LocalDecl::new(tcx.types.bool, DUMMY_SP));
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
                CondiStorage(location, _) | SetCondiTerminator(location, _) => {
                    let st = body[location.block].statements[location.statement_index].clone();
                    body[block].statements.push(st);
                }
                CondiSet(place, rvalue, _) => {
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
                    if let SwitchInt {
                        discr,
                        switch_ty,
                        targets,
                    } = term.kind.clone()
                    {
                        let next = body.basic_blocks_mut().push(BasicBlockData::new(None));
                        let mut new_targets = targets.clone();
                        for bb in new_targets.all_targets_mut() {
                            assert_ne!(*bb, START_BLOCK);
                            if self.break_points.get(bb).is_some() {
                                *bb = START_BLOCK;
                            } else if Self::is_unreachable_block(*bb, body) {
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
                    // TODO: needs legality check here: If the get type is a
                    // mutable Ref(..) or RawPtr(..), it must be guaranteed that
                    // the written value will not be read in the next loop.
                    // Otherwise, this mir cannot be vectorized.
                    if let Some(local) = place.as_local() {
                        self.insert_vector(&place.as_local().unwrap(), tcx, body);
                        let temp_simd = self.get_vector(&local).unwrap();
                        let des = Place {
                            local: temp_simd,
                            projection: tcx.intern_place_elems(&[PlaceElem::Index(inner)]),
                        };
                        body[block].statements.push(Statement {
                            source_info,
                            kind: Assign(Box::new((des, rvalue.clone()))),
                        })
                    } else {
                        unimplemented!("cannot put condi to a non-local")
                    }
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
        body[block].terminator = Some(Terminator {
            source_info,
            kind: Goto { target: inner_loop },
        });
    }

    fn new_inner_loop<'r>(
        &'r mut self,
        tcx: TyCtxt<'tcx>,
        body: &mut Body<'tcx>,
        current: BasicBlock,
        stmts: Vec<ExtraStmt<'tcx>>,
        inner: Local,
    ) -> BasicBlock {
        let source_info = SourceInfo {
            span: DUMMY_SP,
            scope: OUTERMOST_SOURCE_SCOPE,
        };
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
        body[current].terminator = Some(Terminator {
            source_info,
            kind: Goto { target: loop_start },
        });
        let temp1 = body
            .local_decls
            .push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
        body[loop_start].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(temp1),
                Rvalue::Use(Operand::Copy(Place::from(inner))),
            ))),
        });
        let temp2 = body
            .local_decls
            .push(LocalDecl::new(tcx.types.bool, DUMMY_SP));
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
        let mut loop_next = body.basic_blocks_mut().push(BasicBlockData::new(None));
        for stmt in stmts {
            match stmt {
                TempAssign(place, rvalue, bitset) => {
                    bitset.iter().for_each(|local| {
                        if let Some(simd_rhs) = self.get_vector(&local) {
                            body[loop_next].statements.push(Statement {
                                source_info,
                                kind: Assign(Box::new((
                                    Place::from(local),
                                    Rvalue::Use(Operand::Copy(Place {
                                        local: simd_rhs,
                                        projection: tcx.intern_place_elems(&[PlaceElem::Index(inner)]),
                                    })),
                                ))),
                            })
                        };
                    });
                    let local = place.as_local().unwrap();
                    let simd_lhs = self.get_vector(&local);
                    let des = Place {
                        local: simd_lhs,
                        projection: tcx.intern_place_elems(&[PlaceElem::Index(inner)]),
                    };
                    body[loop_next].statements.push(Statement {
                        source_info,
                        kind: Assign(Box::new((des, rvalue.clone()))),
                    })
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
                        args.iter().for_each(|operand| {
                            let local = operand.place().unwrap().as_local().unwrap();
                            let simd_rhs = self.get_vector(&local);
                            body[loop_next].statements.push(Statement {
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
                        });
                        let place = destination.unwrap().0;
                        let local = place.as_local().unwrap();
                        let simd_lhs = self.get_vector(&local);
                        let des = Place {
                            local: simd_lhs,
                            projection: tcx.intern_place_elems(&[PlaceElem::Index(inner)]),
                        };
                        body[loop_next].terminator = Some(Terminator {
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
                        loop_next = next;
                    } else {
                        bug!("wrong terminator stmt: {:?}", stmt)
                    }
                }
                AfterSet(place, rvalue, bitset) => {
                    bitset.iter().for_each(|local| {
                        if let Some(simd_rhs) = self.temp_to_vector.get(&local) {
                            body[loop_next].statements.push(Statement {
                                source_info,
                                kind: Assign(Box::new((
                                    Place::from(local),
                                    Rvalue::Use(Operand::Copy(Place {
                                        local: *simd_rhs,
                                        projection: tcx
                                            .intern_place_elems(&[PlaceElem::Index(inner)]),
                                    })),
                                ))),
                            })
                        };
                    });
                    body[loop_next].statements.push(Statement {
                        source_info,
                        kind: Assign(Box::new((place, rvalue.clone()))),
                    });
                }
                _ => unimplemented!("stmt {:?} are not supported in inner loop", stmt),
            }
        }
        body[loop_next].statements.push(Statement {
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
        body[loop_next].terminator = Some(Terminator {
            source_info,
            kind: Goto { target: loop_start },
        });

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
        let source_info = SourceInfo {
            span: DUMMY_SP,
            scope: OUTERMOST_SOURCE_SCOPE,
        };
        let mut resolved_stmts = Vec::new();
        for stmt in &vect_stmts {
            match stmt {
                TempStorage(location) => {
                    let kind = body[location.block].statements[location.statement_index]
                        .kind
                        .clone();
                    resolved_stmts.push(StraightStmt(Statement { source_info, kind }));
                }
                AfterSet(place, rvalue, _bitset) => {
                    // TODO: An optimization can be added: if the value being written will not
                    // be read in the loop, move the writing process out of the loop.
                    match rvalue {
                        Rvalue::BinaryOp(binop, ops) => {
                            let (op1, op2) = ops.as_ref();
                            resolved_stmts.push(BinOpAfterSet(
                                *place,
                                *binop,
                                op1.clone(),
                                op2.clone(),
                            ));
                        }
                        _ => {
                            resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                        }
                    }
                }
                TempAssign(place, rvalue, _bitset) => match rvalue {
                    Rvalue::Use(operand) => {
                        resolved_stmts.push(UseAssign(*place, operand.clone()));
                    }
                    Rvalue::BinaryOp(bin_op, ops) => {
                        let (op1, op2) = ops.as_ref();
                        resolved_stmts.push(BinOpAssign(*place, *bin_op, op1.clone(), op2.clone()));
                    }
                    _ => {
                        resolved_stmts.push(InnerLoopStmt(stmt.clone()));
                    }
                },
                TempFuncTerminator(location) => {
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
                _ => unimplemented!("resolve vertical stmt failed: {:?}", stmt),
            }
        }
        resolved_stmts
    }

    fn resolve_temp_to_vector<'r>(
        &'r mut self,
        tcx: TyCtxt<'tcx>,
        body: &mut Body<'tcx>,
        resolved_stmts: &Vec<VectorStmt>,
    ) {
        let mut changed = true;
        // insert vector from vertical statements
        for stmt in resolved_stmts {
            match stmt {
                InnerLoopStmt(..) | StraightStmt(..) | StraightTerm(..) | UseAssign(..)
                | BinOpAfterSet(..) => {}
                BinOpAssign(place, _, op1, op2) => {
                    self.insert_vector(&place.as_local().unwrap(), tcx, body);
                    self.insert_vector(&op1.place().unwrap().as_local().unwrap(), tcx, body);
                    self.insert_vector(&op2.place().unwrap().as_local().unwrap(), tcx, body);
                }
                VectorTerm(Symbol, args, des) => match Symbol {
                    sym::simd_fsqrt => {
                        self.insert_vector(&des.as_local().unwrap(), tcx, body);
                        args.iter().for_each(|arg| {
                            self.insert_vector(
                                &arg.place().unwrap().as_local().unwrap(),
                                tcx,
                                body,
                            );
                        });
                    }
                    _ => unimplemented!("unimplemented vector func"),
                },
            }
        }

        // insert vector from inner loop statements and use rvalue
        while changed {
            changed = false;
            for stmt in resolved_stmts {
                match stmt {
                    InnerLoopStmt(extra_stmt) => match extra_stmt {
                        TempAssign(place, _rvalue, bitset) => {
                            if bitset.iter().any(|local| self.get_vector(&local).is_some())
                                && self.insert_vector(&place.as_local().unwrap(), tcx, body)
                            {
                                changed = true
                            }
                        }
                        _ => {}
                    },
                    UseAssign(place, op) => {
                        if let Some(rhs) = op.place().map(|place| place) {
                            if let Some(rhs) = rhs.as_local() {
                                if self.temp_to_vector.get(&rhs).is_some() {
                                    if self.insert_vector(&place.as_local().unwrap(), tcx, body) {
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                    StraightStmt(..) | StraightTerm(..) | BinOpAfterSet(..) | BinOpAssign(..)
                    | VectorTerm(..) => {}
                }
            }
        }
    }

    fn generate_vector_section<'r>(
        &'r mut self,
        tcx: TyCtxt<'tcx>,
        body: &mut Body<'tcx>,
        mut current: BasicBlock,
        vect_stmts: &Vec<ExtraStmt<'tcx>>,
        inner: Local,
        outer_loop: BasicBlock,
    ) -> BasicBlock {
        let source_info = SourceInfo {
            span: DUMMY_SP,
            scope: OUTERMOST_SOURCE_SCOPE,
        };
        let resolved_stmts = self.resolve_vector_section(tcx, body, outer_loop, vect_stmts.clone());
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
                        body[current].statements.push(stmt);
                    }
                    BinOpAfterSet(place, bin_op, op1, op2) => {
                        // TODO: An optimization can be added: if the value being written will not
                        // be read in the loop, move the writing process out of the loop.
                        match (op1.place(), op2.place()) {
                            (Some(p1), Some(p2)) => {
                                let (l1, l2) = (p1.as_local().unwrap(), p2.as_local().unwrap());
                                match (self.locals_use.get(l1), self.locals_use.get(l2)) {
                                    (Some(AfterLoop), Some(InLoop)) => {
                                        let func = match bin_op {
                                            BinOp::Add => sym::simd_reduce_add_unordered,
                                            _ => unimplemented!(
                                                "unimplemented after set bin op: {:?}",
                                                bin_op
                                            ),
                                        };
                                        let next =
                                            body.basic_blocks_mut().push(BasicBlockData::new(None));
                                        let args =
                                            vec![Operand::Move(Place::from(self.get_vector(&l2)))];
                                        body[current].terminator = Some(Terminator {
                                            source_info,
                                            kind: VectorFunc {
                                                func,
                                                args,
                                                destination: Some((p2, next)),
                                            },
                                        });
                                        body[next].statements.push(Statement {
                                            source_info,
                                            kind: Assign(Box::new((
                                                place,
                                                Rvalue::BinaryOp(bin_op, Box::new((op1, op2))),
                                            ))),
                                        });
                                        current = next;
                                    }
                                    _ => unimplemented!(
                                        "set after ops local use: {:?} with {:?}",
                                        l1,
                                        l2
                                    ),
                                }
                            }
                            _ => unimplemented!("set after ops: {:?} with {:?}", op1, op2),
                        }
                    }
                    UseAssign(place, operand) => {
                        let simd_rhs =
                            self.get_vector(&operand.place().unwrap().as_local().unwrap());
                        let local = place.as_local().unwrap();
                        let simd_lhs = self.get_vector(&local);
                        body[current].statements.push(Statement {
                            source_info,
                            kind: Assign(Box::new((
                                Place::from(simd_lhs),
                                Rvalue::Use(Operand::Copy(Place::from(simd_rhs))),
                            ))),
                        })
                    }
                    BinOpAssign(place, bin_op, op1, op2) => {
                        let func = match bin_op {
                            BinOp::Add => sym::simd_add,
                            BinOp::Shr => sym::simd_shr,
                            BinOp::BitAnd => sym::simd_and,
                            _ => unimplemented!("unimplemented binop: {:?}", bin_op),
                        };

                        let (simd_rhs1, simd_rhs2) = (
                            self.get_vector(&op1.place().unwrap().as_local().unwrap()),
                            self.get_vector(&op2.place().unwrap().as_local().unwrap()),
                        );
                        let args = vec![
                            Operand::Move(Place::from(simd_rhs1)),
                            Operand::Move(Place::from(simd_rhs2)),
                        ];

                        let des = place.as_local().unwrap();
                        let simd_des = self.get_vector(&des);

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
                    VectorTerm(func, args, des) => {
                        let simd_des = self.get_vector(&des.as_local().unwrap());
                        let args: Vec<_> = args
                            .iter()
                            .map(|arg| {
                                Operand::Move(Place::from(
                                    self.get_vector(&arg.place().unwrap().as_local().unwrap()),
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
        current
    }

    fn generate_remain_section<'r>(
        &'r mut self,
        tcx: TyCtxt<'tcx>,
        body: &mut Body<'tcx>,
        vect_stmts: &Vec<ExtraStmt<'tcx>>,
        inner: Local,
        remain_init: BasicBlock,
    ) {
        let source_info = SourceInfo {
            span: DUMMY_SP,
            scope: OUTERMOST_SOURCE_SCOPE,
        };
        let break_point = *self.break_points.iter().next().unwrap();
        let inside = body
            .local_decls
            .push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
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
        body[remain_init].terminator = Some(Terminator {
            source_info,
            kind: Goto {
                target: remain_start,
            },
        });
        let temp1 = body
            .local_decls
            .push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
        body[remain_start].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(temp1),
                Rvalue::Use(Operand::Copy(Place::from(inside))),
            ))),
        });
        let temp2 = body
            .local_decls
            .push(LocalDecl::new(tcx.types.usize, DUMMY_SP));
        body[remain_start].statements.push(Statement {
            source_info,
            kind: Assign(Box::new((
                Place::from(temp2),
                Rvalue::Use(Operand::Copy(Place::from(inner))),
            ))),
        });
        let temp3 = body
            .local_decls
            .push(LocalDecl::new(tcx.types.bool, DUMMY_SP));
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
                    let kind = body[location.block].statements[location.statement_index]
                        .kind
                        .clone();
                    body[block].statements.push(Statement { source_info, kind });
                }
                AfterSet(place, rvalue, _) => {
                    body[block].statements.push(Statement {
                        source_info,
                        kind: Assign(Box::new((*place, rvalue.clone()))),
                    });
                }
                TempAssign(place, rvalue, bitset) => {
                    bitset.iter().for_each(|local| {
                        if let Some(simd) = self.temp_to_vector.get(&local) {
                            body[block].statements.push(Statement {
                                source_info,
                                kind: Assign(Box::new((
                                    Place::from(local),
                                    Rvalue::Use(Operand::Copy(Place {
                                        local: *simd,
                                        projection: tcx
                                            .intern_place_elems(&[PlaceElem::Index(inside)]),
                                    })),
                                ))),
                            })
                        }
                    });
                    body[block].statements.push(Statement {
                        source_info,
                        kind: Assign(Box::new((*place, rvalue.clone()))),
                    });
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
                    body[block].terminator = Some(Terminator {
                        source_info,
                        kind: Goto {
                            target: remain_start,
                        },
                    });
                }
                _ => unimplemented!("resolve vertical stmt failed: {:?}", stmt),
            }
        }
    }

    fn generate_blocks<'r>(&'r mut self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let (condi_stmts, vect_stmts) = self.resolve_segments();
        self.resolve_vector_len(body, tcx, &vect_stmts);

        let inner = body
            .local_decls
            .push(LocalDecl::new(tcx.types.usize, DUMMY_SP));

        let outer_loop = body.basic_blocks_mut().push(BasicBlockData::new(None));

        let mut to_inner_break = Vec::<BasicBlock>::new();
        let mut to_remain_init = Vec::<BasicBlock>::new();

        // TODO: Add Storage statement for newly generated locals

        // TODO: Keep source_info as much as possible

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

        self.generate_vector_section(tcx, body, inner_break, &vect_stmts, inner, outer_loop);

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
        self.generate_remain_section(tcx, body, &vect_stmts, inner, remain_init);
    }
}
