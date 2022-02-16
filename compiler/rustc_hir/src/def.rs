use crate::def_id::{DefId, CRATE_DEF_INDEX, LOCAL_CRATE};
use crate::hir;

use rustc_ast as ast;
use rustc_ast::NodeId;
use rustc_macros::HashStable_Generic;
use rustc_span::hygiene::MacroKind;
use rustc_span::Symbol;

use std::array::IntoIter;
use std::fmt::Debug;

/// Encodes if a `DefKind::Ctor` is the constructor of an enum variant or a struct.
#[derive(Clone, Copy, PartialEq, Eq, Encodable, Decodable, Hash, Debug)]
#[derive(HashStable_Generic)]
pub enum CtorOf {
    /// This `DefKind::Ctor` is a synthesized constructor of a tuple or unit struct.
    Struct,
    /// This `DefKind::Ctor` is a synthesized constructor of a tuple or unit variant.
    Variant,
}

/// What kind of constructor something is.
#[derive(Clone, Copy, PartialEq, Eq, Encodable, Decodable, Hash, Debug)]
#[derive(HashStable_Generic)]
pub enum CtorKind {
    /// Constructor function automatically created by a tuple struct/variant.
    Fn,
    /// Constructor constant automatically created by a unit struct/variant.
    Const,
    /// Unusable name in value namespace created by a struct variant.
    Fictive,
}

/// An attribute that is not a macro; e.g., `#[inline]` or `#[rustfmt::skip]`.
#[derive(Clone, Copy, PartialEq, Eq, Encodable, Decodable, Hash, Debug)]
#[derive(HashStable_Generic)]
pub enum NonMacroAttrKind {
    /// Single-segment attribute defined by the language (`#[inline]`)
    Builtin(Symbol),
    /// Multi-segment custom attribute living in a "tool module" (`#[rustfmt::skip]`).
    Tool,
    /// Single-segment custom attribute registered by a derive macro (`#[serde(default)]`).
    DeriveHelper,
    /// Single-segment custom attribute registered by a derive macro
    /// but used before that derive macro was expanded (deprecated).
    DeriveHelperCompat,
    /// Single-segment custom attribute registered with `#[register_attr]`.
    Registered,
}

/// What kind of definition something is; e.g., `mod` vs `struct`.
#[derive(Clone, Copy, PartialEq, Eq, Encodable, Decodable, Hash, Debug)]
#[derive(HashStable_Generic)]
pub enum DefKind {
    // Type namespace
    Mod,
    /// Refers to the struct itself, [`DefKind::Ctor`] refers to its constructor if it exists.
    Struct,
    Union,
    Enum,
    /// Refers to the variant itself, [`DefKind::Ctor`] refers to its constructor if it exists.
    Variant,
    Trait,
    /// Type alias: `type Foo = Bar;`
    TyAlias,
    /// Type from an `extern` block.
    ForeignTy,
    /// Trait alias: `trait IntIterator = Iterator<Item = i32>;`
    TraitAlias,
    /// Associated type: `trait MyTrait { type Assoc; }`
    AssocTy,
    /// Type parameter: the `T` in `struct Vec<T> { ... }`
    TyParam,

    // Value namespace
    Fn,
    Const,
    /// Constant generic parameter: `struct Foo<const N: usize> { ... }`
    ConstParam,
    Static,
    /// Refers to the struct or enum variant's constructor.
    ///
    /// The reason `Ctor` exists in addition to [`DefKind::Struct`] and
    /// [`DefKind::Variant`] is because structs and enum variants exist
    /// in the *type* namespace, whereas struct and enum variant *constructors*
    /// exist in the *value* namespace.
    ///
    /// You may wonder why enum variants exist in the type namespace as opposed
    /// to the value namespace. Check out [RFC 2593] for intuition on why that is.
    ///
    /// [RFC 2593]: https://github.com/rust-lang/rfcs/pull/2593
    Ctor(CtorOf, CtorKind),
    /// Associated function: `impl MyStruct { fn associated() {} }`
    AssocFn,
    /// Associated constant: `trait MyTrait { const ASSOC: usize; }`
    AssocConst,

    // Macro namespace
    Macro(MacroKind),

    // Not namespaced (or they are, but we don't treat them so)
    ExternCrate,
    Use,
    /// An `extern` block.
    ForeignMod,
    /// Anonymous constant, e.g. the `1 + 2` in `[u8; 1 + 2]`
    AnonConst,
    /// An inline constant, e.g. `const { 1 + 2 }`
    InlineConst,
    /// Opaque type, aka `impl Trait`.
    OpaqueTy,
    Field,
    /// Lifetime parameter: the `'a` in `struct Foo<'a> { ... }`
    LifetimeParam,
    /// A use of `global_asm!`.
    GlobalAsm,
    Impl,
    Closure,
    Generator,
}

impl DefKind {
    pub fn descr(self, def_id: DefId) -> &'static str {
        match self {
            DefKind::Fn => "function",
            DefKind::Mod if def_id.index == CRATE_DEF_INDEX && def_id.krate != LOCAL_CRATE => {
                "crate"
            }
            DefKind::Mod => "module",
            DefKind::Static => "static",
            DefKind::Enum => "enum",
            DefKind::Variant => "variant",
            DefKind::Ctor(CtorOf::Variant, CtorKind::Fn) => "tuple variant",
            DefKind::Ctor(CtorOf::Variant, CtorKind::Const) => "unit variant",
            DefKind::Ctor(CtorOf::Variant, CtorKind::Fictive) => "struct variant",
            DefKind::Struct => "struct",
            DefKind::Ctor(CtorOf::Struct, CtorKind::Fn) => "tuple struct",
            DefKind::Ctor(CtorOf::Struct, CtorKind::Const) => "unit struct",
            DefKind::Ctor(CtorOf::Struct, CtorKind::Fictive) => {
                panic!("impossible struct constructor")
            }
            DefKind::OpaqueTy => "opaque type",
            DefKind::TyAlias => "type alias",
            DefKind::TraitAlias => "trait alias",
            DefKind::AssocTy => "associated type",
            DefKind::Union => "union",
            DefKind::Trait => "trait",
            DefKind::ForeignTy => "foreign type",
            DefKind::AssocFn => "associated function",
            DefKind::Const => "constant",
            DefKind::AssocConst => "associated constant",
            DefKind::TyParam => "type parameter",
            DefKind::ConstParam => "const parameter",
            DefKind::Macro(macro_kind) => macro_kind.descr(),
            DefKind::LifetimeParam => "lifetime parameter",
            DefKind::Use => "import",
            DefKind::ForeignMod => "foreign module",
            DefKind::AnonConst => "constant expression",
            DefKind::InlineConst => "inline constant",
            DefKind::Field => "field",
            DefKind::Impl => "implementation",
            DefKind::Closure => "closure",
            DefKind::Generator => "generator",
            DefKind::ExternCrate => "extern crate",
            DefKind::GlobalAsm => "global assembly block",
        }
    }

    /// Gets an English article for the definition.
    pub fn article(&self) -> &'static str {
        match *self {
            DefKind::AssocTy
            | DefKind::AssocConst
            | DefKind::AssocFn
            | DefKind::Enum
            | DefKind::OpaqueTy
            | DefKind::Impl
            | DefKind::Use
            | DefKind::InlineConst
            | DefKind::ExternCrate => "an",
            DefKind::Macro(macro_kind) => macro_kind.article(),
            _ => "a",
        }
    }

    pub fn ns(&self) -> Option<Namespace> {
        match self {
            DefKind::Mod
            | DefKind::Struct
            | DefKind::Union
            | DefKind::Enum
            | DefKind::Variant
            | DefKind::Trait
            | DefKind::OpaqueTy
            | DefKind::TyAlias
            | DefKind::ForeignTy
            | DefKind::TraitAlias
            | DefKind::AssocTy
            | DefKind::TyParam => Some(Namespace::TypeNS),

            DefKind::Fn
            | DefKind::Const
            | DefKind::ConstParam
            | DefKind::Static
            | DefKind::Ctor(..)
            | DefKind::AssocFn
            | DefKind::AssocConst => Some(Namespace::ValueNS),

            DefKind::Macro(..) => Some(Namespace::MacroNS),

            // Not namespaced.
            DefKind::AnonConst
            | DefKind::InlineConst
            | DefKind::Field
            | DefKind::LifetimeParam
            | DefKind::ExternCrate
            | DefKind::Closure
            | DefKind::Generator
            | DefKind::Use
            | DefKind::ForeignMod
            | DefKind::GlobalAsm
            | DefKind::Impl => None,
        }
    }
}

/// The resolution of a path or export.
///
/// For every path or identifier in Rust, the compiler must determine
/// what the path refers to. This process is called name resolution,
/// and `Res` is the primary result of name resolution.
///
/// For example, everything prefixed with `/* Res */` in this example has
/// an associated `Res`:
///
/// ```
/// fn str_to_string(s: & /* Res */ str) -> /* Res */ String {
///     /* Res */ String::from(/* Res */ s)
/// }
///
/// /* Res */ str_to_string("hello");
/// ```
///
/// The associated `Res`s will be:
///
/// - `str` will resolve to [`Res::PrimTy`];
/// - `String` will resolve to [`Res::Def`], and the `Res` will include the [`DefId`]
///   for `String` as defined in the standard library;
/// - `String::from` will also resolve to [`Res::Def`], with the [`DefId`]
///   pointing to `String::from`;
/// - `s` will resolve to [`Res::Local`];
/// - the call to `str_to_string` will resolve to [`Res::Def`], with the [`DefId`]
///   pointing to the definition of `str_to_string` in the current crate.
//
#[derive(Clone, Copy, PartialEq, Eq, Encodable, Decodable, Hash, Debug)]
#[derive(HashStable_Generic)]
pub enum Res<Id = hir::HirId> {
    /// Definition having a unique ID (`DefId`), corresponds to something defined in user code.
    ///
    /// **Not bound to a specific namespace.**
    Def(DefKind, DefId),

    // Type namespace
    /// A primitive type such as `i32` or `str`.
    ///
    /// **Belongs to the type namespace.**
    PrimTy(hir::PrimTy),
    /// The `Self` type, optionally with the trait it is associated with
    /// and optionally with the [`DefId`] of the impl it is associated with.
    ///
    /// **Belongs to the type namespace.**
    ///
    /// For example, the `Self` in
    ///
    /// ```
    /// trait Foo {
    ///     fn foo() -> Box<Self>;
    /// }
    /// ```
    ///
    /// would have the [`DefId`] of `Foo` associated with it. The `Self` in
    ///
    /// ```
    /// struct Bar;
    ///
    /// impl Bar {
    ///     fn new() -> Self { Bar }
    /// }
    /// ```
    ///
    /// would have the [`DefId`] of the impl associated with it. Finally, the `Self` in
    ///
    /// ```
    /// impl Foo for Bar {
    ///     fn foo() -> Box<Self> { Box::new(Bar) }
    /// }
    /// ```
    ///
    /// would have both the [`DefId`] of `Foo` and the [`DefId`] of the impl
    /// associated with it.
    ///
    /// *See also [`Res::SelfCtor`].*
    ///
    /// -----
    ///
    /// HACK(min_const_generics): impl self types also have an optional requirement to **not** mention
    /// any generic parameters to allow the following with `min_const_generics`:
    /// ```
    /// impl Foo { fn test() -> [u8; std::mem::size_of::<Self>()] { todo!() } }
    /// ```
    /// We do however allow `Self` in repeat expression even if it is generic to not break code
    /// which already works on stable while causing the `const_evaluatable_unchecked` future compat lint.
    ///
    /// FIXME(generic_const_exprs): Remove this bodge once that feature is stable.
    SelfTy(
        /// Optionally, the trait associated with this `Self` type.
        Option<DefId>,
        /// Optionally, the impl associated with this `Self` type.
        Option<(DefId, bool)>,
    ),
    /// A tool attribute module; e.g., the `rustfmt` in `#[rustfmt::skip]`.
    ///
    /// **Belongs to the type namespace.**
    ToolMod,

    // Value namespace
    /// The `Self` constructor, along with the [`DefId`]
    /// of the impl it is associated with.
    ///
    /// **Belongs to the value namespace.**
    ///
    /// *See also [`Res::SelfTy`].*
    SelfCtor(DefId),
    /// A local variable or function parameter.
    ///
    /// **Belongs to the value namespace.**
    Local(Id),

    // Macro namespace
    /// An attribute that is *not* implemented via macro.
    /// E.g., `#[inline]` and `#[rustfmt::skip]`, which are essentially directives,
    /// as opposed to `#[test]`, which is a builtin macro.
    ///
    /// **Belongs to the macro namespace.**
    NonMacroAttr(NonMacroAttrKind), // e.g., `#[inline]` or `#[rustfmt::skip]`

    // All namespaces
    /// Name resolution failed. We use a dummy `Res` variant so later phases
    /// of the compiler won't crash and can instead report more errors.
    ///
    /// **Not bound to a specific namespace.**
    Err,
}

/// The result of resolving a path before lowering to HIR,
/// with "module" segments resolved and associated item
/// segments deferred to type checking.
/// `base_res` is the resolution of the resolved part of the
/// path, `unresolved_segments` is the number of unresolved
/// segments.
///
/// ```text
/// module::Type::AssocX::AssocY::MethodOrAssocType
/// ^~~~~~~~~~~~  ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// base_res      unresolved_segments = 3
///
/// <T as Trait>::AssocX::AssocY::MethodOrAssocType
///       ^~~~~~~~~~~~~~  ^~~~~~~~~~~~~~~~~~~~~~~~~
///       base_res        unresolved_segments = 2
/// ```
#[derive(Copy, Clone, Debug)]
pub struct PartialRes {
    base_res: Res<NodeId>,
    unresolved_segments: usize,
}

impl PartialRes {
    #[inline]
    pub fn new(base_res: Res<NodeId>) -> Self {
        PartialRes { base_res, unresolved_segments: 0 }
    }

    #[inline]
    pub fn with_unresolved_segments(base_res: Res<NodeId>, mut unresolved_segments: usize) -> Self {
        if base_res == Res::Err {
            unresolved_segments = 0
        }
        PartialRes { base_res, unresolved_segments }
    }

    #[inline]
    pub fn base_res(&self) -> Res<NodeId> {
        self.base_res
    }

    #[inline]
    pub fn unresolved_segments(&self) -> usize {
        self.unresolved_segments
    }
}

/// Different kinds of symbols can coexist even if they share the same textual name.
/// Therefore, they each have a separate universe (known as a "namespace").
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Namespace {
    /// The type namespace includes `struct`s, `enum`s, `union`s, `trait`s, and `mod`s
    /// (and, by extension, crates).
    ///
    /// Note that the type namespace includes other items; this is not an
    /// exhaustive list.
    TypeNS,
    /// The value namespace includes `fn`s, `const`s, `static`s, and local variables (including function arguments).
    ValueNS,
    /// The macro namespace includes `macro_rules!` macros, declarative `macro`s,
    /// procedural macros, attribute macros, `derive` macros, and non-macro attributes
    /// like `#[inline]` and `#[rustfmt::skip]`.
    MacroNS,
}

impl Namespace {
    /// The English description of the namespace.
    pub fn descr(self) -> &'static str {
        match self {
            Self::TypeNS => "type",
            Self::ValueNS => "value",
            Self::MacroNS => "macro",
        }
    }
}

/// Just a helper ‒ separate structure for each namespace.
#[derive(Copy, Clone, Default, Debug)]
pub struct PerNS<T> {
    pub value_ns: T,
    pub type_ns: T,
    pub macro_ns: T,
}

impl<T> PerNS<T> {
    pub fn map<U, F: FnMut(T) -> U>(self, mut f: F) -> PerNS<U> {
        PerNS { value_ns: f(self.value_ns), type_ns: f(self.type_ns), macro_ns: f(self.macro_ns) }
    }

    pub fn into_iter(self) -> IntoIter<T, 3> {
        [self.value_ns, self.type_ns, self.macro_ns].into_iter()
    }

    pub fn iter(&self) -> IntoIter<&T, 3> {
        [&self.value_ns, &self.type_ns, &self.macro_ns].into_iter()
    }
}

impl<T> ::std::ops::Index<Namespace> for PerNS<T> {
    type Output = T;

    fn index(&self, ns: Namespace) -> &T {
        match ns {
            Namespace::ValueNS => &self.value_ns,
            Namespace::TypeNS => &self.type_ns,
            Namespace::MacroNS => &self.macro_ns,
        }
    }
}

impl<T> ::std::ops::IndexMut<Namespace> for PerNS<T> {
    fn index_mut(&mut self, ns: Namespace) -> &mut T {
        match ns {
            Namespace::ValueNS => &mut self.value_ns,
            Namespace::TypeNS => &mut self.type_ns,
            Namespace::MacroNS => &mut self.macro_ns,
        }
    }
}

impl<T> PerNS<Option<T>> {
    /// Returns `true` if all the items in this collection are `None`.
    pub fn is_empty(&self) -> bool {
        self.type_ns.is_none() && self.value_ns.is_none() && self.macro_ns.is_none()
    }

    /// Returns an iterator over the items which are `Some`.
    pub fn present_items(self) -> impl Iterator<Item = T> {
        [self.type_ns, self.value_ns, self.macro_ns].into_iter().flatten()
    }
}

impl CtorKind {
    pub fn from_ast(vdata: &ast::VariantData) -> CtorKind {
        match *vdata {
            ast::VariantData::Tuple(..) => CtorKind::Fn,
            ast::VariantData::Unit(..) => CtorKind::Const,
            ast::VariantData::Struct(..) => CtorKind::Fictive,
        }
    }

    pub fn from_hir(vdata: &hir::VariantData<'_>) -> CtorKind {
        match *vdata {
            hir::VariantData::Tuple(..) => CtorKind::Fn,
            hir::VariantData::Unit(..) => CtorKind::Const,
            hir::VariantData::Struct(..) => CtorKind::Fictive,
        }
    }
}

impl NonMacroAttrKind {
    pub fn descr(self) -> &'static str {
        match self {
            NonMacroAttrKind::Builtin(..) => "built-in attribute",
            NonMacroAttrKind::Tool => "tool attribute",
            NonMacroAttrKind::DeriveHelper | NonMacroAttrKind::DeriveHelperCompat => {
                "derive helper attribute"
            }
            NonMacroAttrKind::Registered => "explicitly registered attribute",
        }
    }

    pub fn article(self) -> &'static str {
        match self {
            NonMacroAttrKind::Registered => "an",
            _ => "a",
        }
    }

    /// Users of some attributes cannot mark them as used, so they are considered always used.
    pub fn is_used(self) -> bool {
        match self {
            NonMacroAttrKind::Tool
            | NonMacroAttrKind::DeriveHelper
            | NonMacroAttrKind::DeriveHelperCompat => true,
            NonMacroAttrKind::Builtin(..) | NonMacroAttrKind::Registered => false,
        }
    }
}

impl<Id> Res<Id> {
    /// Return the `DefId` of this `Def` if it has an ID, else panic.
    pub fn def_id(&self) -> DefId
    where
        Id: Debug,
    {
        self.opt_def_id()
            .unwrap_or_else(|| panic!("attempted .def_id() on invalid res: {:?}", self))
    }

    /// Return `Some(..)` with the `DefId` of this `Res` if it has a ID, else `None`.
    pub fn opt_def_id(&self) -> Option<DefId> {
        match *self {
            Res::Def(_, id) => Some(id),

            Res::Local(..)
            | Res::PrimTy(..)
            | Res::SelfTy(..)
            | Res::SelfCtor(..)
            | Res::ToolMod
            | Res::NonMacroAttr(..)
            | Res::Err => None,
        }
    }

    /// Return the `DefId` of this `Res` if it represents a module.
    pub fn mod_def_id(&self) -> Option<DefId> {
        match *self {
            Res::Def(DefKind::Mod, id) => Some(id),
            _ => None,
        }
    }

    /// A human readable name for the res kind ("function", "module", etc.).
    pub fn descr(&self) -> &'static str {
        match *self {
            Res::Def(kind, def_id) => kind.descr(def_id),
            Res::SelfCtor(..) => "self constructor",
            Res::PrimTy(..) => "builtin type",
            Res::Local(..) => "local variable",
            Res::SelfTy(..) => "self type",
            Res::ToolMod => "tool module",
            Res::NonMacroAttr(attr_kind) => attr_kind.descr(),
            Res::Err => "unresolved item",
        }
    }

    /// Gets an English article for the `Res`.
    pub fn article(&self) -> &'static str {
        match *self {
            Res::Def(kind, _) => kind.article(),
            Res::NonMacroAttr(kind) => kind.article(),
            Res::Err => "an",
            _ => "a",
        }
    }

    pub fn map_id<R>(self, mut map: impl FnMut(Id) -> R) -> Res<R> {
        match self {
            Res::Def(kind, id) => Res::Def(kind, id),
            Res::SelfCtor(id) => Res::SelfCtor(id),
            Res::PrimTy(id) => Res::PrimTy(id),
            Res::Local(id) => Res::Local(map(id)),
            Res::SelfTy(a, b) => Res::SelfTy(a, b),
            Res::ToolMod => Res::ToolMod,
            Res::NonMacroAttr(attr_kind) => Res::NonMacroAttr(attr_kind),
            Res::Err => Res::Err,
        }
    }

    #[track_caller]
    pub fn expect_non_local<OtherId>(self) -> Res<OtherId> {
        self.map_id(|_| panic!("unexpected `Res::Local`"))
    }

    pub fn macro_kind(self) -> Option<MacroKind> {
        match self {
            Res::Def(DefKind::Macro(kind), _) => Some(kind),
            Res::NonMacroAttr(..) => Some(MacroKind::Attr),
            _ => None,
        }
    }

    /// Returns `None` if this is `Res::Err`
    pub fn ns(&self) -> Option<Namespace> {
        match self {
            Res::Def(kind, ..) => kind.ns(),
            Res::PrimTy(..) | Res::SelfTy(..) | Res::ToolMod => Some(Namespace::TypeNS),
            Res::SelfCtor(..) | Res::Local(..) => Some(Namespace::ValueNS),
            Res::NonMacroAttr(..) => Some(Namespace::MacroNS),
            Res::Err => None,
        }
    }

    /// Always returns `true` if `self` is `Res::Err`
    pub fn matches_ns(&self, ns: Namespace) -> bool {
        self.ns().map_or(true, |actual_ns| actual_ns == ns)
    }

    /// Returns whether such a resolved path can occur in a tuple struct/variant pattern
    pub fn expected_in_tuple_struct_pat(&self) -> bool {
        matches!(self, Res::Def(DefKind::Ctor(_, CtorKind::Fn), _) | Res::SelfCtor(..))
    }
}