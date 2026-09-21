import ObserverEquivariance.NormalForm

/-!
# Strict presentation independence (paper `sec:descent`)

Paper labels covered in this file:

* `def:vertical-trivial`: `SendsToIdentity F v` (`∃ h : F x = F y, F v = eqToHom h`, i.e. `F v`
  is an identity arrow, NOT merely an isomorphism) and `VerticallyTrivial p F` (every vertical
  arrow is sent to an identity).  The redundancy of clause (i) ("`F x = F y` whenever
  `p x = p y`") is proved: `VerticallyTrivial.obj_eq` (from any strict section) and
  `VerticallyTrivial.obj_eq_of_minSpec`; the paper's two-clause formulation is equivalent to the
  one-clause predicate (`verticallyTrivial_iff_two_clauses`).
* `thm:descent` (strict factorization criterion), for an ARBITRARY target category `C`:
  `VerticallyTrivial p F ↔ ∃! E : S ⥤ C, p ⋙ E = F`, with the unique factor `B ⋙ F`
  (`strictSection_descent`, `StrictSection.factor_eq`, `StrictSection.factor_unique`), and its
  specializations `MinSpec.descent`, `OEData.descent`.  The bundled form naming the factor,
  `VerticallyTrivial p F ↔ (p ⋙ (B ⋙ F) = F ∧ ∀ E, p ⋙ E = F → E = B ⋙ F)`, is
  `strictSection_descent_factor` (`MinSpec.descent_factor`, `OEData.descent_factor`).
  `StrictSection.descentEquiv` is the object-level bijection `(S ⥤ C) ≃ {F // VerticallyTrivial p F}`.
* The paragraph after `thm:descent` (natural transformations): for `α : p ⋙ E ⟶ p ⋙ E'` there
  is a unique `β : E ⟶ E'` with `whiskerLeft p β = α`, namely `β_s = α_{b_s}` up to the
  `B ⋙ p = 𝟭` casts (`natTrans_descent`, `StrictSection.descendNatTrans_app`), and naturality
  along `η` gives `α_x = α_{b_{p x}}` (`StrictSection.natTrans_app_eq`).  The paper-shaped
  statement for `F = p ⋙ E`, `F' = p ⋙ E'` given as hypotheses and `α : F ⟶ F'` is
  `natTrans_descent_of_eq` (with `MinSpec`/`OEData` versions); this is the precise sense of
  "universal strict passage".
* `prop:weak-descent`: for EVERY `F` (no hypothesis) the natural isomorphism
  `F η : (p ⋙ B) ⋙ F ≅ F` (`weakDescentIso`, `weak_descent`, and `MinSpec`/`OEData` versions).
* `ex:invariant`: `invariantPairFunctor G : Pair G ⥤ SingleObj G`, `(a ⟶ b) ↦ b a⁻¹`, is
  strictly invariant under the right action of the witness datum but, for nontrivial `G`, is
  not vertically trivial and admits no strict factorization through `pWit G`.  The base
  `Pair PUnit` is the terminal category `*` (one object, one arrow; `pairPUnit_functor_eq`).
* The object-function statement at the end of `sec:descent`: `f (x · g) = f x` for all `x, g`
  iff `f = f' ∘ p` for a unique `f'` (`MinSpec.objectFunction_descent`,
  `OEData.objectFunction_descent`).
-/

open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}
variable {C : Type*} [Category C]

/-! ## Vertical triviality (paper `def:vertical-trivial`) -/

/-- `F` sends the arrow `v : x ⟶ y` to an identity arrow: the endpoints have equal images and
    `F v` is the `eqToHom` of that equality (paper `def:vertical-trivial` (ii)).  This is an
    identity in the strict sense, not an arbitrary isomorphism. -/
def SendsToIdentity (F : O ⥤ C) {x y : O} (v : x ⟶ y) : Prop :=
  ∃ h : F.obj x = F.obj y, F.map v = eqToHom h

/-- A functor `F : O ⥤ C` is vertically trivial for `p` if it sends every vertical arrow to an
    identity arrow (paper `def:vertical-trivial`, in the one-clause formulation that the paper
    states as equivalent; clause (i) is derived in `VerticallyTrivial.obj_eq`). -/
def VerticallyTrivial (p : O ⥤ S) (F : O ⥤ C) : Prop :=
  ∀ {x y : O} (v : x ⟶ y), IsVertical p v → SendsToIdentity F v

namespace VerticallyTrivial

/-- Clause (i) of paper `def:vertical-trivial` is redundant: given a strict section, any two
    objects of one fiber are joined by a vertical arrow (`StrictSection.fiberHom`), and an
    identity arrow has equal source and target. -/
theorem obj_eq {F : O ⥤ C} (hF : VerticallyTrivial p F) (σ : StrictSection p) {x y : O}
    (h : p.obj x = p.obj y) : F.obj x = F.obj y :=
  (hF (σ.fiberHom h) (σ.fiberHom_isVertical h)).1

/-- Clause (i) of paper `def:vertical-trivial` is redundant, for a minimal specification: the
    unique vertical arrow `m.verticalHom h` joins any two objects of one fiber. -/
theorem obj_eq_of_minSpec {F : O ⥤ C} (hF : VerticallyTrivial p F) (m : MinSpec G p) {x y : O}
    (h : p.obj x = p.obj y) : F.obj x = F.obj y :=
  (hF (m.verticalHom h) (m.verticalHom_isVertical h)).1

end VerticallyTrivial

/-- The paper's two-clause formulation of `def:vertical-trivial` ((i) equal images over a fiber,
    (ii) vertical arrows go to identities) is equivalent to the one-clause predicate
    `VerticallyTrivial`, i.e. clause (i) follows from (ii) (paper `def:vertical-trivial`). -/
theorem verticallyTrivial_iff_two_clauses (σ : StrictSection p) (F : O ⥤ C) :
    VerticallyTrivial p F ↔
      (∀ {x y : O}, p.obj x = p.obj y → F.obj x = F.obj y) ∧
        (∀ {x y : O} (v : x ⟶ y), IsVertical p v → ∃ h : F.obj x = F.obj y, F.map v = eqToHom h) :=
  ⟨fun hF => ⟨fun h => hF.obj_eq σ h, fun v hv => hF v hv⟩, fun hF => fun v hv => hF.2 v hv⟩

/-- A strictly factored functor `p ⋙ E` is vertically trivial: `E` sends the identity `p v` to
    an identity (paper `thm:descent`, "only if" direction; no section needed). -/
theorem verticallyTrivial_comp (p : O ⥤ S) (E : S ⥤ C) : VerticallyTrivial p (p ⋙ E) := by
  intro x y v hv
  obtain ⟨h, e⟩ := hv
  refine ⟨congrArg E.obj h, ?_⟩
  show E.map (p.map v) = eqToHom (congrArg E.obj h)
  rw [e, eqToHom_map]

/-- Clause (i) for a strictly factored functor, directly (paper `thm:descent`, "only if"). -/
theorem obj_eq_of_factor (E : S ⥤ C) {x y : O} (h : p.obj x = p.obj y) :
    (p ⋙ E).obj x = (p ⋙ E).obj y :=
  congrArg E.obj h

/-! ## The strict factorization criterion (paper `thm:descent`) -/

namespace StrictSection

variable (σ : StrictSection p)

/-- The component `η_x : B(p x) ⟶ x` with syntactically clean endpoints
    (`σ.B.obj (p.obj x)` rather than `(p ⋙ σ.B).obj x`); helper for paper `thm:descent`. -/
def ηHom (x : O) : σ.B.obj (p.obj x) ⟶ x :=
  σ.η.hom.app x

/-- The clean components `η_x` are vertical (paper `cor:section`, used in `thm:descent`). -/
theorem ηHom_isVertical (x : O) : IsVertical p (σ.ηHom x) :=
  σ.η_vertical x

/-- Naturality of `η` in clean endpoints: `B(p f) ≫ η_y = η_x ≫ f`
    (paper `thm:descent`, proof: `f η_x = η_y B(p(f))`). -/
theorem ηHom_naturality {x y : O} (f : x ⟶ y) :
    σ.B.map (p.map f) ≫ σ.ηHom y = σ.ηHom x ≫ f :=
  σ.η.hom.naturality f

/-- A vertically trivial functor sends the components of `η` to identities
    (paper `thm:descent`, proof). -/
theorem map_η_hom_app {F : O ⥤ C} (hF : VerticallyTrivial p F) (x : O) :
    ∃ h : F.obj (σ.B.obj (p.obj x)) = F.obj x, F.map (σ.ηHom x) = eqToHom h :=
  hF (σ.ηHom x) (σ.ηHom_isVertical x)

/-- For a vertically trivial `F`, the functor `B ⋙ F` is a strict factor: `p ⋙ (B ⋙ F) = F`
    on objects AND arrows (paper `thm:descent`, "if" direction, `F = (FB)p`). -/
theorem factor_eq {F : O ⥤ C} (hF : VerticallyTrivial p F) : p ⋙ (σ.B ⋙ F) = F := by
  choose hobj hmap using σ.map_η_hom_app hF
  fapply CategoryTheory.Functor.ext
  · exact hobj
  · intro x y f
    have e : F.map (σ.B.map (p.map f)) ≫ F.map (σ.ηHom y) = F.map (σ.ηHom x) ≫ F.map f := by
      rw [← F.map_comp, ← F.map_comp, σ.ηHom_naturality f]
    have key : F.map (σ.B.map (p.map f)) = eqToHom (hobj x) ≫ F.map f ≫ eqToHom (hobj y).symm := by
      rw [hmap x, hmap y] at e
      rw [← Category.assoc, ← e, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact key

/-- Uniqueness of the strict factor: if `p ⋙ E = F` then `E = B ⋙ F`
    (paper `thm:descent`, "`J = JpB = FB`"). -/
theorem factor_unique {F : O ⥤ C} {E : S ⥤ C} (hE : p ⋙ E = F) : E = σ.B ⋙ F := by
  rw [← hE, ← Functor.assoc, σ.B_comp_p, Functor.id_comp]

end StrictSection

/-- Strict factorization criterion (paper `thm:descent`), for any target category `C` and any
    strict section `σ` of `p`: `F` is vertically trivial iff it factors strictly and uniquely
    through `p`.  The unique factor is `σ.B ⋙ F` (`StrictSection.factor_eq`,
    `StrictSection.factor_unique`). -/
theorem strictSection_descent (σ : StrictSection p) (F : O ⥤ C) :
    VerticallyTrivial p F ↔ ∃! E : S ⥤ C, p ⋙ E = F := by
  constructor
  · intro hF
    exact ⟨σ.B ⋙ F, σ.factor_eq hF, fun E hE => σ.factor_unique hE⟩
  · rintro ⟨E, rfl, -⟩
    exact verticallyTrivial_comp p E

/-- Strict factorization criterion with the factor named (paper `thm:descent`, including "The
    factor `F̄` is unique and is given by `F̄ = FB`"): `F` is vertically trivial iff `B ⋙ F` is
    a strict factor of `F` through `p` and every strict factor equals `B ⋙ F`. -/
theorem strictSection_descent_factor (σ : StrictSection p) (F : O ⥤ C) :
    VerticallyTrivial p F ↔
      (p ⋙ (σ.B ⋙ F) = F ∧ ∀ E : S ⥤ C, p ⋙ E = F → E = σ.B ⋙ F) := by
  constructor
  · intro hF
    exact ⟨σ.factor_eq hF, fun _ hE => σ.factor_unique hE⟩
  · rintro ⟨h, -⟩
    rw [← h]
    exact verticallyTrivial_comp p _

/-- The object part of strict descent (paper `thm:descent`): `E ↦ p ⋙ E` is a bijection from
    functors on the base onto the vertically trivial functors, with inverse `F ↦ B ⋙ F`.  This
    is only a bijection of functors (objects of the functor categories); it says nothing about
    natural transformations.  The paper's "In this precise sense `p` is a universal strict
    passage" refers to the natural-transformation statement after `thm:descent`, which is
    `natTrans_descent` / `natTrans_descent_of_eq` (the morphism part). -/
@[simps]
def StrictSection.descentEquiv (σ : StrictSection p) :
    (S ⥤ C) ≃ {F : O ⥤ C // VerticallyTrivial p F} where
  toFun E := ⟨p ⋙ E, verticallyTrivial_comp p E⟩
  invFun F := σ.B ⋙ F.1
  left_inv _ := (σ.factor_unique rfl).symm
  right_inv F := Subtype.ext (σ.factor_eq F.2)

/-! ## Natural transformations (paragraph after paper `thm:descent`) -/

namespace StrictSection

variable (σ : StrictSection p)

/-- Transport of a component along an object equality (helper for the paragraph after paper
    `thm:descent`). -/
theorem natTrans_app_congr {E E' : S ⥤ C} (β : E ⟶ E') {s s' : S} (h : s = s') :
    β.app s = eqToHom (congrArg E.obj h) ≫ β.app s' ≫ eqToHom (congrArg E'.obj h).symm := by
  subst h; simp

/-- A family `a_x : E(p x) ⟶ E'(p x)` natural along `p` takes the same value (up to the casts)
    at the two ends of an arrow lying over an identity (helper for the paragraph after paper
    `thm:descent`: "naturality along `η_x` gives `α_x = α_{b_{p(x)}}`"). -/
theorem family_app_eq_of_vertical {E E' : S ⥤ C} (a : ∀ x : O, E.obj (p.obj x) ⟶ E'.obj (p.obj x))
    (ha : ∀ {x y : O} (f : x ⟶ y), E.map (p.map f) ≫ a y = a x ≫ E'.map (p.map f))
    {y x : O} (v : y ⟶ x) (h : p.obj y = p.obj x) (hv : p.map v = eqToHom h) :
    a x = eqToHom (congrArg E.obj h).symm ≫ a y ≫ eqToHom (congrArg E'.obj h) := by
  have nat := ha v
  rw [hv, eqToHom_map, eqToHom_map] at nat
  rw [← nat, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- The strict section equation whiskered by `E`: `B ⋙ (p ⋙ E) = E`
    (helper for the paragraph after paper `thm:descent`). -/
theorem B_comp_p_comp (E : S ⥤ C) : σ.B ⋙ (p ⋙ E) = E := by
  rw [← Functor.assoc, σ.B_comp_p, Functor.id_comp]

/-- The descended transformation `β̄ : E ⟶ E'` of `α : p ⋙ E ⟶ p ⋙ E'`, `β̄_s = α_{B s}` up to
    the casts from `B ⋙ p = 𝟭` (paragraph after paper `thm:descent`). -/
def descendNatTrans {E E' : S ⥤ C} (α : p ⋙ E ⟶ p ⋙ E') : E ⟶ E' :=
  eqToHom (σ.B_comp_p_comp E).symm ≫ Functor.whiskerLeft σ.B α ≫ eqToHom (σ.B_comp_p_comp E')

/-- `β̄_s = α_{B s}` up to the `p(B s) = s` casts (paragraph after paper `thm:descent`,
    `ᾱ_s = α_{b_s}`). -/
theorem descendNatTrans_app {E E' : S ⥤ C} (α : p ⋙ E ⟶ p ⋙ E') (s : S) :
    (σ.descendNatTrans α).app s
      = eqToHom (congrArg E.obj (σ.p_obj_B s)).symm ≫ α.app (σ.B.obj s)
        ≫ eqToHom (congrArg E'.obj (σ.p_obj_B s)) := by
  simp [descendNatTrans, eqToHom_app]
  rfl

/-- Naturality along `η_x` gives `α_x = α_{B(p x)}` up to the casts, for any transformation
    between strictly factored functors (paragraph after paper `thm:descent`). -/
theorem natTrans_app_eq {E E' : S ⥤ C} (α : p ⋙ E ⟶ p ⋙ E') (x : O) :
    α.app x = eqToHom (congrArg E.obj (σ.p_obj_B (p.obj x))).symm
      ≫ α.app (σ.B.obj (p.obj x)) ≫ eqToHom (congrArg E'.obj (σ.p_obj_B (p.obj x))) := by
  obtain ⟨h, e⟩ := σ.ηHom_isVertical x
  exact family_app_eq_of_vertical (fun x => α.app x) (fun f => α.naturality f) (σ.ηHom x) h e

/-- The whiskering of the descended transformation recovers `α` (paragraph after paper
    `thm:descent`, `α = ᾱ p`). -/
theorem whiskerLeft_descendNatTrans {E E' : S ⥤ C} (α : p ⋙ E ⟶ p ⋙ E') :
    Functor.whiskerLeft p (σ.descendNatTrans α) = α := by
  ext x
  exact (σ.descendNatTrans_app α (p.obj x)).trans (σ.natTrans_app_eq α x).symm

end StrictSection

/-- Natural transformations between strictly factored functors descend uniquely
    (paragraph after paper `thm:descent`): for `α : p ⋙ E ⟶ p ⋙ E'` there is a unique
    `β : E ⟶ E'` with `whiskerLeft p β = α`, namely `σ.descendNatTrans α`
    (`β_s = α_{b_s}` up to casts, `StrictSection.descendNatTrans_app`). -/
theorem natTrans_descent (σ : StrictSection p) {E E' : S ⥤ C} (α : p ⋙ E ⟶ p ⋙ E') :
    ∃! β : E ⟶ E', Functor.whiskerLeft p β = α := by
  refine ⟨σ.descendNatTrans α, σ.whiskerLeft_descendNatTrans α, fun β hβ => ?_⟩
  ext s
  rw [σ.descendNatTrans_app, ← hβ]
  exact StrictSection.natTrans_app_congr β (σ.p_obj_B s).symm

/-- Natural transformations descend uniquely, in the paper's form (paragraph after paper
    `thm:descent`: "If `F = F̄p`, `F' = F̄'p`, and `α : F ⇒ F'`, ... there is a unique natural
    transformation `ᾱ : F̄ ⇒ F̄'` with `α = ᾱp`"): for strictly factored functors given by
    hypotheses `hE : p ⋙ E = F`, `hE' : p ⋙ E' = F'` and any `α : F ⟶ F'`, there is a unique
    `β : E ⟶ E'` whose whiskering by `p` is `α` up to the `eqToHom` casts along `hE`, `hE'`. -/
theorem natTrans_descent_of_eq (σ : StrictSection p) {F F' : O ⥤ C} {E E' : S ⥤ C}
    (hE : p ⋙ E = F) (hE' : p ⋙ E' = F') (α : F ⟶ F') :
    ∃! β : E ⟶ E', Functor.whiskerLeft p β = eqToHom hE ≫ α ≫ eqToHom hE'.symm := by
  subst hE hE'
  simpa using natTrans_descent σ α

/-! ## Weak factorization (paper `prop:weak-descent`) -/

namespace StrictSection

variable (σ : StrictSection p)

/-- Naturality of `F η` in clean endpoints (helper for paper `prop:weak-descent`). -/
theorem map_η_naturality (F : O ⥤ C) {x y : O} (f : x ⟶ y) :
    F.map (σ.B.map (p.map f)) ≫ F.map (σ.η.hom.app y) = F.map (σ.η.hom.app x) ≫ F.map f := by
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg F.map (σ.η.hom.naturality f)

end StrictSection

/-- Weak factorization is automatic (paper `prop:weak-descent`): for EVERY functor `F : O ⥤ C`
    (no hypothesis on `F`), applying `F` to `η` gives a natural isomorphism
    `F η : (p ⋙ B) ⋙ F ≅ F`. -/
noncomputable def weakDescentIso (σ : StrictSection p) (F : O ⥤ C) : (p ⋙ σ.B) ⋙ F ≅ F :=
  NatIso.ofComponents (fun x => F.mapIso (σ.η.app x)) (fun f => σ.map_η_naturality F f)

/-- The components of the weak factorization are `F(η_x)` (paper `prop:weak-descent`). -/
@[simp] theorem weakDescentIso_hom_app (σ : StrictSection p) (F : O ⥤ C) (x : O) :
    (weakDescentIso σ F).hom.app x = F.map (σ.η.hom.app x) := rfl

/-- Every functor factors through `p` up to natural isomorphism, with factor `B ⋙ F`
    (paper `prop:weak-descent`; contrast `strictSection_descent`). -/
theorem weak_descent (σ : StrictSection p) (F : O ⥤ C) : ∃ E : S ⥤ C, Nonempty (p ⋙ E ≅ F) :=
  ⟨σ.B ⋙ F, ⟨weakDescentIso σ F⟩⟩

/-! ## Specializations to minimal specifications and normalized data -/

namespace MinSpec

variable (m : MinSpec G p)

/-- Strict factorization criterion for a minimal specification (paper `thm:descent`): the unique
    factor is `m.sectionFunctor ⋙ F`. -/
theorem descent (m : MinSpec G p) (F : O ⥤ C) :
    VerticallyTrivial p F ↔ ∃! E : S ⥤ C, p ⋙ E = F :=
  strictSection_descent m.strictSection F

/-- Strict factorization criterion with the factor named, for a minimal specification (paper
    `thm:descent`, "the factor is unique and is given by `F̄ = FB`", `B = m.sectionFunctor`). -/
theorem descent_factor (m : MinSpec G p) (F : O ⥤ C) :
    VerticallyTrivial p F ↔
      (p ⋙ (m.sectionFunctor ⋙ F) = F ∧ ∀ E : S ⥤ C, p ⋙ E = F → E = m.sectionFunctor ⋙ F) :=
  strictSection_descent_factor m.strictSection F

/-- The strict factor of a vertically trivial functor is `B ⋙ F`, `B(s) = b_s`
    (paper `thm:descent`). -/
theorem factor_eq {F : O ⥤ C} (hF : VerticallyTrivial p F) : p ⋙ (m.sectionFunctor ⋙ F) = F :=
  m.strictSection.factor_eq hF

/-- Uniqueness of the strict factor for a minimal specification (paper `thm:descent`). -/
theorem factor_unique {F : O ⥤ C} {E : S ⥤ C} (hE : p ⋙ E = F) : E = m.sectionFunctor ⋙ F :=
  m.strictSection.factor_unique hE

/-- Natural transformations between strictly factored functors descend uniquely, for a minimal
    specification (paragraph after paper `thm:descent`). -/
theorem natTrans_descent (m : MinSpec G p) {E E' : S ⥤ C} (α : p ⋙ E ⟶ p ⋙ E') :
    ∃! β : E ⟶ E', Functor.whiskerLeft p β = α :=
  _root_.natTrans_descent m.strictSection α

/-- Natural transformations descend uniquely in the paper's form (`F = p ⋙ E`, `F' = p ⋙ E'`
    given as hypotheses), for a minimal specification (paragraph after paper `thm:descent`). -/
theorem natTrans_descent_of_eq (m : MinSpec G p) {F F' : O ⥤ C} {E E' : S ⥤ C}
    (hE : p ⋙ E = F) (hE' : p ⋙ E' = F') (α : F ⟶ F') :
    ∃! β : E ⟶ E', Functor.whiskerLeft p β = eqToHom hE ≫ α ≫ eqToHom hE'.symm :=
  _root_.natTrans_descent_of_eq m.strictSection hE hE' α

/-- The descended transformation has components `ᾱ_s = α_{b_s}` up to the casts
    `p(b_s) = s` (paragraph after paper `thm:descent`). -/
theorem descendNatTrans_app {E E' : S ⥤ C} (α : p ⋙ E ⟶ p ⋙ E') (s : S) :
    (m.strictSection.descendNatTrans α).app s
      = eqToHom (congrArg E.obj (m.p_base s)).symm ≫ α.app (m.base s)
        ≫ eqToHom (congrArg E'.obj (m.p_base s)) :=
  m.strictSection.descendNatTrans_app α s

/-- Weak factorization for a minimal specification (paper `prop:weak-descent`), no hypothesis
    on `F`. -/
noncomputable def weakDescentIso (F : O ⥤ C) : (p ⋙ m.sectionFunctor) ⋙ F ≅ F :=
  _root_.weakDescentIso m.strictSection F

/-- The components are `F` applied to the unique vertical lifts `b_{p x} ⟶ x`
    (paper `prop:weak-descent`). -/
@[simp] theorem weakDescentIso_hom_app (F : O ⥤ C) (x : O) :
    (m.weakDescentIso F).hom.app x = F.map (m.liftOver (𝟙 (p.obj x)) (m.p_base (p.obj x)) rfl) :=
  rfl

/-- Object functions (end of paper `sec:descent`): a function `f : Ob O → X` is invariant under
    the right action iff it factors as `f = f' ∘ p` for a UNIQUE `f' : Ob S → X`. -/
theorem objectFunction_descent {X : Sort*} (f : O → X) :
    (∀ x g, f (m.act x g) = f x) ↔ ∃! f' : S → X, f = f' ∘ p.obj := by
  constructor
  · intro hf
    refine ⟨fun s => f (m.base s), ?_, ?_⟩
    · funext x
      simp only [Function.comp_apply]
      conv_lhs => rw [← m.base_coord x]
      exact hf _ _
    · intro f' hf'
      funext s
      simp only [hf', Function.comp_apply, m.p_base]
  · rintro ⟨f', rfl, -⟩ x g
    simp only [Function.comp_apply, m.p_act]

end MinSpec

namespace OEData

variable (d : OEData G p)

/-- Strict factorization criterion for normalized data (paper `thm:descent`): the unique factor
    is `d.sectionFunctor ⋙ F`, `B(s) = b_s` definitionally. -/
theorem descent (d : OEData G p) (F : O ⥤ C) :
    VerticallyTrivial p F ↔ ∃! E : S ⥤ C, p ⋙ E = F :=
  strictSection_descent d.strictSection F

/-- Strict factorization criterion with the factor named, for normalized data (paper
    `thm:descent`, "the factor is unique and is given by `F̄ = FB`", `B = d.sectionFunctor`,
    `B(s) = b_s` definitionally). -/
theorem descent_factor (d : OEData G p) (F : O ⥤ C) :
    VerticallyTrivial p F ↔
      (p ⋙ (d.sectionFunctor ⋙ F) = F ∧ ∀ E : S ⥤ C, p ⋙ E = F → E = d.sectionFunctor ⋙ F) :=
  strictSection_descent_factor d.strictSection F

/-- The strict factor of a vertically trivial functor is `B ⋙ F` (paper `thm:descent`). -/
theorem factor_eq {F : O ⥤ C} (hF : VerticallyTrivial p F) : p ⋙ (d.sectionFunctor ⋙ F) = F :=
  d.strictSection.factor_eq hF

/-- Uniqueness of the strict factor for normalized data (paper `thm:descent`). -/
theorem factor_unique {F : O ⥤ C} {E : S ⥤ C} (hE : p ⋙ E = F) : E = d.sectionFunctor ⋙ F :=
  d.strictSection.factor_unique hE

/-- Natural transformations between strictly factored functors descend uniquely, for
    normalized data (paragraph after paper `thm:descent`). -/
theorem natTrans_descent (d : OEData G p) {E E' : S ⥤ C} (α : p ⋙ E ⟶ p ⋙ E') :
    ∃! β : E ⟶ E', Functor.whiskerLeft p β = α :=
  _root_.natTrans_descent d.strictSection α

/-- Natural transformations descend uniquely in the paper's form (`F = p ⋙ E`, `F' = p ⋙ E'`
    given as hypotheses), for normalized data (paragraph after paper `thm:descent`). -/
theorem natTrans_descent_of_eq (d : OEData G p) {F F' : O ⥤ C} {E E' : S ⥤ C}
    (hE : p ⋙ E = F) (hE' : p ⋙ E' = F') (α : F ⟶ F') :
    ∃! β : E ⟶ E', Functor.whiskerLeft p β = eqToHom hE ≫ α ≫ eqToHom hE'.symm :=
  _root_.natTrans_descent_of_eq d.strictSection hE hE' α

/-- The descended transformation has components `ᾱ_s = α_{b_s}` up to the casts
    `p(b_s) = s` (paragraph after paper `thm:descent`). -/
theorem descendNatTrans_app {E E' : S ⥤ C} (α : p ⋙ E ⟶ p ⋙ E') (s : S) :
    (d.strictSection.descendNatTrans α).app s
      = eqToHom (congrArg E.obj (d.p_base s)).symm ≫ α.app (d.base s)
        ≫ eqToHom (congrArg E'.obj (d.p_base s)) :=
  d.strictSection.descendNatTrans_app α s

/-- Weak factorization for normalized data (paper `prop:weak-descent`), no hypothesis on `F`. -/
noncomputable def weakDescentIso (F : O ⥤ C) : (p ⋙ d.sectionFunctor) ⋙ F ≅ F :=
  _root_.weakDescentIso d.strictSection F

/-- The components are `F(ℓ_{g_x, b_{p x}})` followed by the (N2) target identification
    (paper `prop:weak-descent`). -/
@[simp] theorem weakDescentIso_hom_app (F : O ⥤ C) (x : O) :
    (d.weakDescentIso F).hom.app x
      = F.map (d.ltrans (d.coord x) (d.base (p.obj x)) ≫ eqToHom (d.sectionEta_target_eq x)) :=
  rfl

/-- Object functions for normalized data (end of paper `sec:descent`): `f (x · g) = f x` for all
    `x, g` iff `f = f' ∘ p` for a UNIQUE `f'`. -/
theorem objectFunction_descent {X : Sort*} (f : O → X) :
    (∀ x g, f (d.act x g) = f x) ↔ ∃! f' : S → X, f = f' ∘ p.obj := by
  constructor
  · intro hf
    refine ⟨fun s => f (d.base s), ?_, ?_⟩
    · funext x
      simp only [Function.comp_apply]
      conv_lhs => rw [← d.base_coord x]
      exact hf _ _
    · intro f' hf'
      funext s
      simp only [hf', Function.comp_apply, d.p_base]
  · rintro ⟨f', rfl, -⟩ x g
    simp only [Function.comp_apply, d.p_act]

end OEData

/-! ## Invariance without strict factorization (paper `ex:invariant`) -/

/-- `Pair PUnit` has exactly one object (paper `ex:invariant`, the terminal category `*`). -/
theorem pairPUnit_obj_eq (a b : Pair PUnit) : a = b := by
  obtain ⟨⟨⟩⟩ := a
  obtain ⟨⟨⟩⟩ := b
  rfl

/-- `Pair PUnit` is terminal (paper `ex:invariant`, the terminal category `*`): any two functors
    from any category `D` into `Pair PUnit` are equal, on objects and arrows (it has one object,
    and each hom-set is a singleton). -/
theorem pairPUnit_functor_eq {D : Type*} [Category D] (F F' : D ⥤ Pair PUnit) : F = F' :=
  CategoryTheory.Functor.ext (fun _ => pairPUnit_obj_eq _ _) (fun _ _ _ => Subsingleton.elim _ _)

/-- The functor `F : Pair G ⥤ BG`, every object to the single object and `F(a ⟶ b) = b a⁻¹`
    (paper `ex:invariant`).  In `SingleObj G`, `f ≫ g = g * f`, so functoriality is
    `(c b⁻¹)(b a⁻¹) = c a⁻¹`. -/
def invariantPairFunctor (G : Type*) [Group G] : Pair G ⥤ SingleObj G where
  obj _ := SingleObj.star G
  map {a b} _ := (b.pt * a.pt⁻¹ : G)
  map_id a := by
    rw [SingleObj.id_as_one]; exact mul_inv_cancel a.pt
  map_comp {a b c} _ _ := by
    rw [SingleObj.comp_as_mul]
    show c.pt * a.pt⁻¹ = (c.pt * b.pt⁻¹) * (b.pt * a.pt⁻¹)
    group

/-- `F(a ⟶ b) = b a⁻¹` (paper `ex:invariant`). -/
@[simp] theorem invariantPairFunctor_map (G : Type*) [Group G] {a b : Pair G} (f : a ⟶ b) :
    (invariantPairFunctor G).map f = (b.pt * a.pt⁻¹ : G) := rfl

/-- `F` is strictly invariant under the right action: `F R_h = F`, since
    `(b h)(a h)⁻¹ = b a⁻¹` (paper `ex:invariant`). -/
theorem invariantPairFunctor_invariant (G : Type*) [Group G] (h : G) :
    (witness G).actFunctor h ⋙ invariantPairFunctor G = invariantPairFunctor G := by
  fapply CategoryTheory.Functor.ext
  · intro _; rfl
  · intro a b f
    show _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    show (b.pt * h) * (a.pt * h)⁻¹ = b.pt * a.pt⁻¹
    group

/-- For nontrivial `G`, `F` is NOT vertically trivial: the vertical arrow `1 ⟶ g` with `g ≠ 1`
    is sent to `g ≠ 1` (paper `ex:invariant`). -/
theorem invariantPairFunctor_not_verticallyTrivial (G : Type*) [Group G] [Nontrivial G] :
    ¬ VerticallyTrivial (pWit G) (invariantPairFunctor G) := by
  intro hF
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  let v : Pair.mk (1 : G) ⟶ Pair.mk g := PUnit.unit
  have hv : IsVertical (pWit G) v := ⟨rfl, Subsingleton.elim _ _⟩
  obtain ⟨h, e⟩ := hF v hv
  have e' : g * (1 : G)⁻¹ = 1 := e.trans (eqToHom_refl _ h)
  exact hg (by simpa using e')

/-- `G`-invariance without strict factorization (paper `ex:invariant`): for nontrivial `G`, the
    strictly invariant functor `invariantPairFunctor G` admits no strict factorization through
    the projection `pWit G : Pair G ⥤ Pair PUnit` (by `thm:descent`).  The base `Pair PUnit` is
    the paper's terminal category `*`: it has exactly one object and exactly one arrow (the
    identity), and every functor into it is unique (`pairPUnit_functor_eq`), so `pWit G` is the
    unique functor `Pair G ⥤ *`. -/
theorem invariantPairFunctor_no_factor (G : Type*) [Group G] [Nontrivial G] :
    ¬ ∃ E : Pair PUnit ⥤ SingleObj G, pWit G ⋙ E = invariantPairFunctor G := by
  rintro ⟨E, hE⟩
  exact invariantPairFunctor_not_verticallyTrivial G (hE ▸ verticallyTrivial_comp (pWit G) E)
