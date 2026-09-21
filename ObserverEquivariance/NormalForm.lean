import ObserverEquivariance.MinSpec

/-!
# Strict product normal form and the chosen section
  (paper `thm:normalform`, `cor:section`, `rem:groupoid`; vertical arrows from `sec:data`)

Paper labels covered in this file:

* vertical arrows (paper `sec:data`, the unlabeled paragraph right after `def:data`: "an arrow
  `v : x → y` is vertical if `p(x) = p(y)` and `p(v) = id`"): the predicate `IsVertical p v`
  (`∃ h : p x = p y, p v = eqToHom h`) and its closure properties.  The notion is used in (N5)
  and in `def:vertical-trivial`, but it is defined in neither.
* `thm:normalform` (strict product normal form): for a minimal specification
  `m : MinSpec G p` the functors `m.normalFormTo : O ⥤ S × Pair G` (`N`) and
  `m.normalFormFrom : S × Pair G ⥤ O` (`M`, `M(s,g) = b_s · g`, arrows = unique lifts of the
  base component) are STRICT inverse functors: `N ⋙ M = 𝟭 O` and `M ⋙ N = 𝟭 (S × Pair G)`
  as equalities of functors (objects and morphisms), not natural isomorphisms.  Both lie over
  `S` strictly ("an isomorphism of categories over `S`"): `N ⋙ Prod.fst = p`
  (`normalFormTo_comp_fst`) and `M ⋙ p = Prod.fst` (`normalFormFrom_comp_fst`).  Both
  intertwine the right `G`-actions strictly.  The `OEData` versions (`normalFormTo d` from
  `Core`, `normalFormFrom d`) are derived from the `MinSpec` ones through `OEData.toMinSpec`,
  plus the arrow-level reindexing statement `normalFormTo_map_chi`.
* `cor:section`: the structure `StrictSection p` (a functor `B` with the STRICT section
  equation `B ⋙ p = 𝟭 S` and a natural isomorphism `η : p ⋙ B ≅ 𝟭 O` with vertical
  components, the other composite only up to isomorphism), the constructions
  `MinSpec.strictSection` and `OEData.strictSection` (`B.obj s = b_s` definitionally for
  `OEData`, `B.map u` = the unique lift, equal to `χ_{u,b_t}` after the (N4) endpoint rewrite,
  `η_x = ℓ_{g_x, b_{p x}}`), and the consequence that `p` is an equivalence.  We do NOT claim
  that `p` is a strict isomorphism: for nontrivial `G` and nonempty `S` no functor `B'`
  satisfies `p ⋙ B' = 𝟭 O` (`MinSpec.no_strict_retraction`).
* `rem:groupoid`: the `MinSpec` versions of both groupoid specializations (the `OEData`
  versions are `OEData.base_hom_isIso` and `OEData.hom_isIso_of_base_isIso` in `Core`).

Dependencies are separable: everything in the `MinSpec` namespace uses only `MinSpec`, so the
normal form and the section are available directly from the minimal specification.
-/

open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}

/-! ## Vertical arrows (paper `sec:data`, paragraph after `def:data`) -/

/-- An arrow `v : x ⟶ y` of `O` is vertical for `p` if it lies over an identity: its
    endpoints have the same projection and `p v` is the identity of that object, expressed as
    an `eqToHom` (paper `sec:data`, the unlabeled paragraph right after `def:data`; the notion
    is used in `def:data` (N5) and in `def:vertical-trivial`). -/
def IsVertical (p : O ⥤ S) {x y : O} (v : x ⟶ y) : Prop :=
  ∃ h : p.obj x = p.obj y, p.map v = eqToHom h

namespace IsVertical

/-- Identities are vertical (paper `sec:data`, paragraph after `def:data`). -/
theorem id (p : O ⥤ S) (x : O) : IsVertical p (𝟙 x) :=
  ⟨rfl, by simp⟩

/-- `eqToHom` arrows are vertical (paper `sec:data`, paragraph after `def:data`). -/
theorem eqToHom (p : O ⥤ S) {x y : O} (h : x = y) : IsVertical p (CategoryTheory.eqToHom h) :=
  ⟨congrArg p.obj h, eqToHom_map p h⟩

/-- Vertical arrows compose (paper `sec:data`, paragraph after `def:data`). -/
theorem comp {x y z : O} {v : x ⟶ y} {w : y ⟶ z} (hv : IsVertical p v) (hw : IsVertical p w) :
    IsVertical p (v ≫ w) := by
  obtain ⟨h₁, e₁⟩ := hv
  obtain ⟨h₂, e₂⟩ := hw
  exact ⟨h₁.trans h₂, by rw [p.map_comp, e₁, e₂, eqToHom_trans]⟩

/-- The inverse of a vertical isomorphism is vertical (vertical arrows: paper `sec:data`,
    paragraph after `def:data`; used for the vertical isomorphisms of `def:data` (N5)). -/
theorem inv {x y : O} {v : x ⟶ y} [IsIso v] (hv : IsVertical p v) :
    IsVertical p (CategoryTheory.inv v) := by
  obtain ⟨h, e⟩ := hv
  refine ⟨h.symm, ?_⟩
  rw [p.map_inv]
  exact IsIso.inv_eq_of_hom_inv_id (by rw [e, eqToHom_trans, eqToHom_refl])

end IsVertical

/-- The chosen vertical translations `ℓ_{g,x}` of normalized data are vertical
    (paper `def:data` (N5)). -/
theorem OEData.ltrans_isVertical (d : OEData G p) (g : G) (x : O) :
    IsVertical p (d.ltrans g x) :=
  ⟨_, d.p_ltrans g x⟩

/-! ## Local helpers about arrows of `S × Pair G` -/

namespace NormalForm

omit [Group G] in
/-- Arrows of `S × Pair G` are determined by their base component (helper for paper
    `thm:normalform`: the pair-groupoid hom-sets are singletons). -/
theorem prodPairHom_ext {X Y : S × Pair G} {f f' : X ⟶ Y} (h : f.1 = f'.1) : f = f' :=
  Prod.ext h (Subsingleton.elim _ _)

omit [Group G] in
/-- The base component of an `eqToHom` in `S × Pair G` (helper for paper `thm:normalform`). -/
theorem eqToHom_prod_fst {X Y : S × Pair G} (h : X = Y) :
    (eqToHom h).1 = eqToHom (congrArg Prod.fst h) := by
  subst h; rfl

end NormalForm

open NormalForm

/-! ## The strict normal form for a minimal specification (paper `thm:normalform`) -/

namespace MinSpec

variable (m : MinSpec G p)

/-- The comparison functor `N : O ⥤ S × Pair G`, `N(x) = (p(x), g_x)`, `N(f) = (p(f), *)`
    (paper `thm:normalform`). -/
def normalFormTo : O ⥤ S × Pair G where
  obj x := (p.obj x, ⟨m.coord x⟩)
  map f := (p.map f, ⟨⟩)
  map_id x := Prod.ext (p.map_id x) (Subsingleton.elim _ _)
  map_comp f g := Prod.ext (p.map_comp f g) (Subsingleton.elim _ _)

/-- (paper `thm:normalform`) -/
@[simp] theorem normalFormTo_obj (x : O) : m.normalFormTo.obj x = (p.obj x, ⟨m.coord x⟩) := rfl

/-- (paper `thm:normalform`) -/
@[simp] theorem normalFormTo_map {x y : O} (f : x ⟶ y) :
    m.normalFormTo.map f = (p.map f, ⟨⟩) := rfl

/-- The first projection composed with `N` is `p` strictly (paper `thm:normalform`). -/
theorem normalFormTo_comp_fst : m.normalFormTo ⋙ CategoryTheory.Prod.fst S (Pair G) = p := rfl

/-- `N` sends the basepoint `b_s` to `(s, 1)` (paper `thm:normalform`). -/
theorem normalFormTo_obj_base (s : S) : m.normalFormTo.obj (m.base s) = (s, ⟨1⟩) := by
  simp

/-- `N` intertwines the action on objects: `N(x · g) = (p(x), g_x g)` (paper `thm:normalform`). -/
theorem normalFormTo_obj_act (x : O) (g : G) :
    m.normalFormTo.obj (m.act x g) = (p.obj x, ⟨m.coord x * g⟩) := by
  simp

/-- The inverse functor `M : S × Pair G ⥤ O`, `M(s,g) = e⁻¹(s,g) = b_s · g`
    (`normalFormFrom_obj`); on arrows `M(u,*)` is the unique arrow `b_s · g ⟶ b_t · h`
    projecting to `u` (paper `thm:normalform`). -/
noncomputable def normalFormFrom : S × Pair G ⥤ O where
  obj X := m.e.symm (X.1, X.2.pt)
  map {X Y} f := m.liftOver f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt)
  map_id _ := m.liftOver_id _
  map_comp f g := (m.liftOver_comp f.1 g.1 _ _ _).symm

/-- (paper `thm:normalform`) -/
@[simp] theorem normalFormFrom_obj_eq_e_symm (X : S × Pair G) :
    m.normalFormFrom.obj X = m.e.symm (X.1, X.2.pt) := rfl

/-- `M(s,g) = b_s · g` (paper `thm:normalform`). -/
theorem normalFormFrom_obj (s : S) (g : G) :
    m.normalFormFrom.obj (s, ⟨g⟩) = m.act (m.base s) g :=
  m.e_symm_eq s g

/-- `M` lies over the first projection on objects (paper `thm:normalform`). -/
theorem p_normalFormFrom_obj (X : S × Pair G) : p.obj (m.normalFormFrom.obj X) = X.1 :=
  m.p_e_symm X.1 X.2.pt

/-- The morphism part of `M` is the unique lift of the base component (paper
    `thm:normalform`). -/
@[simp] theorem normalFormFrom_map {X Y : S × Pair G} (f : X ⟶ Y) :
    m.normalFormFrom.map f = m.liftOver f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt) :=
  rfl

/-- Projection of `M` on arrows (paper `thm:normalform`). -/
theorem p_map_normalFormFrom_map {X Y : S × Pair G} (f : X ⟶ Y) :
    p.map (m.normalFormFrom.map f)
      = eqToHom (m.p_e_symm X.1 X.2.pt) ≫ f.1 ≫ eqToHom (m.p_e_symm Y.1 Y.2.pt).symm :=
  m.p_map_liftOver f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt)

/-- Uniqueness: any arrow `M(X) ⟶ M(Y)` projecting to the base component of `f` equals
    `M(f)` (paper `thm:normalform`). -/
theorem normalFormFrom_map_unique {X Y : S × Pair G} (f : X ⟶ Y)
    (φ : m.normalFormFrom.obj X ⟶ m.normalFormFrom.obj Y)
    (hφ : p.map φ
      = eqToHom (m.p_e_symm X.1 X.2.pt) ≫ f.1 ≫ eqToHom (m.p_e_symm Y.1 Y.2.pt).symm) :
    φ = m.normalFormFrom.map f :=
  (m.eq_liftOver_iff f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt) φ).2 hφ

/-- Strict inverse, first half: `N ⋙ M = 𝟭 O` as functors, i.e. on objects AND arrows
    (paper `thm:normalform`, `MN = id_O`). -/
theorem normalFormTo_comp_normalFormFrom : m.normalFormTo ⋙ m.normalFormFrom = 𝟭 O := by
  fapply CategoryTheory.Functor.ext
  · intro x; exact m.e_symm_p_coord x
  · intro x y f
    have key : m.liftOver (p.map f) (m.p_e_symm (p.obj x) (m.coord x))
          (m.p_e_symm (p.obj y) (m.coord y))
        = eqToHom (m.e_symm_p_coord x) ≫ f ≫ eqToHom (m.e_symm_p_coord y).symm := by
      apply m.hom_ext
      simp [eqToHom_map]
    exact key

/-- Strict inverse, second half: `M ⋙ N = 𝟭 (S × Pair G)` as functors, i.e. on objects AND
    arrows (paper `thm:normalform`, `NM = id`). -/
theorem normalFormFrom_comp_normalFormTo :
    m.normalFormFrom ⋙ m.normalFormTo = 𝟭 (S × Pair G) := by
  have hobj : ∀ X : S × Pair G,
      ((p.obj (m.e.symm (X.1, X.2.pt)), ⟨m.coord (m.e.symm (X.1, X.2.pt))⟩) : S × Pair G) = X := by
    rintro ⟨s, ⟨g⟩⟩; simp
  fapply CategoryTheory.Functor.ext
  · exact hobj
  · intro X Y f
    have key : ((p.map (m.liftOver f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt)), ⟨⟩) :
          ((p.obj (m.e.symm (X.1, X.2.pt)), ⟨m.coord (m.e.symm (X.1, X.2.pt))⟩) : S × Pair G) ⟶
          (p.obj (m.e.symm (Y.1, Y.2.pt)), ⟨m.coord (m.e.symm (Y.1, Y.2.pt))⟩))
        = eqToHom (hobj X) ≫ f ≫ eqToHom (hobj Y).symm := by
      apply prodPairHom_ext
      simp only [prod_comp_fst, eqToHom_prod_fst, p_map_liftOver]
    exact key

/-- `N` intertwines the right `G`-actions strictly:
    `R_g ⋙ N = N ⋙ ((s,a) ↦ (s, a g))` (paper `thm:normalform`). -/
theorem normalForm_equivariant (g : G) :
    m.actFunctor g ⋙ m.normalFormTo = m.normalFormTo ⋙ normalFormProductAction g := by
  have hobj : ∀ x : O,
      ((p.obj (m.act x g), ⟨m.coord (m.act x g)⟩) : S × Pair G) = (p.obj x, ⟨m.coord x * g⟩) :=
    fun x => by simp
  fapply CategoryTheory.Functor.ext
  · exact hobj
  · intro x y f
    have key : ((p.map (m.liftOver (p.map f) (m.p_act x g) (m.p_act y g)), ⟨⟩) :
          ((p.obj (m.act x g), ⟨m.coord (m.act x g)⟩) : S × Pair G) ⟶
            (p.obj (m.act y g), ⟨m.coord (m.act y g)⟩))
        = eqToHom (hobj x) ≫
          ((p.map f, ⟨⟩) : ((p.obj x, ⟨m.coord x * g⟩) : S × Pair G) ⟶
            (p.obj y, ⟨m.coord y * g⟩)) ≫ eqToHom (hobj y).symm := by
      apply prodPairHom_ext
      simp only [prod_comp_fst, eqToHom_prod_fst, p_map_liftOver]
    exact key

/-- `M` intertwines the right `G`-actions strictly:
    `((s,a) ↦ (s, a g)) ⋙ M = M ⋙ R_g` (paper `thm:normalform`). -/
theorem normalFormFrom_equivariant (g : G) :
    normalFormProductAction g ⋙ m.normalFormFrom = m.normalFormFrom ⋙ m.actFunctor g := by
  fapply CategoryTheory.Functor.ext
  · intro X; exact (m.act_e_symm X.1 X.2.pt g).symm
  · intro X Y f
    have key : m.liftOver f.1 (m.p_e_symm X.1 (X.2.pt * g)) (m.p_e_symm Y.1 (Y.2.pt * g))
        = eqToHom (m.act_e_symm X.1 X.2.pt g).symm
          ≫ m.liftOver (p.map (m.liftOver f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt)))
              (m.p_act _ g) (m.p_act _ g)
          ≫ eqToHom (m.act_e_symm Y.1 Y.2.pt g) := by
      apply m.hom_ext
      simp
    exact key

/-- The strict isomorphism of categories `N`, `M` packaged as an equivalence whose unit and
    counit are `eqToIso`s of the strict functor equalities (paper `thm:normalform`). -/
noncomputable def normalFormEquivalence : O ≌ S × Pair G :=
  CategoryTheory.Equivalence.mk m.normalFormTo m.normalFormFrom
    (eqToIso m.normalFormTo_comp_normalFormFrom.symm) (eqToIso m.normalFormFrom_comp_normalFormTo)

/-- (paper `thm:normalform`) -/
@[simp] theorem normalFormEquivalence_functor : m.normalFormEquivalence.functor = m.normalFormTo :=
  rfl

/-- (paper `thm:normalform`) -/
@[simp] theorem normalFormEquivalence_inverse :
    m.normalFormEquivalence.inverse = m.normalFormFrom := rfl

/-- `M` lies over `S` strictly: `M ⋙ p = Prod.fst` as functors, on objects AND arrows (paper
    `thm:normalform`, "an isomorphism of categories over `S`"; the other half,
    `N ⋙ Prod.fst = p`, is `normalFormTo_comp_fst`). -/
theorem normalFormFrom_comp_fst :
    m.normalFormFrom ⋙ p = CategoryTheory.Prod.fst S (Pair G) :=
  calc m.normalFormFrom ⋙ p
      = m.normalFormFrom ⋙ (m.normalFormTo ⋙ CategoryTheory.Prod.fst S (Pair G)) := rfl
    _ = CategoryTheory.Prod.fst S (Pair G) := by
        rw [← Functor.assoc, m.normalFormFrom_comp_normalFormTo]; rfl

end MinSpec

/-! ## Strict sections (paper `cor:section`) -/

/-- A strict section of `p` in the sense of paper `cor:section`: a functor `B : S ⥤ O` with the
    STRICT section equation `B ⋙ p = 𝟭 S` (paper `pB = id_S`) and a natural isomorphism
    `η : p ⋙ B ≅ 𝟭 O` (paper `η : Bp ⇒ id_O`) whose components are vertical.  Only the
    composite `B ⋙ p` is required to be an identity on the nose; `p ⋙ B` is only isomorphic
    to `𝟭 O` (it is not equal to it for nontrivial `G`, see `MinSpec.no_strict_retraction`). -/
structure StrictSection (p : O ⥤ S) where
  /-- The section functor `B` (paper `cor:section`). -/
  B : S ⥤ O
  /-- The strict section equation `pB = id_S` (paper `cor:section`). -/
  B_comp_p : B ⋙ p = 𝟭 S
  /-- The comparison `η : Bp ≅ id_O` (paper `cor:section`). -/
  η : p ⋙ B ≅ 𝟭 O
  /-- The components of `η` are vertical (paper `cor:section`). -/
  η_vertical : ∀ x, IsVertical p (η.hom.app x)

namespace StrictSection

variable (σ : StrictSection p)

/-- `B(s)` lies over `s` (paper `cor:section`). -/
theorem p_obj_B (s : S) : p.obj (σ.B.obj s) = s :=
  Functor.congr_obj σ.B_comp_p s

/-- `B(u)` lies over `u` (paper `cor:section`). -/
theorem p_map_B_map {s t : S} (u : s ⟶ t) :
    p.map (σ.B.map u) = eqToHom (σ.p_obj_B s) ≫ u ≫ eqToHom (σ.p_obj_B t).symm := by
  have h := Functor.congr_hom σ.B_comp_p u
  exact h

/-- The inverse components of `η` are vertical (paper `cor:section`). -/
theorem η_inv_vertical (x : O) : IsVertical p (σ.η.inv.app x) := by
  have e : σ.η.inv.app x = CategoryTheory.inv (σ.η.hom.app x) :=
    (IsIso.inv_eq_of_hom_inv_id (σ.η.hom_inv_id_app x)).symm
  rw [e]
  exact (σ.η_vertical x).inv

/-- A vertical arrow between any two objects of one fiber, `η_x⁻¹ ≫ B(eqToHom) ≫ η_y`
    (paper `def:vertical-trivial`: "every pair of objects in one fiber is connected by a
    vertical isomorphism"). -/
noncomputable def fiberHom {x y : O} (h : p.obj x = p.obj y) : x ⟶ y :=
  σ.η.inv.app x ≫ eqToHom (congrArg σ.B.obj h) ≫ σ.η.hom.app y

/-- The fiber arrow `σ.fiberHom h` is vertical (paper `def:vertical-trivial`). -/
theorem fiberHom_isVertical {x y : O} (h : p.obj x = p.obj y) : IsVertical p (σ.fiberHom h) :=
  (σ.η_inv_vertical x).comp ((IsVertical.eqToHom p _).comp (σ.η_vertical y))

/-- The fiber arrow `σ.fiberHom h` is an isomorphism (paper `def:vertical-trivial`). -/
instance fiberHom_isIso {x y : O} (h : p.obj x = p.obj y) : IsIso (σ.fiberHom h) := by
  show IsIso ((σ.η.app x).symm ≪≫ eqToIso (congrArg σ.B.obj h) ≪≫ σ.η.app y).hom
  infer_instance

/-- A strict section exhibits `p` as an equivalence of categories, with inverse `B`
    (paper `cor:section`: "Hence `p` is an equivalence of categories"). -/
noncomputable def equivalence : O ≌ S :=
  CategoryTheory.Equivalence.mk p σ.B σ.η.symm (eqToIso σ.B_comp_p)

/-- (paper `cor:section`) -/
@[simp] theorem equivalence_functor : σ.equivalence.functor = p := rfl

/-- (paper `cor:section`) -/
@[simp] theorem equivalence_inverse : σ.equivalence.inverse = σ.B := rfl

end StrictSection

/-! ## The section of a minimal specification (paper `cor:section`, `rem:groupoid`) -/

namespace MinSpec

variable (m : MinSpec G p)

/-- The section `B : S ⥤ O`, `B(s) = b_s`, `B(u)` the unique lift `b_s ⟶ b_t` of `u`
    (paper `cor:section`). -/
noncomputable def sectionFunctor : S ⥤ O where
  obj s := m.base s
  map {s t} u := m.liftOver u (m.p_base s) (m.p_base t)
  map_id _ := m.liftOver_id _
  map_comp u v := (m.liftOver_comp u v _ _ _).symm

/-- (paper `cor:section`) -/
@[simp] theorem sectionFunctor_obj (s : S) : m.sectionFunctor.obj s = m.base s := rfl

/-- (paper `cor:section`) -/
@[simp] theorem sectionFunctor_map {s t : S} (u : s ⟶ t) :
    m.sectionFunctor.map u = m.liftOver u (m.p_base s) (m.p_base t) := rfl

/-- The strict section equation `B ⋙ p = 𝟭 S` (paper `cor:section`). -/
theorem sectionFunctor_comp_p : m.sectionFunctor ⋙ p = 𝟭 S := by
  fapply CategoryTheory.Functor.ext
  · intro s; exact m.p_base s
  · intro s t u; exact m.p_map_liftOver u (m.p_base s) (m.p_base t)

/-- `B(u)` is the unique lift of `u` between the basepoints (paper `cor:section`). -/
theorem sectionFunctor_map_unique {s t : S} (u : s ⟶ t) (f : m.base s ⟶ m.base t)
    (hf : p.map f = eqToHom (m.p_base s) ≫ u ≫ eqToHom (m.p_base t).symm) :
    f = m.sectionFunctor.map u :=
  (m.eq_liftOver_iff u (m.p_base s) (m.p_base t) f).2 hf

/-- Unique lifts of identities are vertical (paper `def:vertical-trivial`, `cor:section`). -/
theorem liftOver_id_isVertical {s : S} {x y : O} (hx : p.obj x = s) (hy : p.obj y = s) :
    IsVertical p (m.liftOver (𝟙 s) hx hy) :=
  ⟨hx.trans hy.symm, by simp⟩

/-- The unique vertical arrow between two objects of one fiber (paper `cor:section`,
    `def:vertical-trivial`). -/
noncomputable def verticalHom {x y : O} (h : p.obj x = p.obj y) : x ⟶ y :=
  m.liftOver (𝟙 (p.obj y)) h rfl

/-- (paper `def:vertical-trivial`) -/
theorem verticalHom_isVertical {x y : O} (h : p.obj x = p.obj y) :
    IsVertical p (m.verticalHom h) :=
  m.liftOver_id_isVertical h rfl

/-- Every vertical arrow is the unique vertical arrow between its endpoints
    (paper `def:vertical-trivial`, uniqueness of lifts). -/
theorem eq_verticalHom_of_isVertical {x y : O} {v : x ⟶ y} (hv : IsVertical p v) :
    ∃ h : p.obj x = p.obj y, v = m.verticalHom h := by
  obtain ⟨h, e⟩ := hv
  exact ⟨h, (m.eq_liftOver_iff (𝟙 (p.obj y)) h rfl v).2 (by simp [e])⟩

/-- The vertical comparison `η : p ⋙ B ≅ 𝟭 O`, `η_x : b_{p x} ⟶ x` the unique vertical lift
    (paper `cor:section`). -/
noncomputable def sectionEta : p ⋙ m.sectionFunctor ≅ 𝟭 O :=
  NatIso.ofComponents
    (fun x => m.liftOverIso (Iso.refl (p.obj x)) (m.p_base (p.obj x)) rfl)
    (fun {x y} f => by
      have key : m.liftOver (p.map f) (m.p_base (p.obj x)) (m.p_base (p.obj y))
            ≫ m.liftOver (𝟙 (p.obj y)) (m.p_base (p.obj y)) rfl
          = m.liftOver (𝟙 (p.obj x)) (m.p_base (p.obj x)) rfl ≫ f := by
        apply m.hom_ext; simp
      exact key)

/-- (paper `cor:section`) -/
@[simp] theorem sectionEta_hom_app (x : O) :
    m.sectionEta.hom.app x = m.liftOver (𝟙 (p.obj x)) (m.p_base (p.obj x)) rfl := rfl

/-- (paper `cor:section`) -/
@[simp] theorem sectionEta_inv_app (x : O) :
    m.sectionEta.inv.app x = m.liftOver (𝟙 (p.obj x)) rfl (m.p_base (p.obj x)) := rfl

/-- The strict section of a minimal specification: `B(s) = b_s`, `B(u)` the unique lift,
    `η` the unique vertical lifts (paper `cor:section`). -/
noncomputable def strictSection : StrictSection p where
  B := m.sectionFunctor
  B_comp_p := m.sectionFunctor_comp_p
  η := m.sectionEta
  η_vertical x := m.liftOver_id_isVertical (m.p_base (p.obj x)) rfl

/-- (paper `cor:section`) -/
@[simp] theorem strictSection_B : m.strictSection.B = m.sectionFunctor := rfl

/-- (paper `cor:section`) -/
@[simp] theorem strictSection_η : m.strictSection.η = m.sectionEta := rfl

/-- `p` is NOT a strict isomorphism of categories in general: if `G` is nontrivial and `S` is
    nonempty, no functor `B'` satisfies `p ⋙ B' = 𝟭 O` (paper `cor:section`, which only
    asserts the strict equation `pB = id` and a natural isomorphism `Bp ≅ id`). -/
theorem no_strict_retraction (m : MinSpec G p) [Nontrivial G] [Nonempty S] :
    ¬ ∃ B' : S ⥤ O, p ⋙ B' = 𝟭 O := by
  rintro ⟨B', hB'⟩
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have h1 : B'.obj (p.obj (m.base s)) = m.base s := Functor.congr_obj hB' (m.base s)
  have h2 : B'.obj (p.obj (m.act (m.base s) g)) = m.act (m.base s) g :=
    Functor.congr_obj hB' (m.act (m.base s) g)
  have hp : p.obj (m.act (m.base s) g) = p.obj (m.base s) := m.p_act _ _
  rw [hp, h1] at h2
  have := congrArg m.coord h2
  simp at this
  exact hg this.symm

/-- Groupoid specialization, first half (paper `rem:groupoid`), for a minimal specification:
    if every arrow of `O` is invertible, so is every arrow of `S`. -/
theorem base_hom_isIso (m : MinSpec G p) (hO : ∀ {x y : O} (f : x ⟶ y), IsIso f)
    {s t : S} (u : s ⟶ t) :
    IsIso u := by
  have hf := m.p_map_liftOver u (m.p_base s) (m.p_base t)
  haveI : IsIso (m.liftOver u (m.p_base s) (m.p_base t)) := hO _
  have hu : u = eqToHom (m.p_base s).symm ≫ p.map (m.liftOver u (m.p_base s) (m.p_base t))
      ≫ eqToHom (m.p_base t) := by
    rw [hf]; simp
  rw [hu]
  infer_instance

/-- Groupoid specialization, converse half (paper `rem:groupoid`), for a minimal
    specification: if every arrow of `S` is invertible, so is every arrow of `O`. -/
theorem hom_isIso_of_base_isIso (m : MinSpec G p) (hS : ∀ {s t : S} (u : s ⟶ t), IsIso u)
    {x y : O} (f : x ⟶ y) :
    IsIso f := by
  haveI := m.full
  haveI := m.faithful
  haveI : IsIso (p.map f) := hS _
  exact isIso_of_reflects_iso f p

end MinSpec

/-! ## The normal form for normalized data (paper `thm:normalform`) -/

/-- Core's comparison functor `normalFormTo d` is the `N` of the underlying minimal
    specification (paper `thm:normalform`, `rem:audit`). -/
theorem normalFormTo_eq_toMinSpec (d : OEData G p) :
    normalFormTo d = d.toMinSpec.normalFormTo := rfl

/-- The inverse functor `M : S × Pair G ⥤ O` of normalized data: `M(s,g) = b_s · g`
    DEFINITIONALLY, and `M(u,*)` is the unique lift of `u` (paper `thm:normalform`). -/
noncomputable def normalFormFrom (d : OEData G p) : S × Pair G ⥤ O :=
  d.toMinSpec.normalFormFrom

/-- `M(s,g) = b_s · g`, definitionally (paper `thm:normalform`). -/
@[simp] theorem normalFormFrom_obj (d : OEData G p) (X : S × Pair G) :
    (normalFormFrom d).obj X = d.act (d.base X.1) X.2.pt := rfl

/-- `M` lies over the first projection on objects (paper `thm:normalform`). -/
theorem p_normalFormFrom_obj (d : OEData G p) (X : S × Pair G) :
    p.obj ((normalFormFrom d).obj X) = X.1 :=
  (d.p_act _ _).trans (d.p_base _)

/-- The morphism part of `M` is the unique lift of the base component (paper
    `thm:normalform`). -/
theorem normalFormFrom_map (d : OEData G p) {X Y : S × Pair G} (f : X ⟶ Y) :
    (normalFormFrom d).map f
      = d.toMinSpec.liftOver f.1 ((d.p_act (d.base X.1) X.2.pt).trans (d.p_base X.1)) ((d.p_act (d.base Y.1) Y.2.pt).trans (d.p_base Y.1)) := rfl

/-- Projection of `M` on arrows (paper `thm:normalform`). -/
@[simp] theorem p_map_normalFormFrom_map (d : OEData G p) {X Y : S × Pair G} (f : X ⟶ Y) :
    p.map ((normalFormFrom d).map f)
      = eqToHom ((d.p_act (d.base X.1) X.2.pt).trans (d.p_base X.1)) ≫ f.1
        ≫ eqToHom ((d.p_act (d.base Y.1) Y.2.pt).trans (d.p_base Y.1)).symm :=
  d.toMinSpec.p_map_liftOver f.1 ((d.p_act (d.base X.1) X.2.pt).trans (d.p_base X.1))
    ((d.p_act (d.base Y.1) Y.2.pt).trans (d.p_base Y.1))

/-- Uniqueness: the morphism part of `M` is the unique arrow with the given endpoints over the
    base component (paper `thm:normalform`). -/
theorem normalFormFrom_map_unique (d : OEData G p) {X Y : S × Pair G} (f : X ⟶ Y)
    (φ : (normalFormFrom d).obj X ⟶ (normalFormFrom d).obj Y)
    (hφ : p.map φ
      = eqToHom ((d.p_act (d.base X.1) X.2.pt).trans (d.p_base X.1)) ≫ f.1 ≫ eqToHom ((d.p_act (d.base Y.1) Y.2.pt).trans (d.p_base Y.1)).symm) :
    φ = (normalFormFrom d).map f :=
  (d.toMinSpec.eq_liftOver_iff f.1 ((d.p_act (d.base X.1) X.2.pt).trans (d.p_base X.1)) ((d.p_act (d.base Y.1) Y.2.pt).trans (d.p_base Y.1)) φ).2 hφ

/-- Strict inverse, first half: `N ⋙ M = 𝟭 O` (paper `thm:normalform`). -/
theorem normalFormTo_comp_normalFormFrom (d : OEData G p) :
    normalFormTo d ⋙ normalFormFrom d = 𝟭 O :=
  d.toMinSpec.normalFormTo_comp_normalFormFrom

/-- Strict inverse, second half: `M ⋙ N = 𝟭 (S × Pair G)` (paper `thm:normalform`). -/
theorem normalFormFrom_comp_normalFormTo (d : OEData G p) :
    normalFormFrom d ⋙ normalFormTo d = 𝟭 (S × Pair G) :=
  d.toMinSpec.normalFormFrom_comp_normalFormTo

/-- `M` lies over `S` strictly for normalized data: `normalFormFrom d ⋙ p = Prod.fst` as
    functors, on objects AND arrows (paper `thm:normalform`, "an isomorphism of categories over
    `S`"; the other half, `normalFormTo d ⋙ Prod.fst = p`, is `normalFormTo_fst` in `Core`). -/
theorem normalFormFrom_comp_fst (d : OEData G p) :
    normalFormFrom d ⋙ p = CategoryTheory.Prod.fst S (Pair G) :=
  d.toMinSpec.normalFormFrom_comp_fst

/-- `M` intertwines the right `G`-actions strictly (paper `thm:normalform`). -/
theorem normalFormFrom_equivariant (d : OEData G p) (g : G) :
    normalFormProductAction g ⋙ normalFormFrom d = normalFormFrom d ⋙ d.actFunctor g := by
  rw [← d.toMinSpec_actFunctor]
  exact d.toMinSpec.normalFormFrom_equivariant g

/-- `N` sends reindexing to `(t,g) ↦ (s,g)` on arrows: `N(χ_{u,y})` is the arrow
    `(u, *) : (s, g_y) ⟶ (t, g_y)`, up to the endpoint identifications
    `normalForm_reind` and `t = p(y)` (paper `thm:normalform`). -/
theorem normalFormTo_map_chi (d : OEData G p) {s t : S} (u : s ⟶ t) (y : O)
    (hy : p.obj y = t) :
    (normalFormTo d).map (d.chi u y hy)
      = eqToHom (normalForm_reind d u y hy)
        ≫ ((u, ⟨⟩) : ((s, ⟨d.coord y⟩) : S × Pair G) ⟶ (t, ⟨d.coord y⟩))
        ≫ eqToHom (Prod.ext hy.symm rfl : ((t, ⟨d.coord y⟩) : S × Pair G) = (normalFormTo d).obj y) := by
  apply prodPairHom_ext
  simp only [normalFormTo_map, prod_comp_fst, eqToHom_prod_fst, d.p_chi]
  rfl

/-! ## The section of normalized data (paper `cor:section`) -/

namespace OEData

variable (d : OEData G p)

/-- The section `B : S ⥤ O` of normalized data: `B(s) = b_s` DEFINITIONALLY, and `B(u)` is the
    unique lift `b_s ⟶ b_t` of `u` (paper `cor:section`). -/
noncomputable def sectionFunctor : S ⥤ O where
  obj s := d.base s
  map {s t} u := d.toMinSpec.liftOver u (d.p_base s) (d.p_base t)
  map_id _ := d.toMinSpec.liftOver_id _
  map_comp u v := (d.toMinSpec.liftOver_comp u v _ _ _).symm

/-- `B(s) = b_s` (definitional; paper `cor:section`). -/
@[simp] theorem sectionFunctor_obj (s : S) : d.sectionFunctor.obj s = d.base s := rfl

/-- `B(u)` is the unique lift (definitional; paper `cor:section`). -/
theorem sectionFunctor_map {s t : S} (u : s ⟶ t) :
    d.sectionFunctor.map u = d.toMinSpec.liftOver u (d.p_base s) (d.p_base t) := rfl

/-- `B(u)` lies over `u` (paper `cor:section`). -/
@[simp] theorem p_map_sectionFunctor_map {s t : S} (u : s ⟶ t) :
    p.map (d.sectionFunctor.map u) = eqToHom (d.p_base s) ≫ u ≫ eqToHom (d.p_base t).symm :=
  d.toMinSpec.p_map_liftOver u (d.p_base s) (d.p_base t)

/-- The strict section equation `B ⋙ p = 𝟭 S` (paper `cor:section`). -/
theorem sectionFunctor_comp_p : d.sectionFunctor ⋙ p = 𝟭 S := by
  fapply CategoryTheory.Functor.ext
  · intro s; exact d.p_base s
  · intro s t u; exact d.p_map_sectionFunctor_map u

/-- `B(u)` is the unique arrow `b_s ⟶ b_t` over `u` (paper `cor:section`). -/
theorem sectionFunctor_map_unique {s t : S} (u : s ⟶ t) (f : d.base s ⟶ d.base t)
    (hf : p.map f = eqToHom (d.p_base s) ≫ u ≫ eqToHom (d.p_base t).symm) :
    f = d.sectionFunctor.map u :=
  (d.toMinSpec.eq_liftOver_iff u (d.p_base s) (d.p_base t) f).2 hf

/-- For normalized data `B(u) = χ_{u,b_t}`, with the source rewritten by (N4)
    `u^* b_t = b_s` (paper `cor:section`). -/
theorem sectionFunctor_map_eq_chi {s t : S} (u : s ⟶ t) :
    d.sectionFunctor.map u = eqToHom (d.reind_base u).symm ≫ d.chi u (d.base t) (d.p_base t) := by
  symm
  apply d.sectionFunctor_map_unique
  simp [d.p_chi, eqToHom_map]

/-- The section of normalized data agrees with the section of its minimal specification
    (paper `cor:section`, `rem:audit`). -/
theorem toMinSpec_sectionFunctor : d.toMinSpec.sectionFunctor = d.sectionFunctor := by
  fapply CategoryTheory.Functor.ext
  · intro s; exact d.toMinSpec_base s
  · intro s t u
    have key : d.toMinSpec.liftOver u (d.toMinSpec.p_base s) (d.toMinSpec.p_base t)
        = eqToHom (d.toMinSpec_base s) ≫ d.toMinSpec.liftOver u (d.p_base s) (d.p_base t)
          ≫ eqToHom (d.toMinSpec_base t).symm := by
      apply d.toMinSpec.hom_ext
      simp
    exact key

/-- The target of `ℓ_{g_x, b_{p x}}` is `x`, by (N2) (paper `cor:section`). -/
theorem sectionEta_target_eq (x : O) :
    d.act (d.base (p.obj (d.base (p.obj x)))) (d.coord x * d.coord (d.base (p.obj x))) = x := by
  have hc : d.coord (d.base (p.obj x)) = 1 := by
    have := d.coord_base (p.obj x) 1; rwa [d.act_one] at this
  rw [hc, mul_one, d.p_base, d.base_coord]

/-- Naturality of `η` in clean endpoints: `B(p f) ≫ η_y = η_x ≫ f` (paper `cor:section`:
    both sides have the same endpoints and projection). -/
theorem sectionEta_naturality {x y : O} (f : x ⟶ y) :
    d.toMinSpec.liftOver (p.map f) (d.p_base (p.obj x)) (d.p_base (p.obj y))
        ≫ d.ltrans (d.coord y) (d.base (p.obj y)) ≫ eqToHom (d.sectionEta_target_eq y)
      = (d.ltrans (d.coord x) (d.base (p.obj x)) ≫ eqToHom (d.sectionEta_target_eq x)) ≫ f := by
  apply d.toMinSpec.hom_ext
  simp [d.p_ltrans, eqToHom_map]

/-- The vertical comparison `η : p ⋙ B ≅ 𝟭 O` of normalized data, with components
    `η_x = ℓ_{g_x, b_{p x}}` followed by the (N2) identification of the target
    (paper `cor:section`). -/
noncomputable def sectionEta : p ⋙ d.sectionFunctor ≅ 𝟭 O :=
  NatIso.ofComponents
    (fun x => d.ltransIso (d.coord x) (d.base (p.obj x)) ≪≫ eqToIso (d.sectionEta_target_eq x))
    (fun f => d.sectionEta_naturality f)

/-- `η_x = ℓ_{g_x, b_{p x}}` up to the target identification (paper `cor:section`). -/
@[simp] theorem sectionEta_hom_app (x : O) :
    d.sectionEta.hom.app x
      = d.ltrans (d.coord x) (d.base (p.obj x)) ≫ eqToHom (d.sectionEta_target_eq x) := rfl

/-- The components of `η` are vertical (paper `cor:section`). -/
theorem sectionEta_isVertical (x : O) : IsVertical p (d.sectionEta.hom.app x) := by
  have key : p.map (d.ltrans (d.coord x) (d.base (p.obj x)) ≫ eqToHom (d.sectionEta_target_eq x))
      = eqToHom (d.p_base (p.obj x)) := by
    simp only [Functor.map_comp, d.p_ltrans, eqToHom_map, eqToHom_trans]
  exact ⟨d.p_base (p.obj x), key⟩

/-- `η_x` is the unique vertical arrow `b_{p x} ⟶ x` (paper `cor:section`). -/
theorem sectionEta_hom_app_eq_liftOver (x : O) :
    d.sectionEta.hom.app x = d.toMinSpec.liftOver (𝟙 (p.obj x)) (d.p_base (p.obj x)) rfl := by
  have key : d.ltrans (d.coord x) (d.base (p.obj x)) ≫ eqToHom (d.sectionEta_target_eq x)
      = d.toMinSpec.liftOver (𝟙 (p.obj x)) (d.p_base (p.obj x)) rfl := by
    apply d.toMinSpec.hom_ext
    simp only [Functor.map_comp, d.p_ltrans, eqToHom_map, eqToHom_trans, MinSpec.p_map_liftOver,
      Category.id_comp]
  exact key

/-- The strict section of normalized data: `B = d.sectionFunctor` (`B(s) = b_s`
    definitionally), `η_x = ℓ_{g_x, b_{p x}}` (paper `cor:section`). -/
noncomputable def strictSection : StrictSection p where
  B := d.sectionFunctor
  B_comp_p := d.sectionFunctor_comp_p
  η := d.sectionEta
  η_vertical := d.sectionEta_isVertical

/-- (paper `cor:section`) -/
@[simp] theorem strictSection_B : d.strictSection.B = d.sectionFunctor := rfl

/-- (paper `cor:section`) -/
@[simp] theorem strictSection_η : d.strictSection.η = d.sectionEta := rfl

end OEData
