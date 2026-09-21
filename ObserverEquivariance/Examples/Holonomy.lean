import ObserverEquivariance.Core

/-!
# Nontrivial transport around loops (paper `sec:holonomy`, `prop:holonomy`)

Paper labels covered: `sec:holonomy` (the model and its transport laws), `prop:holonomy`
(the holonomy-controlled extension `1 → C_G(im ρ) → E_ρ → H_ρ → 1`), and the two examples
following it (the `S₃` transposition and the nonsplit `Q₈` extension).

For a group hom `ρ : Γ →* G` the model is
`S = SingleObj Γ`, `O = SingleObj Γ × Pair G`, `p = Prod.fst`, with transport
`γ^* (*, g) = (*, ρ(γ)⁻¹ g)` and chosen arrow `χ_{γ,g} = (γ, ⟨⟩)`.
This is deliberately NOT an `OEData` for general `ρ`: clause (N4) (parallel basepoints) is
exactly what fails, and `holReind_holBase_iff` proves it holds iff `ρ = 1`;
`holonomy_not_normalized` / `holonomy_not_OEData` state that for `ρ ≠ 1` no normalized datum
carries this transport and basepoint.  The remaining clauses hold: (N3) is the split,
right-equivariant transport (`holReind_id`, …, `holChi_act`), and (N1), (N2), (N5), (N6) are
bundled in `holonomy_N1_N2_N5_N6` (with `holLtrans_isIso` for invertibility in (N5)).
On the lift side, `holLiftProj` is the projection of the lift group to the base automorphism;
`holLift_exact` transfers `holonomy_exact` to it, with kernel `≃* C_G(im ρ)`
(`holLiftProjKerEquiv`).
-/

open CategoryTheory

universe u v

section Model

variable {Γ : Type u} {G : Type v} [Group Γ]

/-- The total category `O = BΓ × Pair(G)` of the holonomy model (paper `sec:holonomy`). -/
abbrev HolTotal (Γ : Type u) (G : Type v) [Group Γ] := SingleObj Γ × Pair G

/-- The projection `p = Prod.fst : BΓ × Pair(G) ⥤ BΓ` of the holonomy model
    (paper `sec:holonomy`). -/
abbrev holP (Γ : Type u) (G : Type v) [Group Γ] : HolTotal Γ G ⥤ SingleObj Γ :=
  CategoryTheory.Prod.fst (SingleObj Γ) (Pair G)

/-- The usual right `G`-action on objects of the holonomy model, `(*, g) · h = (*, g h)`
    (paper `sec:holonomy`, "the usual coordinates"). -/
def holAct [Mul G] (x : HolTotal Γ G) (h : G) : HolTotal Γ G := (x.1, ⟨x.2.pt * h⟩)

/-- The basepoint `b = 1` of the holonomy model (paper `sec:holonomy`). -/
def holBase [One G] (s : SingleObj Γ) : HolTotal Γ G := (s, ⟨1⟩)

variable [Group G]

/-- The holonomy action agrees with the product-model action `normalFormProductAction`
    of Core (paper `sec:holonomy`). -/
theorem holAct_eq_normalFormProductAction (x : HolTotal Γ G) (h : G) :
    holAct x h = (normalFormProductAction (S := SingleObj Γ) h).obj x := rfl

/-- The holonomy transport `γ^* (*, g) = (*, ρ(γ)⁻¹ g)` over an arrow `γ : s ⟶ t` of `BΓ`
    (paper `sec:holonomy`). -/
def holReind (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) :
    HolTotal Γ G :=
  (s, ⟨(ρ γ)⁻¹ * y.2.pt⟩)

/-- The chosen arrow `χ_{γ,y} : γ^* y ⟶ y` over `γ`, namely `(γ, ⟨⟩)` (paper `sec:holonomy`). -/
def holChi (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) :
    holReind ρ γ y ⟶ y :=
  (γ, ⟨⟩)

/-- The transported object lies over the source of `γ` (paper `sec:holonomy`, (N3)). -/
@[simp] theorem holP_obj_holReind (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t)
    (y : HolTotal Γ G) : (holP Γ G).obj (holReind ρ γ y) = s := rfl

/-- The chosen arrow `χ_{γ,y}` lies over `γ` (paper `sec:holonomy`, (N3)). -/
@[simp] theorem holP_map_holChi (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t)
    (y : HolTotal Γ G) : (holP Γ G).map (holChi ρ γ y) = γ := rfl

/-- Coordinates of the transport: the `Pair G`-component of `γ^* y` is `ρ(γ)⁻¹ g`
    (paper `sec:holonomy`). -/
@[simp] theorem holReind_pt (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t)
    (y : HolTotal Γ G) : (holReind ρ γ y).2.pt = (ρ γ)⁻¹ * y.2.pt := rfl

omit [Group G] in
/-- Local helper: two objects of `BΓ × Pair(G)` are equal iff their `Pair G`-points are
    (the `BΓ` component is a single object) (paper `sec:holonomy`). -/
theorem holTotal_ext {x y : HolTotal Γ G} (h : x.2.pt = y.2.pt) : x = y := by
  obtain ⟨x1, ⟨a⟩⟩ := x
  obtain ⟨y1, ⟨b⟩⟩ := y
  cases x1; cases y1
  cases h
  rfl

/-- Local helper: an `eqToHom` of `BΓ` is the neutral element `1 : Γ`
    (paper `sec:holonomy`). -/
theorem singleObj_eqToHom {a b : SingleObj Γ} (h : a = b) : eqToHom h = (1 : Γ) := by
  subst h; rfl

omit [Group G] in
/-- Local helper: the `BΓ`-component of an `eqToHom` of `BΓ × Pair(G)` is `1 : Γ`
    (paper `sec:holonomy`). -/
theorem holEqToHom_fst {x y : HolTotal Γ G} (h : x = y) : ((eqToHom h).1 : Γ) = 1 := by
  subst h; rfl

omit [Group G] in
/-- Local helper: arrows of `BΓ × Pair(G)` are determined by their `BΓ`-component
    (paper `sec:holonomy`). -/
theorem holHom_ext {x y : HolTotal Γ G} {f g : x ⟶ y} (h : (f.1 : Γ) = g.1) : f = g :=
  Prod.hom_ext h (Subsingleton.elim _ _)

/-! ### Split transport -/

/-- Splitness, identity law: `(𝟙 s)^* y = y` (paper `sec:holonomy`, "the homomorphism law
    makes this transport split"). -/
theorem holReind_id (ρ : Γ →* G) (s : SingleObj Γ) (y : HolTotal Γ G) :
    holReind ρ (𝟙 s) y = y := by
  apply holTotal_ext
  show (ρ (1 : Γ))⁻¹ * y.2.pt = y.2.pt
  rw [map_one, inv_one, one_mul]

/-- Splitness, composition law: `(γ ≫ δ)^* y = γ^* (δ^* y)` (paper `sec:holonomy`). -/
theorem holReind_comp (ρ : Γ →* G) {s t r : SingleObj Γ} (γ : s ⟶ t) (δ : t ⟶ r)
    (y : HolTotal Γ G) : holReind ρ (γ ≫ δ) y = holReind ρ γ (holReind ρ δ y) := by
  apply holTotal_ext
  show (ρ (δ * γ))⁻¹ * y.2.pt = (ρ γ)⁻¹ * ((ρ δ)⁻¹ * y.2.pt)
  rw [map_mul, mul_inv_rev, mul_assoc]

/-- Splitness of the chosen arrows, identity law: `χ_{𝟙,y} = 𝟙` up to the cast
    (paper `sec:holonomy`). -/
theorem holChi_id (ρ : Γ →* G) (s : SingleObj Γ) (y : HolTotal Γ G) :
    holChi ρ (𝟙 s) y = eqToHom (holReind_id ρ s y) := by
  apply holHom_ext
  rw [holEqToHom_fst]
  rfl

/-- Splitness of the chosen arrows, composition law:
    `χ_{γ≫δ,y} = cast ≫ χ_{γ, δ^* y} ≫ χ_{δ,y}` (paper `sec:holonomy`). -/
theorem holChi_comp (ρ : Γ →* G) {s t r : SingleObj Γ} (γ : s ⟶ t) (δ : t ⟶ r)
    (y : HolTotal Γ G) :
    holChi ρ (γ ≫ δ) y
      = eqToHom (holReind_comp ρ γ δ y) ≫ holChi ρ γ (holReind ρ δ y) ≫ holChi ρ δ y := by
  apply holHom_ext
  show ((γ ≫ δ : s ⟶ r) : Γ) = (eqToHom (holReind_comp ρ γ δ y)).1 ≫ (γ ≫ δ)
  rw [holEqToHom_fst]
  show δ * γ = (δ * γ) * 1
  rw [mul_one]

/-! ### Right equivariance of the transport -/

/-- The transport commutes with right multiplication: `γ^* (y · h) = (γ^* y) · h`
    (paper `sec:holonomy`). -/
theorem holReind_act (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G)
    (h : G) : holReind ρ γ (holAct y h) = holAct (holReind ρ γ y) h := by
  apply holTotal_ext
  show (ρ γ)⁻¹ * (y.2.pt * h) = (ρ γ)⁻¹ * y.2.pt * h
  rw [mul_assoc]

/-- The chosen arrows are right equivariant: `χ_{γ, y·h} = cast ≫ R_h(χ_{γ,y})`, with `R_h` the
    product action functor (paper `sec:holonomy`). -/
theorem holChi_act (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) (h : G) :
    holChi ρ γ (holAct y h)
      = eqToHom (holReind_act ρ γ y h)
          ≫ (normalFormProductAction (S := SingleObj Γ) h).map (holChi ρ γ y) := by
  apply holHom_ext
  show (γ : Γ) = (eqToHom (holReind_act ρ γ y h)).1 ≫ γ
  rw [holEqToHom_fst]
  show γ = γ * 1
  rw [mul_one]

/-! ### Parallelity of the basepoint -/

/-- (N4) for the holonomy model holds exactly for trivial `ρ`: the basepoint `1` is parallel,
    `γ^* b_t = b_s` for all arrows, iff `ρ = 1` (paper `sec:holonomy`). -/
theorem holReind_holBase_iff (ρ : Γ →* G) :
    (∀ {s t : SingleObj Γ} (γ : s ⟶ t), holReind ρ γ (holBase t) = holBase s) ↔ ρ = 1 := by
  constructor
  · intro h
    ext γ
    have h1 := congrArg (fun x : HolTotal Γ G => x.2.pt)
      (h (s := SingleObj.star Γ) (t := SingleObj.star Γ) γ)
    simp only [holReind_pt, holBase, mul_one, inv_eq_one] at h1
    simpa using h1
  · rintro rfl s t γ
    apply holTotal_ext
    show ((1 : Γ →* G) γ)⁻¹ * 1 = 1
    simp

/-! ### The remaining clauses (N1), (N2), (N5), (N6) -/

/-- Coordinates of the holonomy model, `g_{(*, g)} = g` (paper `sec:holonomy`, "the usual
    coordinates"; `def:data` (N2)). -/
def holCoord (x : HolTotal Γ G) : G := x.2.pt

/-- (N1), object unit law: `x · 1 = x` (paper `sec:holonomy`, `def:data` (N1)). -/
theorem holAct_one (x : HolTotal Γ G) : holAct x 1 = x := holTotal_ext (mul_one _)

/-- (N1), object composition law: `(x · g) · h = x · (g h)`
    (paper `sec:holonomy`, `def:data` (N1)). -/
theorem holAct_mul (x : HolTotal Γ G) (g h : G) : holAct (holAct x g) h = holAct x (g * h) :=
  holTotal_ext (mul_assoc _ _ _)

/-- (N1), the action is over `S` on objects: `p (x · g) = p x`
    (paper `sec:holonomy`, `def:data` (N1)). -/
theorem holP_holAct (x : HolTotal Γ G) (g : G) :
    (holP Γ G).obj (holAct x g) = (holP Γ G).obj x := rfl

/-- (N1), morphism unit law: `R_1` is the identity functor
    (paper `sec:holonomy`, `def:data` (N1)). -/
theorem holAct_functor_one :
    normalFormProductAction (S := SingleObj Γ) (1 : G) = 𝟭 (HolTotal Γ G) :=
  CategoryTheory.Functor.ext (fun _ => holTotal_ext (mul_one _)) (fun _ _ _ => holHom_ext (by
    simp only [Functor.id_map, prod_comp_fst]; rw [holEqToHom_fst, holEqToHom_fst]
    simp only [SingleObj.comp_as_mul, mul_one, one_mul]; rfl))

/-- (N1), morphism composition law: `R_h R_g = R_{gh}`, i.e. `R_g ⋙ R_h = R_{g h}`
    (paper `sec:holonomy`, `def:data` (N1)). -/
theorem holAct_functor_mul (g h : G) :
    normalFormProductAction (S := SingleObj Γ) g ⋙ normalFormProductAction h
      = normalFormProductAction (g * h) :=
  CategoryTheory.Functor.ext (fun _ => holTotal_ext (mul_assoc _ _ _)) (fun _ _ _ => holHom_ext (by
    simp only [Functor.comp_map, prod_comp_fst]; rw [holEqToHom_fst, holEqToHom_fst]
    simp only [SingleObj.comp_as_mul, mul_one, one_mul]; rfl))

/-- (N1), the action is over `S` on morphisms: `p R_g = p`
    (paper `sec:holonomy`, `def:data` (N1)). -/
theorem holP_act_functor (g : G) :
    normalFormProductAction (S := SingleObj Γ) g ⋙ holP Γ G = holP Γ G := rfl

/-- (N2): `x = b_{p x} · g_x` (paper `sec:holonomy`, `def:data` (N2)). -/
theorem holBase_coord (x : HolTotal Γ G) :
    holAct (holBase ((holP Γ G).obj x)) (holCoord x) = x := holTotal_ext (one_mul _)

/-- (N2): `g_{b_s · g} = g` (paper `sec:holonomy`, `def:data` (N2)). -/
theorem holCoord_holAct_holBase (s : SingleObj Γ) (g : G) :
    holCoord (holAct (holBase s) g) = g := one_mul g

/-- (N5): the chosen vertical isomorphism `ℓ_{a,x} : x ≅ b_{p x} · (a g_x)`, with base
    component the identity (paper `sec:holonomy`, "the usual vertical translations";
    `def:data` (N5)). -/
def holLtrans (a : G) (x : HolTotal Γ G) :
    x ≅ holAct (holBase ((holP Γ G).obj x)) (a * holCoord x) where
  hom := (𝟙 x.1, ⟨⟩)
  inv := (𝟙 x.1, ⟨⟩)
  hom_inv_id := holHom_ext (Category.id_comp _)
  inv_hom_id := holHom_ext (Category.id_comp _)

/-- (N5): `ℓ_{a,x}` is vertical, `p(ℓ_{a,x}) = 𝟙_{p x}` (paper `sec:holonomy`, `def:data` (N5)). -/
theorem holP_map_holLtrans (a : G) (x : HolTotal Γ G) :
    (holP Γ G).map (holLtrans a x).hom = 𝟙 _ := rfl

/-- (N5): the arrow `ℓ_{a,x}` is an isomorphism (paper `sec:holonomy`, `def:data` (N5)). -/
theorem holLtrans_isIso (a : G) (x : HolTotal Γ G) : IsIso (holLtrans a x).hom :=
  inferInstance

omit [Group G] in
/-- (N6): the projection `p = Prod.fst` of the holonomy model is faithful
    (paper `sec:holonomy`, `def:data` (N6)). -/
theorem holP_faithful : (holP Γ G).Faithful := ⟨fun {_ _} _ _ h => holHom_ext h⟩

/-- The holonomy data satisfy (N1), (N2), (N5) and (N6) (paper `sec:holonomy`: "These data
    satisfy (N1)--(N3) and (N5)--(N6)"; (N3) is `holReind_id`, `holReind_comp`, `holChi_id`,
    `holChi_comp`, `holReind_act`, `holChi_act`, `holP_obj_holReind`, `holP_map_holChi`).
    The isomorphism part of (N5) is `holLtrans_isIso`. -/
theorem holonomy_N1_N2_N5_N6 :
    ((∀ x : HolTotal Γ G, holAct x 1 = x) ∧
      (∀ (x : HolTotal Γ G) (g h : G), holAct (holAct x g) h = holAct x (g * h)) ∧
      (∀ (x : HolTotal Γ G) (g : G), (holP Γ G).obj (holAct x g) = (holP Γ G).obj x) ∧
      normalFormProductAction (S := SingleObj Γ) (1 : G) = 𝟭 (HolTotal Γ G) ∧
      (∀ g h : G, normalFormProductAction (S := SingleObj Γ) g ⋙ normalFormProductAction h
        = normalFormProductAction (g * h)) ∧
      (∀ g : G, normalFormProductAction (S := SingleObj Γ) g ⋙ holP Γ G = holP Γ G)) ∧
    ((∀ s : SingleObj Γ, (holP Γ G).obj (holBase (G := G) s) = s) ∧
      (∀ x : HolTotal Γ G, holAct (holBase ((holP Γ G).obj x)) (holCoord x) = x) ∧
      (∀ (s : SingleObj Γ) (g : G), holCoord (holAct (holBase s) g) = g)) ∧
    (∀ (a : G) (x : HolTotal Γ G), (holP Γ G).map (holLtrans a x).hom = 𝟙 _) ∧
    (holP Γ G).Faithful :=
  -- `holP_holAct` / `holBase_coord` are inlined: `Pair`'s hom universe is otherwise left free.
  ⟨⟨holAct_one, holAct_mul, fun _ _ => rfl, holAct_functor_one, holAct_functor_mul,
      holP_act_functor⟩,
    ⟨fun _ => rfl, fun _ => holTotal_ext (one_mul _), holCoord_holAct_holBase⟩,
    holP_map_holLtrans, holP_faithful⟩

/-- For nontrivial `ρ` the holonomy data are NOT normalized: no `NormalizedPreDatum` on
    `p = Prod.fst : BΓ × Pair(G) ⥤ BΓ` has the holonomy transport `γ^* (*, g) = (*, ρ(γ)⁻¹ g)`
    and the basepoint `b = 1`, since (N4) would force `ρ = 1` (paper `sec:holonomy`,
    "(N4) holds only when ρ is trivial"). -/
theorem holonomy_not_normalized (ρ : Γ →* G) (hρ : ρ ≠ 1) :
    ¬ ∃ d : NormalizedPreDatum G (holP Γ G),
      (∀ {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) (hy : (holP Γ G).obj y = t),
        d.reind γ y hy = holReind ρ γ y) ∧ ∀ s, d.base s = holBase s := by
  rintro ⟨d, hr, hb⟩
  apply hρ
  rw [← holReind_holBase_iff]
  intro s t γ
  have h := d.reind_base γ
  rw [hr, hb, hb] at h
  exact h

/-- For nontrivial `ρ` there is no `OEData G (holP Γ G)` whose transport is the holonomy
    transport and whose basepoint is `b = 1` (paper `sec:holonomy`, "(N4) holds only when ρ is
    trivial"); the same argument as `holonomy_not_normalized`, via the inherited `reind_base`. -/
theorem holonomy_not_OEData (ρ : Γ →* G) (hρ : ρ ≠ 1) :
    ¬ ∃ d : OEData G (holP Γ G),
      (∀ {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) (hy : (holP Γ G).obj y = t),
        d.reind γ y hy = holReind ρ γ y) ∧ ∀ s, d.base s = holBase s := by
  rintro ⟨d, hr, hb⟩
  apply hρ
  rw [← holReind_holBase_iff]
  intro s t γ
  have h := d.reind_base γ
  rw [hr, hb, hb] at h
  exact h

end Model

/-! ## The lift group and `E_ρ` (paper `prop:holonomy`) -/

section Lifts

variable {Γ : Type u} {G : Type v} [Group Γ] [Group G]

omit [Group G] in
/-- Local helper: a functor into `BΓ × Pair(G)` is determined by its objects and the
    `BΓ`-components of its arrows (paper `prop:holonomy`, "a lift is determined by ..."). -/
theorem holFunctor_ext {C : Type*} [Category C] {F F' : C ⥤ HolTotal Γ G}
    (hobj : ∀ x, F.obj x = F'.obj x)
    (hmap : ∀ {x y : C} (f : x ⟶ y), ((F.map f).1 : Γ) = (F'.map f).1) : F = F' := by
  refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
  apply holHom_ext
  show ((F.map f).1 : Γ)
    = ((eqToHom (hobj y).symm).1 * (F'.map f).1) * (eqToHom (hobj x)).1
  rw [holEqToHom_fst, holEqToHom_fst, mul_one, one_mul, hmap]

/-- The conditions of paper `def:lifts` for the holonomy model (paper `prop:holonomy`):
    `F` covers the base functor `A` strictly, is (object-level) `G`-equivariant, and preserves
    the holonomy transport on objects, `F(γ^* y) = (A γ)^* F(y)`. -/
structure IsHolLift (ρ : Γ →* G) (F : HolTotal Γ G ⥤ HolTotal Γ G)
    (A : SingleObj Γ ⥤ SingleObj Γ) : Prop where
  covers : F ⋙ holP Γ G = holP Γ G ⋙ A
  equiv : ∀ (x : HolTotal Γ G) (h : G), F.obj (holAct x h) = holAct (F.obj x) h
  pres : ∀ {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G),
    F.obj (holReind ρ γ y) = holReind ρ (A.map γ) (F.obj y)

/-- The group of equivariant, transport-preserving lifts in the holonomy model (paper
    `prop:holonomy`): pairs `(F, A)` of a strict automorphism `F` of `O = BΓ × Pair(G)` and a
    strict automorphism `A` of `S = BΓ` such that `F` covers `A`, is `G`-equivariant and
    preserves the holonomy transport.  Group law: componentwise composition. -/
def HolLift (ρ : Γ →* G) : Subgroup (StrictAut (HolTotal Γ G) × StrictAut (SingleObj Γ)) where
  carrier := {e | IsHolLift ρ e.1.hom e.2.hom}
  one_mem' := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := fun {a b} ha hb => by
    have ha : IsHolLift ρ a.1.hom a.2.hom := ha
    have hb : IsHolLift ρ b.1.hom b.2.hom := hb
    show IsHolLift ρ (b.1.hom ⋙ a.1.hom) (b.2.hom ⋙ a.2.hom)
    refine ⟨?_, fun x h => ?_, fun γ y => ?_⟩
    · rw [Functor.assoc, ha.covers, ← Functor.assoc, hb.covers, Functor.assoc]
    · show a.1.hom.obj (b.1.hom.obj (holAct x h)) = holAct (a.1.hom.obj (b.1.hom.obj x)) h
      rw [hb.equiv, ha.equiv]
    · show a.1.hom.obj (b.1.hom.obj (holReind ρ γ y))
        = holReind ρ (a.2.hom.map (b.2.hom.map γ)) (a.1.hom.obj (b.1.hom.obj y))
      rw [hb.pres, ha.pres]
  inv_mem' := fun {a} ha => by
    have ha : IsHolLift ρ a.1.hom a.2.hom := ha
    show IsHolLift ρ a.1.inv a.2.inv
    obtain ⟨⟨F, Finv, hFF', hF'F⟩, ⟨B, Binv, hBB', hB'B⟩⟩ := a
    have ha : IsHolLift ρ F B := ha
    have hobj : ∀ x, F.obj (Finv.obj x) = x := fun x => Functor.congr_obj hF'F x
    have hobj' : ∀ x, Finv.obj (F.obj x) = x := fun x => Functor.congr_obj hFF' x
    have hinj : ∀ x y, F.obj x = F.obj y → x = y := fun x y h => by
      rw [← hobj' x, ← hobj' y, h]
    have hmap : ∀ {s t : SingleObj Γ} (γ : s ⟶ t), ((B.map (Binv.map γ)) : Γ) = γ := by
      intro s t γ
      have h := Functor.congr_hom hB'B γ
      rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul, singleObj_eqToHom,
        singleObj_eqToHom, one_mul, mul_one] at h
      exact h
    refine ⟨?_, fun x h => ?_, fun γ y => ?_⟩
    · calc Finv ⋙ holP Γ G = Finv ⋙ holP Γ G ⋙ (B ⋙ Binv) := by
            rw [hBB', Functor.comp_id]
        _ = Finv ⋙ (holP Γ G ⋙ B) ⋙ Binv := rfl
        _ = Finv ⋙ (F ⋙ holP Γ G) ⋙ Binv := by rw [ha.covers]
        _ = (Finv ⋙ F) ⋙ holP Γ G ⋙ Binv := rfl
        _ = holP Γ G ⋙ Binv := by rw [hF'F, Functor.id_comp]
    · apply hinj
      rw [ha.equiv, hobj, hobj]
    · apply hinj
      rw [ha.pres, hobj, hobj]
      apply holTotal_ext
      show (ρ γ)⁻¹ * y.2.pt = (ρ (B.map (Binv.map γ)))⁻¹ * y.2.pt
      rw [hmap γ]

/-- Membership in the lift group is the lift predicate (paper `prop:holonomy`). -/
theorem mem_HolLift (ρ : Γ →* G) (e : StrictAut (HolTotal Γ G) × StrictAut (SingleObj Γ)) :
    e ∈ HolLift ρ ↔ IsHolLift ρ e.1.hom e.2.hom := Iff.rfl

/-- A lift has object map `g ↦ k g` with `k` the coordinate of the image of the basepoint
    (paper `prop:holonomy`, proof: "a lift ... is determined by `g ↦ kg` on objects"). -/
theorem IsHolLift.obj_pt {ρ : Γ →* G} {F : HolTotal Γ G ⥤ HolTotal Γ G}
    {A : SingleObj Γ ⥤ SingleObj Γ} (hF : IsHolLift ρ F A) (x : HolTotal Γ G) :
    (F.obj x).2.pt = (F.obj (holBase (SingleObj.star Γ))).2.pt * x.2.pt := by
  have hx : x = holAct (holBase (SingleObj.star Γ)) x.2.pt :=
    holTotal_ext (by show x.2.pt = 1 * x.2.pt; rw [one_mul])
  calc (F.obj x).2.pt = (F.obj (holAct (holBase (SingleObj.star Γ)) x.2.pt)).2.pt :=
        congrArg (fun z => (F.obj z).2.pt) hx
    _ = _ := by rw [hF.equiv]; rfl

/-- A lift acts on the base component of arrows by the covered base functor,
    `γ ↦ A γ` (paper `prop:holonomy`, proof). -/
theorem IsHolLift.map_fst {ρ : Γ →* G} {F : HolTotal Γ G ⥤ HolTotal Γ G}
    {A : SingleObj Γ ⥤ SingleObj Γ} (hF : IsHolLift ρ F A) {x y : HolTotal Γ G} (f : x ⟶ y) :
    ((F.map f).1 : Γ) = A.map f.1 := by
  have h := Functor.congr_hom hF.covers f
  rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul, singleObj_eqToHom, singleObj_eqToHom,
    one_mul, mul_one] at h
  exact h

/-- Morphism form of transport preservation: a lift sends the chosen arrow `χ_{γ,y}` to the
    chosen arrow `χ_{Aγ, F y}` up to the object cast (paper `prop:holonomy`, with `def:lifts`). -/
theorem IsHolLift.map_holChi {ρ : Γ →* G} {F : HolTotal Γ G ⥤ HolTotal Γ G}
    {A : SingleObj Γ ⥤ SingleObj Γ} (hF : IsHolLift ρ F A) {s t : SingleObj Γ} (γ : s ⟶ t)
    (y : HolTotal Γ G) :
    F.map (holChi ρ γ y) = eqToHom (hF.pres γ y) ≫ holChi ρ (A.map γ) (F.obj y) := by
  apply holHom_ext
  rw [hF.map_fst]
  show A.map γ = A.map γ * (eqToHom (hF.pres γ y)).1
  rw [holEqToHom_fst, mul_one]

/-- The subgroup `E_ρ = {(k, α) ∈ G × Aut(Γ) | ∀ γ, ρ(α γ) = k ρ(γ) k⁻¹}` of the direct product
    `G × MulAut Γ` (multiplication `(k,α)(l,β) = (kl, αβ)`) (paper `prop:holonomy`). -/
def Eρ (ρ : Γ →* G) : Subgroup (G × MulAut Γ) where
  carrier := {e | ∀ γ : Γ, ρ (e.2 γ) = e.1 * ρ γ * e.1⁻¹}
  one_mem' := fun γ => by
    show ρ ((1 : MulAut Γ) γ) = 1 * ρ γ * 1⁻¹
    rw [MulAut.one_apply, one_mul, inv_one, mul_one]
  mul_mem' := fun {a b} ha hb γ => by
    show ρ ((a.2 * b.2) γ) = (a.1 * b.1) * ρ γ * (a.1 * b.1)⁻¹
    rw [MulAut.mul_apply, ha, hb]
    group
  inv_mem' := fun {a} ha γ => by
    show ρ (a.2⁻¹ γ) = a.1⁻¹ * ρ γ * a.1⁻¹⁻¹
    have h := ha (a.2⁻¹ γ)
    rw [MulAut.apply_inv_self] at h
    rw [h]
    group

/-- Membership in `E_ρ` unfolded (paper `prop:holonomy`). -/
theorem mem_Eρ (ρ : Γ →* G) (e : G × MulAut Γ) :
    e ∈ Eρ ρ ↔ ∀ γ : Γ, ρ (e.2 γ) = e.1 * ρ γ * e.1⁻¹ := Iff.rfl

/-- The subgroup `H_ρ = {α ∈ Aut(Γ) | ρ ∘ α is conjugate to ρ in G}` (paper `prop:holonomy`);
    see `mem_Hρ_iff_conj` for the literal "conjugate homomorphisms" form. -/
def Hρ (ρ : Γ →* G) : Subgroup (MulAut Γ) where
  carrier := {α | ∃ k : G, ∀ γ : Γ, ρ (α γ) = k * ρ γ * k⁻¹}
  one_mem' := ⟨1, (Eρ ρ).one_mem⟩
  mul_mem' := fun {α β} ⟨k, hk⟩ ⟨l, hl⟩ =>
    ⟨k * l, (Eρ ρ).mul_mem (show (k, α) ∈ Eρ ρ from hk) (show (l, β) ∈ Eρ ρ from hl)⟩
  inv_mem' := fun {α} ⟨k, hk⟩ => ⟨k⁻¹, (Eρ ρ).inv_mem (show (k, α) ∈ Eρ ρ from hk)⟩

/-- `α ∈ H_ρ` iff `ρ ∘ α = Ad_k ∘ ρ` for some `k : G` (paper `prop:holonomy`). -/
theorem mem_Hρ_iff_conj (ρ : Γ →* G) (α : MulAut Γ) :
    α ∈ Hρ ρ ↔ ∃ k : G, ρ.comp α.toMonoidHom = (MulAut.conj k).toMonoidHom.comp ρ := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, MonoidHom.ext fun γ => by simpa [MulAut.conj_apply] using hk γ⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, fun γ => by simpa [MulAut.conj_apply] using DFunLike.congr_fun hk γ⟩

/-! ### Identification of the lift group with `E_ρ` -/

/-- The lift functor `(*, g) ↦ (*, k g)`, `(γ, ⟨⟩) ↦ (α γ, ⟨⟩)` (paper `prop:holonomy`). -/
def holLiftFunctor (k : G) (α : MulAut Γ) : HolTotal Γ G ⥤ HolTotal Γ G where
  obj x := (x.1, ⟨k * x.2.pt⟩)
  map f := ((α f.1 : Γ), ⟨⟩)
  map_id _ := holHom_ext (map_one α)
  map_comp f g := holHom_ext (map_mul α g.1 f.1)

/-- The strict automorphism of `O` with object map `g ↦ k g` and base action `α`
    (paper `prop:holonomy`). -/
def holLiftAut (k : G) (α : MulAut Γ) : StrictAut (HolTotal Γ G) where
  hom := holLiftFunctor k α
  inv := holLiftFunctor k⁻¹ α⁻¹
  hom_inv_id := holFunctor_ext (fun x => holTotal_ext (inv_mul_cancel_left k x.2.pt))
    (fun f => MulAut.inv_apply_self Γ α f.1)
  inv_hom_id := holFunctor_ext (fun x => holTotal_ext (mul_inv_cancel_left k x.2.pt))
    (fun f => MulAut.apply_inv_self Γ α f.1)

/-- The strict automorphism of `BΓ` induced by `α ∈ Aut(Γ)` (paper `prop:holonomy`, "a strict
    base automorphism is an `α ∈ Aut(Γ)`"). -/
def holBaseAut (α : MulAut Γ) : StrictAut (SingleObj Γ) where
  hom := SingleObj.mapHom Γ Γ α.toMonoidHom
  inv := SingleObj.mapHom Γ Γ (α⁻¹ : MulAut Γ).toMonoidHom
  hom_inv_id := by
    rw [← SingleObj.mapHom_comp]
    have : (α⁻¹ : MulAut Γ).toMonoidHom.comp α.toMonoidHom = MonoidHom.id Γ :=
      MonoidHom.ext fun g => MulAut.inv_apply_self Γ α g
    rw [this, SingleObj.mapHom_id]
  inv_hom_id := by
    rw [← SingleObj.mapHom_comp]
    have : α.toMonoidHom.comp (α⁻¹ : MulAut Γ).toMonoidHom = MonoidHom.id Γ :=
      MonoidHom.ext fun g => MulAut.apply_inv_self Γ α g
    rw [this, SingleObj.mapHom_id]

/-- `θSingleObjEquiv` recovers `α` from `holBaseAut α` (paper `prop:holonomy`). -/
@[simp] theorem θSingleObjEquiv_holBaseAut (α : MulAut Γ) :
    θSingleObjEquiv Γ (holBaseAut α) = α := by
  ext g; rfl

/-- Transport preservation for a lift is exactly the defining equation of `E_ρ`, one direction:
    every lift gives an element of `E_ρ` (paper `prop:holonomy`, proof). -/
theorem IsHolLift.mem_Eρ {ρ : Γ →* G} {F : HolTotal Γ G ⥤ HolTotal Γ G}
    {A : StrictAut (SingleObj Γ)} (hF : IsHolLift ρ F A.hom) :
    ((F.obj (holBase (SingleObj.star Γ))).2.pt, θSingleObjEquiv Γ A) ∈ Eρ ρ := by
  intro γ
  have h1 := congrArg (fun z : HolTotal Γ G => z.2.pt)
    (hF.pres (s := SingleObj.star Γ) (t := SingleObj.star Γ) γ (holBase (SingleObj.star Γ)))
  simp only [holReind_pt] at h1
  rw [hF.obj_pt (holReind ρ (s := SingleObj.star Γ) (t := SingleObj.star Γ) γ
    (holBase (SingleObj.star Γ))), holReind_pt] at h1
  show ρ (A.hom.map (X := SingleObj.star Γ) (Y := SingleObj.star Γ) γ)
    = (F.obj (holBase (SingleObj.star Γ))).2.pt * ρ γ * (F.obj (holBase (SingleObj.star Γ))).2.pt⁻¹
  generalize (F.obj (holBase (SingleObj.star Γ))).2.pt = k at h1 ⊢
  generalize ρ (A.hom.map (X := SingleObj.star Γ) (Y := SingleObj.star Γ) γ) = r at h1 ⊢
  have h2 : r⁻¹ = k * (ρ γ)⁻¹ * k⁻¹ := by
    apply eq_mul_inv_of_mul_eq
    rw [← h1]
    show k * ((ρ γ)⁻¹ * 1) = k * (ρ γ)⁻¹
    rw [mul_one]
  rw [← inv_inj, h2]
  group

/-- Conversely every element of `E_ρ` gives a lift (paper `prop:holonomy`, proof). -/
theorem holLiftAut_mem {ρ : Γ →* G} {k : G} {α : MulAut Γ} (h : (k, α) ∈ Eρ ρ) :
    (holLiftAut k α, holBaseAut α) ∈ HolLift ρ := by
  refine ⟨rfl, fun x g => ?_, fun γ y => ?_⟩
  · apply holTotal_ext
    show k * (x.2.pt * g) = k * x.2.pt * g
    rw [mul_assoc]
  · apply holTotal_ext
    have hγ : ρ (α γ) = k * ρ γ * k⁻¹ := h γ
    show k * ((ρ γ)⁻¹ * y.2.pt) = (ρ (α γ))⁻¹ * (k * y.2.pt)
    rw [hγ]
    group

/-- The group of equivariant transport-preserving lifts is `E_ρ` (paper `prop:holonomy`):
    `(F, A) ↦ (k, θ(A))`, where `k` is the coordinate of `F(b)` and `θ = θSingleObjEquiv`. -/
noncomputable def holLiftEquiv (ρ : Γ →* G) : HolLift ρ ≃* Eρ ρ where
  toFun e := ⟨((e.1.1.hom.obj (holBase (SingleObj.star Γ))).2.pt, θSingleObjEquiv Γ e.1.2),
    IsHolLift.mem_Eρ e.2⟩
  invFun e := ⟨(holLiftAut e.1.1 e.1.2, holBaseAut e.1.2), holLiftAut_mem e.2⟩
  left_inv e := by
    obtain ⟨⟨F, A⟩, hF⟩ := e
    have hF : IsHolLift ρ F.hom A.hom := hF
    apply Subtype.ext
    apply Prod.ext
    · apply StrictAut.ext_hom
      apply holFunctor_ext
      · intro x
        apply holTotal_ext
        exact (hF.obj_pt x).symm
      · intro x y f
        exact (hF.map_fst f).symm
    · apply θSingleObj_injective
      exact θSingleObjEquiv_holBaseAut _
  right_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · show e.1.1 * 1 = e.1.1
      rw [mul_one]
    · exact θSingleObjEquiv_holBaseAut _
  map_mul' e₁ e₂ := by
    have h₁ : IsHolLift ρ e₁.1.1.hom e₁.1.2.hom := e₁.2
    apply Subtype.ext
    apply Prod.ext
    · show (e₁.1.1.hom.obj (e₂.1.1.hom.obj (holBase (SingleObj.star Γ)))).2.pt
        = (e₁.1.1.hom.obj (holBase (SingleObj.star Γ))).2.pt
          * (e₂.1.1.hom.obj (holBase (SingleObj.star Γ))).2.pt
      exact h₁.obj_pt _
    · exact map_mul (θSingleObjEquiv Γ) e₁.1.2 e₂.1.2

/-- The `G`-component of `holLiftEquiv` is the coordinate of the image of the basepoint
    (paper `prop:holonomy`). -/
@[simp] theorem holLiftEquiv_apply_fst (ρ : Γ →* G) (e : HolLift ρ) :
    (holLiftEquiv ρ e).1.1 = (e.1.1.hom.obj (holBase (SingleObj.star Γ))).2.pt := rfl

/-- The `Aut(Γ)`-component of `holLiftEquiv` is the base automorphism under
    `θSingleObjEquiv` (paper `prop:holonomy`). -/
@[simp] theorem holLiftEquiv_apply_snd (ρ : Γ →* G) (e : HolLift ρ) :
    (holLiftEquiv ρ e).1.2 = θSingleObjEquiv Γ e.1.2 := rfl

/-! ### The exact sequence `1 → C_G(im ρ) → E_ρ → H_ρ → 1` -/

/-- The projection `E_ρ →* Aut(Γ)`, `(k, α) ↦ α` (paper `prop:holonomy`). -/
def EρProj (ρ : Γ →* G) : Eρ ρ →* MulAut Γ :=
  (MonoidHom.snd G (MulAut Γ)).comp (Eρ ρ).subtype

/-- `EρProj` unfolded (paper `prop:holonomy`). -/
@[simp] theorem EρProj_apply (ρ : Γ →* G) (e : Eρ ρ) : EρProj ρ e = e.1.2 := rfl

/-- The image of the projection `E_ρ → Aut(Γ)` is `H_ρ` (paper `prop:holonomy`). -/
theorem EρProj_range (ρ : Γ →* G) : (EρProj ρ).range = Hρ ρ := by
  ext α
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.1.1, e.2⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨(k, α), hk⟩, rfl⟩

/-- The projection corestricted to `H_ρ` (paper `prop:holonomy`). -/
def EρToHρ (ρ : Γ →* G) : Eρ ρ →* Hρ ρ :=
  (EρProj ρ).codRestrict (Hρ ρ) (fun e => ⟨e.1.1, e.2⟩)

/-- `EρToHρ` unfolded (paper `prop:holonomy`). -/
@[simp] theorem EρToHρ_apply_coe (ρ : Γ →* G) (e : Eρ ρ) : (EρToHρ ρ e : MulAut Γ) = e.1.2 :=
  rfl

/-- The corestricted projection `E_ρ → H_ρ` is surjective (paper `prop:holonomy`). -/
theorem EρToHρ_surjective (ρ : Γ →* G) : Function.Surjective (EρToHρ ρ) := by
  rintro ⟨α, k, hk⟩
  exact ⟨⟨(k, α), hk⟩, rfl⟩

/-- The kernels of the projection and of its corestriction agree (paper `prop:holonomy`). -/
theorem EρToHρ_ker (ρ : Γ →* G) : (EρToHρ ρ).ker = (EρProj ρ).ker :=
  MonoidHom.ker_codRestrict _ _ _

/-- The inclusion `C_G(im ρ) →* E_ρ`, `k ↦ (k, id)` (paper `prop:holonomy`). -/
def centralizerToEρ (ρ : Γ →* G) : Subgroup.centralizer (ρ.range : Set G) →* Eρ ρ where
  toFun k := ⟨(k.1, 1), fun γ => by
    show ρ γ = k.1 * ρ γ * k.1⁻¹
    rw [← Subgroup.mem_centralizer_iff.mp k.2 (ρ γ) (MonoidHom.mem_range.mpr ⟨γ, rfl⟩),
      mul_inv_cancel_right]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `centralizerToEρ` is injective (paper `prop:holonomy`, exactness at `C_G(im ρ)`). -/
theorem centralizerToEρ_injective (ρ : Γ →* G) : Function.Injective (centralizerToEρ ρ) :=
  fun _ _ h => Subtype.ext (congrArg (fun e : Eρ ρ => e.1.1) h)

/-- The kernel of the projection `E_ρ → Aut(Γ)` is the image of `C_G(im ρ)`
    (paper `prop:holonomy`, exactness at `E_ρ`). -/
theorem centralizerToEρ_range (ρ : Γ →* G) : (centralizerToEρ ρ).range = (EρProj ρ).ker := by
  ext e
  rw [MonoidHom.mem_range, MonoidHom.mem_ker, EρProj_apply]
  constructor
  · rintro ⟨k, rfl⟩
    rfl
  · intro he
    refine ⟨⟨e.1.1, Subgroup.mem_centralizer_iff.mpr ?_⟩, ?_⟩
    · intro h hh
      obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hh
      have hγ := e.2 γ
      rw [he, MulAut.one_apply] at hγ
      calc ρ γ * e.1.1 = e.1.1 * ρ γ * e.1.1⁻¹ * e.1.1 := by rw [← hγ]
        _ = e.1.1 * ρ γ := by group
    · apply Subtype.ext
      exact Prod.ext rfl he.symm

/-- The kernel of the projection `E_ρ → Aut(Γ)` is the holonomy centralizer `C_G(im ρ)`
    (paper `prop:holonomy`). -/
noncomputable def EρProjKerEquiv (ρ : Γ →* G) :
    (EρProj ρ).ker ≃* Subgroup.centralizer (ρ.range : Set G) :=
  (MulEquiv.subgroupCongr (centralizerToEρ_range ρ)).symm.trans
    (MonoidHom.ofInjective (centralizerToEρ_injective ρ)).symm

/-- The holonomy-controlled extension `1 → C_G(im ρ) → E_ρ → H_ρ → 1` is exact
    (paper `prop:holonomy`). -/
theorem holonomy_exact (ρ : Γ →* G) :
    Function.Injective (centralizerToEρ ρ) ∧ (centralizerToEρ ρ).range = (EρToHρ ρ).ker ∧
      Function.Surjective (EρToHρ ρ) :=
  ⟨centralizerToEρ_injective ρ, (centralizerToEρ_range ρ).trans (EρToHρ_ker ρ).symm,
    EρToHρ_surjective ρ⟩

/-! ### Transfer to the lift group `HolLift ρ` -/

/-- The projection of the lift group to the base automorphism, `(F, A) ↦ A`
    (paper `prop:holonomy`, "the group of equivariant lifts preserving this transport"). -/
def holLiftProj (ρ : Γ →* G) : HolLift ρ →* StrictAut (SingleObj Γ) :=
  (MonoidHom.snd _ _).comp (HolLift ρ).subtype

/-- `holLiftProj` unfolded (paper `prop:holonomy`). -/
@[simp] theorem holLiftProj_apply (ρ : Γ →* G) (e : HolLift ρ) : holLiftProj ρ e = e.1.2 := rfl

/-- Under `holLiftEquiv`, the projection `E_ρ → Aut(Γ)` is the lift-group projection followed by
    `θSingleObjEquiv` (paper `prop:holonomy`). -/
theorem EρProj_holLiftEquiv (ρ : Γ →* G) (e : HolLift ρ) :
    EρProj ρ (holLiftEquiv ρ e) = θSingleObjEquiv Γ (holLiftProj ρ e) := rfl

/-- The inclusion `C_G(im ρ) →* HolLift ρ`, `k ↦` the lift `g ↦ k g` over the identity
    (paper `prop:holonomy`). -/
noncomputable def centralizerToHolLift (ρ : Γ →* G) :
    Subgroup.centralizer (ρ.range : Set G) →* HolLift ρ :=
  (holLiftEquiv ρ).symm.toMonoidHom.comp (centralizerToEρ ρ)

/-- `centralizerToHolLift` unfolded through `holLiftEquiv` (paper `prop:holonomy`). -/
theorem centralizerToHolLift_apply (ρ : Γ →* G) (k : Subgroup.centralizer (ρ.range : Set G)) :
    centralizerToHolLift ρ k = (holLiftEquiv ρ).symm (centralizerToEρ ρ k) := rfl

/-- `centralizerToHolLift` is injective (paper `prop:holonomy`). -/
theorem centralizerToHolLift_injective (ρ : Γ →* G) :
    Function.Injective (centralizerToHolLift ρ) :=
  (holLiftEquiv ρ).symm.injective.comp (centralizerToEρ_injective ρ)

/-- A lift lies over the identity iff its image in `E_ρ` lies over the identity
    (paper `prop:holonomy`). -/
theorem holLiftProj_eq_one_iff (ρ : Γ →* G) (e : HolLift ρ) :
    holLiftProj ρ e = 1 ↔ EρProj ρ (holLiftEquiv ρ e) = 1 := by
  rw [EρProj_holLiftEquiv, map_eq_one_iff _ (θSingleObjEquiv Γ).injective]

/-- The lifts over the identity are exactly the image of `C_G(im ρ)`
    (paper `prop:holonomy`, exactness at the lift group). -/
theorem centralizerToHolLift_range (ρ : Γ →* G) :
    (centralizerToHolLift ρ).range = (holLiftProj ρ).ker := by
  ext e
  rw [MonoidHom.mem_ker, holLiftProj_eq_one_iff, ← MonoidHom.mem_ker, ← centralizerToEρ_range,
    MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [centralizerToHolLift_apply, MulEquiv.apply_symm_apply]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [centralizerToHolLift_apply, hk, MulEquiv.symm_apply_apply]

/-- The image of the lift-group projection is `θ⁻¹(H_ρ)`: a strict base automorphism lifts iff
    its induced automorphism of `Γ` lies in `H_ρ` (paper `prop:holonomy`). -/
theorem holLiftProj_range (ρ : Γ →* G) :
    (holLiftProj ρ).range = (Hρ ρ).comap (θSingleObjEquiv Γ).toMonoidHom := by
  ext A
  rw [MonoidHom.mem_range, Subgroup.mem_comap]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨(holLiftEquiv ρ e).1.1, (holLiftEquiv ρ e).2⟩
  · rintro ⟨k, hk⟩
    refine ⟨(holLiftEquiv ρ).symm ⟨(k, θSingleObjEquiv Γ A), hk⟩, ?_⟩
    apply (θSingleObjEquiv Γ).injective
    rw [← EρProj_holLiftEquiv, MulEquiv.apply_symm_apply]
    rfl

/-- The holonomy-controlled extension at the level of the lift group (paper `prop:holonomy`):
    `1 → C_G(im ρ) → HolLift ρ → θ⁻¹(H_ρ) → 1` is exact. -/
theorem holLift_exact (ρ : Γ →* G) :
    Function.Injective (centralizerToHolLift ρ) ∧
      (centralizerToHolLift ρ).range = (holLiftProj ρ).ker ∧
      (holLiftProj ρ).range = (Hρ ρ).comap (θSingleObjEquiv Γ).toMonoidHom :=
  ⟨centralizerToHolLift_injective ρ, centralizerToHolLift_range ρ, holLiftProj_range ρ⟩

/-- The kernel of the lift-group projection is the holonomy centralizer `C_G(im ρ)`
    (paper `prop:holonomy`). -/
noncomputable def holLiftProjKerEquiv (ρ : Γ →* G) :
    (holLiftProj ρ).ker ≃* Subgroup.centralizer (ρ.range : Set G) :=
  (MulEquiv.subgroupCongr (centralizerToHolLift_range ρ)).symm.trans
    (MonoidHom.ofInjective (centralizerToHolLift_injective ρ)).symm

/-- A lift over the identity with object map `g ↦ k g` preserves the transport exactly when
    `k ∈ C_G(im ρ)` (paper `sec:holonomy`, "or equivalently `k ∈ C_G(im ρ)`"). -/
theorem holLiftAut_one_mem_iff (ρ : Γ →* G) (k : G) :
    (holLiftAut k (1 : MulAut Γ), holBaseAut (1 : MulAut Γ)) ∈ HolLift ρ ↔
      k ∈ Subgroup.centralizer (ρ.range : Set G) := by
  constructor
  · intro h
    have hE := IsHolLift.mem_Eρ (ρ := ρ) (A := holBaseAut 1) h
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hr
    have hγ : ρ ((θSingleObjEquiv Γ (holBaseAut 1)) γ) = (k * 1) * ρ γ * (k * 1)⁻¹ := hE γ
    rw [θSingleObjEquiv_holBaseAut, MulAut.one_apply, mul_one] at hγ
    calc ρ γ * k = k * ρ γ * k⁻¹ * k := by rw [← hγ]
      _ = k * ρ γ := by group
  · intro hk
    exact holLiftAut_mem (centralizerToEρ ρ ⟨k, hk⟩).2

/-! ### Special case: trivial `ρ` -/

/-- For trivial `ρ` the transport is the product-model one, `γ^* (*, g) = (*, g)`
    (paper `sec:holonomy`, "trivial `ρ` recovers the untwisted product classification"). -/
theorem holReind_one {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) :
    holReind (1 : Γ →* G) γ y = (s, y.2) := by
  apply holTotal_ext
  show ((1 : Γ →* G) γ)⁻¹ * y.2.pt = y.2.pt
  simp

/-- For trivial `ρ`, `E_ρ` is all of `G × Aut(Γ)` (paper `sec:holonomy`). -/
theorem Eρ_one : Eρ (1 : Γ →* G) = ⊤ :=
  eq_top_iff.mpr fun e _ γ => by simp

/-- For trivial `ρ`, `H_ρ` is all of `Aut(Γ)` (paper `sec:holonomy`). -/
theorem Hρ_one : Hρ (1 : Γ →* G) = ⊤ :=
  eq_top_iff.mpr fun _ _ => ⟨1, fun γ => by simp⟩

/-- For trivial `ρ`, the holonomy centralizer is all of `G` (paper `sec:holonomy`). -/
theorem centralizer_range_one : Subgroup.centralizer ((1 : Γ →* G).range : Set G) = ⊤ :=
  eq_top_iff.mpr fun g _ => Subgroup.mem_centralizer_iff.mpr fun h hh => by
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hh
    simp

/-- For trivial `ρ` the lift group is the untwisted product `G × Aut(Γ)`
    (paper `sec:holonomy`). -/
noncomputable def holLiftEquivTrivial : HolLift (1 : Γ →* G) ≃* G × MulAut Γ :=
  (holLiftEquiv 1).trans ((MulEquiv.subgroupCongr Eρ_one).trans Subgroup.topEquiv)

end Lifts

/-! ## Special case: a transposition in `S₃` (paper `sec:holonomy`, first example) -/

section S3

/-- `ρ : C₂ →* S₃` sending the generator to the transposition `(0 1)`
    (paper `sec:holonomy`, example after `prop:holonomy`). -/
def holS3ρ : Multiplicative (ZMod 2) →* Equiv.Perm (Fin 3) where
  toFun a := if a = 1 then 1 else Equiv.swap 0 1
  map_one' := by decide
  map_mul' := by decide

/-- `holS3ρ` sends the generator to `(0 1)` (paper `sec:holonomy`). -/
theorem holS3ρ_ofAdd_one : holS3ρ (Multiplicative.ofAdd 1) = Equiv.swap 0 1 := by decide

/-- `holS3ρ` is injective (paper `sec:holonomy`). -/
theorem holS3ρ_injective : Function.Injective holS3ρ := by
  intro a b
  revert a b
  decide

/-- The centralizer of the image of the transposition is the image itself
    (paper `sec:holonomy`). -/
theorem holS3_centralizer_eq :
    Subgroup.centralizer (holS3ρ.range : Set (Equiv.Perm (Fin 3))) = holS3ρ.range := by
  ext g
  rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_range]
  constructor
  · intro hg
    have h := hg (Equiv.swap 0 1) (MonoidHom.mem_range.mpr ⟨_, holS3ρ_ofAdd_one⟩)
    clear hg
    revert g
    decide
  · rintro ⟨a, rfl⟩ h hh
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hh
    rw [← map_mul, ← map_mul, mul_comm]

/-- `C_{S₃}(im ρ) ≃* C₂` for `ρ` the transposition (paper `sec:holonomy`). -/
noncomputable def holS3CentralizerEquiv :
    Subgroup.centralizer (holS3ρ.range : Set (Equiv.Perm (Fin 3))) ≃* Multiplicative (ZMod 2) :=
  (MulEquiv.subgroupCongr holS3_centralizer_eq).trans (MonoidHom.ofInjective holS3ρ_injective).symm

/-- `C_{S₃}(im ρ)` is a proper subgroup of `S₃` (paper `sec:holonomy`). -/
theorem holS3_centralizer_ne_top :
    Subgroup.centralizer (holS3ρ.range : Set (Equiv.Perm (Fin 3))) ≠ ⊤ := by
  intro htop
  have h : Equiv.swap (1 : Fin 3) 2 ∈
      Subgroup.centralizer (holS3ρ.range : Set (Equiv.Perm (Fin 3))) := htop ▸ Subgroup.mem_top _
  have h2 := Subgroup.mem_centralizer_iff.mp h (Equiv.swap 0 1)
    (MonoidHom.mem_range.mpr ⟨_, holS3ρ_ofAdd_one⟩)
  revert h2
  decide

/-- The kernel of `E_ρ → Aut(C₂)` for the `S₃` transposition is `C₂` (paper `sec:holonomy`). -/
noncomputable def holS3KerEquiv : (EρProj holS3ρ).ker ≃* Multiplicative (ZMod 2) :=
  (EρProjKerEquiv holS3ρ).trans holS3CentralizerEquiv

end S3

/-! ## Special case: `ρ = id` and the nonsplit `Q₈` extension (paper `sec:holonomy`) -/

section IdCase

variable (G : Type v) [Group G]

/-- For `ρ = id`, `E_ρ = {(q, Ad_q)}` (paper `sec:holonomy`, `Q₈` example). -/
theorem mem_Eρ_id_iff (e : G × MulAut G) : e ∈ Eρ (MonoidHom.id G) ↔ e.2 = MulAut.conj e.1 := by
  constructor
  · intro h
    ext γ
    exact h γ
  · intro h γ
    rw [h]
    rfl

/-- For `ρ = id`, `E_ρ ≃* G` via `(q, Ad_q) ↦ q` (paper `sec:holonomy`, `Q₈` example). -/
def EρIdEquiv : Eρ (MonoidHom.id G) ≃* G where
  toFun e := e.1.1
  invFun k := ⟨(k, MulAut.conj k), (mem_Eρ_id_iff G _).mpr rfl⟩
  left_inv e := by
    apply Subtype.ext
    exact Prod.ext rfl ((mem_Eρ_id_iff G _).mp e.2).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- For `ρ = id`, `H_ρ = Inn(G)`, the range of `MulAut.conj` (paper `sec:holonomy`). -/
theorem Hρ_id : Hρ (MonoidHom.id G) = (MulAut.conj : G →* MulAut G).range := by
  ext α
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, MulEquiv.ext fun γ => (hk γ).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, fun γ => rfl⟩

end IdCase

section Q8

/-- The quotient map `Q₈ →* C₂ × C₂`, `a i ↦ (i mod 2, 0)`, `xa i ↦ (i mod 2, 1)`, with
    kernel the center `{±1}` (paper `sec:holonomy`, `Q₈` example). -/
def holQ8Quot : QuaternionGroup 2 →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) where
  toFun
    | .a i => (Multiplicative.ofAdd (i.val : ZMod 2), 1)
    | .xa i => (Multiplicative.ofAdd (i.val : ZMod 2), Multiplicative.ofAdd 1)
  map_one' := by decide
  map_mul' := by decide

/-- `holQ8Quot` is surjective (paper `sec:holonomy`). -/
theorem holQ8Quot_surjective : Function.Surjective holQ8Quot := by
  intro b
  revert b
  decide

/-- The kernel of `Ad : Q₈ →* Aut(Q₈)` equals the kernel of `holQ8Quot` (paper `sec:holonomy`). -/
theorem holQ8_ker_conj :
    (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).ker = holQ8Quot.ker := by
  ext q
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, DFunLike.ext_iff]
  simp only [MulAut.conj_apply, MulAut.one_apply]
  revert q
  decide

/-- For `Γ = G = Q₈` and `ρ = id`: `E_ρ ≃* Q₈` (paper `sec:holonomy`). -/
def holQ8EρEquiv : Eρ (MonoidHom.id (QuaternionGroup 2)) ≃* QuaternionGroup 2 :=
  EρIdEquiv (QuaternionGroup 2)

/-- For `Γ = G = Q₈` and `ρ = id`: `H_ρ = Inn(Q₈) ≃* C₂ × C₂` (paper `sec:holonomy`). -/
noncomputable def holQ8HρEquiv :
    Hρ (MonoidHom.id (QuaternionGroup 2)) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  (MulEquiv.subgroupCongr (Hρ_id (QuaternionGroup 2))).trans
    ((QuotientGroup.quotientKerEquivRange MulAut.conj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq holQ8_ker_conj).trans
        (QuotientGroup.quotientKerEquivOfSurjective holQ8Quot holQ8Quot_surjective)))

/-- The `Q₈` extension `1 → C₂ → Q₈ → C₂ × C₂ → 1` has NO group-homomorphic section: there is
    no monoid hom `σ : H_ρ →* E_ρ` with `proj ∘ σ = id` (paper `sec:holonomy`, `Q₈` example). -/
theorem holQ8_no_section :
    ¬ ∃ σ : Hρ (MonoidHom.id (QuaternionGroup 2)) →* Eρ (MonoidHom.id (QuaternionGroup 2)),
      (EρToHρ (MonoidHom.id (QuaternionGroup 2))).comp σ = MonoidHom.id _ := by
  rintro ⟨σ, hσ⟩
  let i : QuaternionGroup 2 := QuaternionGroup.a 1
  let αi : Hρ (MonoidHom.id (QuaternionGroup 2)) := ⟨MulAut.conj i, i, fun _ => rfl⟩
  have hsq : αi * αi = 1 := by
    apply Subtype.ext
    show MulAut.conj i * MulAut.conj i = 1
    rw [← map_mul]
    ext γ
    show (i * i) * γ * (i * i)⁻¹ = γ
    revert γ
    decide
  have hproj : (σ αi).1.2 = MulAut.conj i :=
    congrArg Subtype.val (DFunLike.congr_fun hσ αi)
  have hq : (σ αi).1.1 * (σ αi).1.1 = 1 := by
    have h := congrArg (fun e : Eρ (MonoidHom.id (QuaternionGroup 2)) => e.1.1)
      (show σ αi * σ αi = 1 by rw [← map_mul, hsq, map_one])
    exact h
  have h1 := (σ αi).2 (QuaternionGroup.xa 0)
  rw [hproj] at h1
  simp only [MonoidHom.id_apply, MulAut.conj_apply] at h1
  generalize (σ αi).1.1 = q at hq h1
  revert q
  decide

/-- Every lift in `E_ρ ≃ Q₈` of a nonidentity element of `H_ρ` has order four
    (paper `sec:holonomy`, `Q₈` example). -/
theorem holQ8_orderOf_lift (e : Eρ (MonoidHom.id (QuaternionGroup 2)))
    (he : EρToHρ (MonoidHom.id (QuaternionGroup 2)) e ≠ 1) : orderOf e = 4 := by
  rw [← MulEquiv.orderOf_eq (holQ8EρEquiv) e]
  have hne : e.1.2 ≠ 1 := fun h => he (Subtype.ext h)
  rw [(mem_Eρ_id_iff _ _).mp e.2] at hne
  have hne' : ∃ γ, e.1.1 * γ * e.1.1⁻¹ ≠ γ := by
    by_contra hcon
    exact hne (MulEquiv.ext fun γ => by
      by_contra h
      exact hcon ⟨γ, h⟩)
  show orderOf e.1.1 = 2 ^ (1 + 1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ q : QuaternionGroup 2, (∃ γ, q * γ * q⁻¹ ≠ γ) →
      ¬ q ^ 2 ^ 1 = 1 ∧ q ^ 2 ^ (1 + 1) = 1 := by
    decide
  obtain ⟨h1, h2⟩ := key e.1.1 hne'
  exact orderOf_eq_prime_pow h1 h2

/-- The inclusion `C₂ →* Q₈` onto the center `{±1}` (paper `sec:holonomy`, `Q₈` example). -/
def holQ8Center : Multiplicative (ZMod 2) →* QuaternionGroup 2 where
  toFun a := if a = 1 then 1 else QuaternionGroup.a 2
  map_one' := by decide
  map_mul' := by decide

/-- `holQ8Center` is injective (paper `sec:holonomy`). -/
theorem holQ8Center_injective : Function.Injective holQ8Center := by
  intro a b
  revert a b
  decide

/-- The holonomy centralizer for `ρ = id` on `Q₈` is the center `{±1}` (paper `sec:holonomy`). -/
theorem holQ8_centralizer_eq :
    Subgroup.centralizer ((MonoidHom.id (QuaternionGroup 2)).range : Set (QuaternionGroup 2))
      = holQ8Center.range := by
  ext g
  rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_range]
  constructor
  · intro hg
    have h : ∀ x : QuaternionGroup 2, x * g = g * x := fun x =>
      hg x (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
    clear hg
    revert g
    decide
  · rintro ⟨a, rfl⟩ x -
    revert a x
    decide

/-- For `ρ = id` on `Q₈`, the kernel `C_{Q₈}(im ρ)` of the extension is `C₂`
    (paper `sec:holonomy`, the sequence `1 → C₂ → Q₈ → C₂ × C₂ → 1`). -/
noncomputable def holQ8CentralizerEquiv :
    Subgroup.centralizer ((MonoidHom.id (QuaternionGroup 2)).range : Set (QuaternionGroup 2))
      ≃* Multiplicative (ZMod 2) :=
  (MulEquiv.subgroupCongr holQ8_centralizer_eq).trans
    (MonoidHom.ofInjective holQ8Center_injective).symm

/-- For `ρ = id` on `Q₈`, the kernel of `E_ρ → Aut(Q₈)` is `C₂` (paper `sec:holonomy`). -/
noncomputable def holQ8KerEquiv :
    (EρProj (MonoidHom.id (QuaternionGroup 2))).ker ≃* Multiplicative (ZMod 2) :=
  (EρProjKerEquiv _).trans holQ8CentralizerEquiv

end Q8
