import ObserverEquivariance.NormalForm

/-!
# Local multipliers and the coordinate description of lifts (paper `lem:local`)

Paper labels covered in this file:

* `lem:local` (Coordinate description of lifts), in full:
  - every equivariant functor `F` covering `A` (`F ⋙ p = p ⋙ A`) has the object function
    `F(b_s · g) = b_{A s} · (k(s) g)` with the multiplier `k = liftMultiplier d F`,
    `k(s) = g_{F(b_s)}` (`lift_obj_eq`, `lift_obj_act_base`), and `k` is UNIQUE
    (`multiplier_unique`);
  - in the product normal form the lift IS the functor `(s,g) ↦ (A s, k(s) g)`, strictly and on
    arrows (`normalForm_lift_eq`);
  - the morphism map is determined by the covering equation (`lift_map_eq_liftOver`,
    `lift_eq_of_obj_eq`);
  - transport preservation is equivalent to `k(s) = k(t)` for every `u : s ⟶ t`
    (`preservesCleavage_iff_multiplier`);
  - conversely every `k : S → G` defines an equivariant functor over `A`
    (`liftByMultiplier`, `liftByMultiplier_isGEquivariant`, `liftByMultiplier_covers`,
    `liftMultiplier_liftByMultiplier`), which preserves transport iff `k` is constant along
    arrows (`liftByMultiplier_preservesCleavage_iff`); for a strict base automorphism `A` it has
    the strict inverse with object function `(t,h) ↦ (A⁻¹ t, k(A⁻¹ t)⁻¹ h)`
    (`liftByMultiplier_comp_inv`, `liftByMultiplier_inv_comp`), so a locally constant `k` gives an
    element of `AutBoxG d` (`autBoxGOfMultiplier`, `autBoxGOverOfMultiplier`), and every element
    of `AutBoxG d` arises this way (`eq_autBoxGOfMultiplier`).  No connectedness is used here.
* The paragraph after `lem:local` (section formulation on a connected base): for `F`
  equivariant over `A` and `S` connected, `F` preserves transport iff
  `∃ c, ∀ s, F(b_s) = b_{A s} · c` (`preservesCleavage_iff_exists_base_obj`) iff
  `∃ c, B ⋙ F = A ⋙ B ⋙ R_c` as functors (`preservesCleavage_iff_exists_section`; the paper's
  operator-order `FB = R_c B A`).  The object equations imply the functor equation by
  faithfulness without connectedness (`sectionFunctor_comp_eq_of_obj`).
* The canonical-lift paragraph: `k = 1` gives `liftFunctor` (`liftByMultiplier_one`) and a
  constant `k = a` gives `Λ_a Ã` (`liftByMultiplier_const`, Lean order `Ã ⋙ Λ_a`).
* `thm:strict` (proof): on a connected base every admissible lift has a unique factorization
  `Λ_a Ã` (`exists_unique_eq_liftFunctor_comp_Λ`).
* `thm:twisted` (proof): the twisted coordinate description `F(s,g) = (A s, k(s) θ_A(g))`
  (`lift_obj_eq_twisted`, `multiplier_unique_twisted`, `normalForm_lift_eq_twisted`), the same
  transport criterion (`preservesCleavage_iff_multiplier_twisted`), the converse
  (`liftByMultiplierθ`) with strict inverse built from `A⁻¹` and `θ_A⁻¹`
  (`liftByMultiplierθ_comp_inv`, `liftByMultiplierθ_inv_comp`, `autBoxGθOverOfMultiplier`), and
  the unique factorization `Λ_a Ã_θ` (`exists_unique_eq_liftFunctorθ_comp_Λ`).

Conventions: `F ⋙ G` is "first `F`, then `G`".  The object form, local constancy and global
constancy used in the proof of `Core.rigidity` are stated here as public lemmas
(`lift_obj_eq`, `liftMultiplier_eq_of_hom`, `liftMultiplier_const`).
-/

open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}

open NormalForm

/-! ## 1. The multiplier and the object formula (paper `lem:local`) -/

/-- The local multiplier of an endofunctor `F` of `O`: `k(s) = g_{F(b_s)}`, the coordinate of the
    image of the basepoint (paper `lem:local`, `F(s,1) = (A(s), k(s))`). -/
def liftMultiplier (d : OEData G p) (F : O ⥤ O) (s : S) : G :=
  d.coord (F.obj (d.base s))

namespace LocalLifts

/-- `p(b_s · g) = s` (helper for paper `lem:local`). -/
theorem p_act_base (d : OEData G p) (s : S) (g : G) : p.obj (d.act (d.base s) g) = s :=
  (d.p_act _ _).trans (d.p_base _)

/-- `g_{b_s} = 1` (helper for paper `lem:local`). -/
theorem coord_base_one (d : OEData G p) (s : S) : d.coord (d.base s) = 1 := by
  have h := d.coord_base s 1; rwa [d.act_one] at h

/-- Clean-endpoint form of the covering equation on objects (helper for paper `lem:local`). -/
theorem covers_obj {F : O ⥤ O} {A : S ⥤ S} (hc : F ⋙ p = p ⋙ A) (x : O) :
    p.obj (F.obj x) = A.obj (p.obj x) :=
  Functor.congr_obj hc x

/-- Clean-endpoint form of the covering equation on arrows (helper for paper `lem:local`). -/
theorem covers_map {F : O ⥤ O} {A : S ⥤ S} (hc : F ⋙ p = p ⋙ A) {x y : O} (f : x ⟶ y) :
    p.map (F.map f)
      = eqToHom (covers_obj hc x) ≫ A.map (p.map f) ≫ eqToHom (covers_obj hc y).symm :=
  Functor.congr_hom hc f

/-- `R_c ⋙ p = p` for normalized data (helper for the section formulation after paper
    `lem:local`). -/
theorem actFunctor_comp_p (d : OEData G p) (c : G) : d.actFunctor c ⋙ p = p := by
  rw [← d.toMinSpec_actFunctor]; exact d.toMinSpec.actFunctor_comp_p c

/-- Two functors `C ⥤ O` with equal objects and equal composites with `p` are equal, by
    faithfulness of `p` (paper `lem:local`: "its morphism map is uniquely determined by the
    covering equation"; the section formulation "by faithfulness"). -/
theorem functor_ext_of_comp_p (d : OEData G p) {C : Type*} [Category C] {F₁ F₂ : C ⥤ O}
    (hobj : ∀ X, F₁.obj X = F₂.obj X) (hcomp : F₁ ⋙ p = F₂ ⋙ p) : F₁ = F₂ := by
  haveI := d.p_faithful
  refine CategoryTheory.Functor.ext hobj (fun X Y f => ?_)
  apply p.map_injective
  rw [p.map_comp, p.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hcomp f

end LocalLifts

open LocalLifts

/-- A functor covering `A` sends the basepoint `b_s` to `b_{A s} · k(s)` (paper `lem:local`,
    `F(s,1) = (A(s), k(s))`).  Only the covering equation is used. -/
theorem lift_obj_base (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S} (hc : F ⋙ p = p ⋙ A) (s : S) :
    F.obj (d.base s) = d.act (d.base (A.obj s)) (liftMultiplier d F s) := by
  conv_lhs => rw [← d.base_coord (F.obj (d.base s))]
  unfold liftMultiplier
  rw [covers_obj hc, d.p_base]

/-- Object form of an equivariant lift (paper `lem:local`): if `F` is `G`-equivariant and covers
    `A`, then `F(x) = b_{A(p x)} · (k(p x) g_x)`, i.e. `F(s,g) = (A(s), k(s) g)`. -/
theorem lift_obj_eq (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S} (hF : IsGEquivariant d F)
    (hc : F ⋙ p = p ⋙ A) (x : O) :
    F.obj x = d.act (d.base (A.obj (p.obj x))) (liftMultiplier d F (p.obj x) * d.coord x) := by
  have e1 : F.obj x = d.act (F.obj (d.base (p.obj x))) (d.coord x) := by
    conv_lhs => rw [← d.base_coord x]
    exact hF _ _
  rw [e1, lift_obj_base d hc, d.act_mul]

/-- Object form on the normal-form coordinates (paper `lem:local`):
    `F(b_s · g) = b_{A s} · (k(s) g)`. -/
theorem lift_obj_act_base (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S} (hF : IsGEquivariant d F)
    (hc : F ⋙ p = p ⋙ A) (s : S) (g : G) :
    F.obj (d.act (d.base s) g) = d.act (d.base (A.obj s)) (liftMultiplier d F s * g) := by
  rw [hF, lift_obj_base d hc, d.act_mul]

/-- Uniqueness of the multiplier (paper `lem:local`, "a unique object function"): any `k` with
    `F(x) = b_{A(p x)} · (k(p x) g_x)` for all `x` is `liftMultiplier d F`. -/
theorem multiplier_unique (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S} {k : S → G}
    (hk : ∀ x, F.obj x = d.act (d.base (A.obj (p.obj x))) (k (p.obj x) * d.coord x)) :
    k = liftMultiplier d F := by
  funext s
  have h := hk (d.base s)
  rw [d.p_base] at h
  unfold liftMultiplier
  rw [h, d.coord_base, coord_base_one, mul_one]

/-! ## 2. The morphism map is determined (paper `lem:local`) -/

/-- The morphism map of a functor covering `A` is the unique lift of `A(p f)` between the image
    objects (paper `lem:local`: "fullness and faithfulness give exactly one possible image over
    `Au`"). -/
theorem lift_map_eq_liftOver (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S} (hc : F ⋙ p = p ⋙ A)
    {x y : O} (f : x ⟶ y) :
    F.map f = d.toMinSpec.liftOver (A.map (p.map f)) (covers_obj hc x) (covers_obj hc y) :=
  (d.toMinSpec.eq_liftOver_iff _ _ _ _).2 (covers_map hc f)

/-- Two functors covering the same `A` with the same object function are equal (paper
    `lem:local`: "its morphism map is uniquely determined by the covering equation"). -/
theorem lift_eq_of_obj_eq (d : OEData G p) {F₁ F₂ : O ⥤ O} {A : S ⥤ S}
    (h₁ : F₁ ⋙ p = p ⋙ A) (h₂ : F₂ ⋙ p = p ⋙ A) (hobj : ∀ x, F₁.obj x = F₂.obj x) : F₁ = F₂ :=
  funct_ext d hobj (h₁.trans h₂.symm)

/-! ## 3. The transport criterion (paper `lem:local`) -/

/-- Local constancy of the multiplier (paper `lem:local`, `thm:strict` proof): a
    transport-preserving functor over `A` has `k(s) = k(t)` for every `u : s ⟶ t`. -/
theorem liftMultiplier_eq_of_hom (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S}
    (pc : PreservesCleavage d F A) {s t : S} (u : s ⟶ t) :
    liftMultiplier d F s = liftMultiplier d F t := by
  have key := pc.src u (d.base t) (d.p_base t)
  rw [d.reind_base, d.reind_eq, lift_obj_base d pc.covers s] at key
  exact d.act_free _ _ _ key

/-- Global constancy on a connected base (paper `thm:strict` proof: "constant along every
    morphism, and hence along every zigzag"). -/
theorem liftMultiplier_const (d : OEData G p) [IsConnected S] {F : O ⥤ O} {A : S ⥤ S}
    (pc : PreservesCleavage d F A) (s t : S) :
    liftMultiplier d F s = liftMultiplier d F t :=
  constant_of_preserves_morphisms (liftMultiplier d F)
    (fun _ _ u => liftMultiplier_eq_of_hom d pc u) s t

/-- Transport criterion (paper `lem:local`): an equivariant functor covering `A` preserves the
    chosen transport iff its multiplier satisfies `k(s) = k(t)` for every `u : s ⟶ t`. -/
theorem preservesCleavage_iff_multiplier (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S}
    (hF : IsGEquivariant d F) (hc : F ⋙ p = p ⋙ A) :
    PreservesCleavage d F A ↔
      ∀ {s t : S} (_ : s ⟶ t), liftMultiplier d F s = liftMultiplier d F t := by
  constructor
  · intro pc s t u
    exact liftMultiplier_eq_of_hom d pc u
  · intro hk
    refine ⟨hc, ?_⟩
    intro s t u y hy
    rw [d.reind_eq, lift_obj_act_base d hF hc, d.reind_eq, lift_obj_eq d hF hc y, d.coord_base,
      hy, hk u]

/-! ## 4. The product normal form of a lift (paper `lem:local`) -/

/-- The product-model functor `(s,g) ↦ (A(s), k(s) g)`, `(u,*) ↦ (A u, *)` (paper `lem:local`). -/
def multiplierProductFunctor (A : S ⥤ S) (k : S → G) : S × Pair G ⥤ S × Pair G where
  obj X := (A.obj X.1, ⟨k X.1 * X.2.pt⟩)
  map f := (A.map f.1, ⟨⟩)
  map_id X := Prod.ext (A.map_id X.1) (Subsingleton.elim _ _)
  map_comp f g := Prod.ext (A.map_comp f.1 g.1) (Subsingleton.elim _ _)

/-- (paper `lem:local`) -/
@[simp] theorem multiplierProductFunctor_obj (A : S ⥤ S) (k : S → G) (s : S) (g : G) :
    (multiplierProductFunctor A k).obj (s, ⟨g⟩) = (A.obj s, ⟨k s * g⟩) := rfl

/-- In the product normal form, an equivariant lift over `A` IS the functor
    `(s,g) ↦ (A(s), k(s) g)` with `k = liftMultiplier d F`, as a strict equality of functors
    `M ⋙ F ⋙ N = (s,g) ↦ (A s, k(s) g)` (paper `lem:local`). -/
theorem normalForm_lift_eq (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S} (hF : IsGEquivariant d F)
    (hc : F ⋙ p = p ⋙ A) :
    normalFormFrom d ⋙ F ⋙ normalFormTo d = multiplierProductFunctor A (liftMultiplier d F) := by
  have hobj : ∀ X : S × Pair G,
      ((p.obj (F.obj (d.act (d.base X.1) X.2.pt)), ⟨d.coord (F.obj (d.act (d.base X.1) X.2.pt))⟩) :
        S × Pair G) = (A.obj X.1, ⟨liftMultiplier d F X.1 * X.2.pt⟩) := by
    intro X
    rw [lift_obj_act_base d hF hc, d.p_act, d.p_base, d.coord_base]
  fapply CategoryTheory.Functor.ext
  · exact hobj
  · intro X Y f
    have key : ((p.map (F.map (d.toMinSpec.liftOver f.1 (p_act_base d X.1 X.2.pt)
          (p_act_base d Y.1 Y.2.pt))), ⟨⟩) :
          ((p.obj (F.obj (d.act (d.base X.1) X.2.pt)),
            ⟨d.coord (F.obj (d.act (d.base X.1) X.2.pt))⟩) : S × Pair G) ⟶
          (p.obj (F.obj (d.act (d.base Y.1) Y.2.pt)),
            ⟨d.coord (F.obj (d.act (d.base Y.1) Y.2.pt))⟩))
        = eqToHom (hobj X) ≫
          ((A.map f.1, ⟨⟩) : ((A.obj X.1, ⟨liftMultiplier d F X.1 * X.2.pt⟩) : S × Pair G) ⟶
            (A.obj Y.1, ⟨liftMultiplier d F Y.1 * Y.2.pt⟩)) ≫ eqToHom (hobj Y).symm := by
      apply prodPairHom_ext
      simp only [prod_comp_fst, eqToHom_prod_fst, covers_map hc, MinSpec.p_map_liftOver,
        Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    exact key

/-! ## 5. The converse: every multiplier defines a lift (paper `lem:local`) -/

/-- The lift defined by a multiplier `k : S → G` over `A : S ⥤ S` (paper `lem:local`,
    "conversely every such `k` defines an admissible lift"): objects
    `x ↦ b_{A(p x)} · (k(p x) g_x)`, arrows the unique lift of `A(p f)`. -/
noncomputable def liftByMultiplier (d : OEData G p) (A : S ⥤ S) (k : S → G) : O ⥤ O where
  obj x := d.act (d.base (A.obj (p.obj x))) (k (p.obj x) * d.coord x)
  map {x y} f := d.toMinSpec.liftOver (A.map (p.map f))
    (d.p_liftObjθ A x (k (p.obj x) * d.coord x)) (d.p_liftObjθ A y (k (p.obj y) * d.coord y))
  map_id x := by simp
  map_comp f g := by simp

/-- (paper `lem:local`) -/
@[simp] theorem liftByMultiplier_obj (d : OEData G p) (A : S ⥤ S) (k : S → G) (x : O) :
    (liftByMultiplier d A k).obj x = d.act (d.base (A.obj (p.obj x))) (k (p.obj x) * d.coord x) :=
  rfl

/-- (paper `lem:local`) -/
theorem liftByMultiplier_map (d : OEData G p) (A : S ⥤ S) (k : S → G) {x y : O} (f : x ⟶ y) :
    (liftByMultiplier d A k).map f = d.toMinSpec.liftOver (A.map (p.map f))
      (d.p_liftObjθ A x (k (p.obj x) * d.coord x)) (d.p_liftObjθ A y (k (p.obj y) * d.coord y)) :=
  rfl

/-- The multiplier lift covers `A` (paper `lem:local`, `pF = Ap`). -/
theorem liftByMultiplier_covers (d : OEData G p) (A : S ⥤ S) (k : S → G) :
    liftByMultiplier d A k ⋙ p = p ⋙ A := by
  fapply CategoryTheory.Functor.ext
  · intro x; exact d.p_liftObjθ A x (k (p.obj x) * d.coord x)
  · intro x y f
    exact d.toMinSpec.p_map_liftOver _ (d.p_liftObjθ A x _) (d.p_liftObjθ A y _)

/-- The multiplier lift is `G`-equivariant (paper `lem:local`). -/
theorem liftByMultiplier_isGEquivariant (d : OEData G p) (A : S ⥤ S) (k : S → G) :
    IsGEquivariant d (liftByMultiplier d A k) := by
  intro x g
  simp only [liftByMultiplier_obj]
  rw [d.p_act, d.coord_act, d.act_mul, mul_assoc]

/-- The multiplier of `liftByMultiplier d A k` is `k` (paper `lem:local`). -/
theorem liftMultiplier_liftByMultiplier (d : OEData G p) (A : S ⥤ S) (k : S → G) :
    liftMultiplier d (liftByMultiplier d A k) = k := by
  funext s
  simp only [liftMultiplier, liftByMultiplier_obj]
  rw [d.coord_base, d.p_base, coord_base_one, mul_one]

/-- The multiplier lift preserves transport iff `k` is constant along every base arrow (paper
    `lem:local`). -/
theorem liftByMultiplier_preservesCleavage_iff (d : OEData G p) (A : S ⥤ S) (k : S → G) :
    PreservesCleavage d (liftByMultiplier d A k) A ↔ ∀ {s t : S} (_ : s ⟶ t), k s = k t := by
  rw [preservesCleavage_iff_multiplier d (liftByMultiplier_isGEquivariant d A k)
    (liftByMultiplier_covers d A k), liftMultiplier_liftByMultiplier]

/-- Every equivariant functor over `A` is the multiplier lift of its own multiplier
    (paper `lem:local`: object function `F(s,g) = (A s, k(s) g)` plus the determined arrow map). -/
theorem eq_liftByMultiplier (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S} (hF : IsGEquivariant d F)
    (hc : F ⋙ p = p ⋙ A) : F = liftByMultiplier d A (liftMultiplier d F) :=
  lift_eq_of_obj_eq d hc (liftByMultiplier_covers d A _) (lift_obj_eq d hF hc)

/-- The canonical lift is the multiplier lift with `k = 1` (paper, canonical-lift paragraph
    after `lem:local`). -/
theorem liftByMultiplier_one (d : OEData G p) (A : S ⥤ S) :
    liftByMultiplier d A 1 = liftFunctor d A :=
  lift_eq_of_obj_eq d (liftByMultiplier_covers d A 1) (lift_preservesCleavage d A).covers
    (fun x => by
      show d.act (d.base (A.obj (p.obj x))) ((1 : S → G) (p.obj x) * d.coord x)
        = d.act (d.base (A.obj (p.obj x))) (d.coord x)
      rw [Pi.one_apply, one_mul])

/-- A constant multiplier `k = a` gives `Λ_a Ã`, in Lean order `Ã ⋙ Λ_a` (paper `lem:local`,
    `thm:strict`). -/
theorem liftByMultiplier_const (d : OEData G p) (A : S ⥤ S) (a : G) :
    liftByMultiplier d A (fun _ => a) = liftFunctor d A ⋙ Λ d a := by
  refine lift_eq_of_obj_eq d (liftByMultiplier_covers d A _) ?_ (fun x => ?_)
  · rw [Functor.assoc, Λ_comp_p]; exact (lift_preservesCleavage d A).covers
  · show d.act (d.base (A.obj (p.obj x))) (a * d.coord x)
      = d.act (d.base (p.obj (d.act (d.base (A.obj (p.obj x))) (d.coord x))))
          (a * d.coord (d.act (d.base (A.obj (p.obj x))) (d.coord x)))
    rw [d.p_act, d.p_base, d.coord_base]

/-- The multiplier lift factors as a fiber translation by the object function `k` followed by
    the canonical lift: `liftByMultiplier d A k = ΛFun d k ⋙ liftFunctor d A` (paper `lem:local`). -/
theorem liftByMultiplier_eq_ΛFun_comp (d : OEData G p) (A : S ⥤ S) (k : S → G) :
    liftByMultiplier d A k = ΛFun d k ⋙ liftFunctor d A := by
  refine lift_eq_of_obj_eq d (liftByMultiplier_covers d A _) ?_ (fun x => ?_)
  · rw [Functor.assoc, (lift_preservesCleavage d A).covers, ← Functor.assoc, ΛFun_comp_p]
  · show d.act (d.base (A.obj (p.obj x))) (k (p.obj x) * d.coord x)
      = d.act (d.base (A.obj (p.obj (d.act (d.base (p.obj x)) (k (p.obj x) * d.coord x)))))
          (d.coord (d.act (d.base (p.obj x)) (k (p.obj x) * d.coord x)))
    rw [d.p_act, d.p_base, d.coord_base]

/-! ## 6. Strict inverse and the bundled lift (paper `lem:local`) -/

/-- Strict inverse, first half (paper `lem:local` proof, inverse object function
    `(t,h) ↦ (A⁻¹(t), k(A⁻¹(t))⁻¹ h)`): `F_k ⋙ F⁻¹ = 𝟭 O`. -/
theorem liftByMultiplier_comp_inv (d : OEData G p) (A : StrictAut S) (k : S → G) :
    liftByMultiplier d A.hom k ⋙ liftByMultiplier d A.inv (fun t => (k (A.inv.obj t))⁻¹)
      = 𝟭 O := by
  have hAA : ∀ s, A.inv.obj (A.hom.obj s) = s := fun s => Functor.congr_obj A.hom_inv_id s
  refine funct_ext d (fun x => ?_) ?_
  · show d.act (d.base (A.inv.obj (p.obj (d.act (d.base (A.hom.obj (p.obj x)))
          (k (p.obj x) * d.coord x)))))
        ((k (A.inv.obj (p.obj (d.act (d.base (A.hom.obj (p.obj x))) (k (p.obj x) * d.coord x)))))⁻¹
          * d.coord (d.act (d.base (A.hom.obj (p.obj x))) (k (p.obj x) * d.coord x))) = x
    rw [d.p_act, d.p_base, d.coord_base, hAA, inv_mul_cancel_left, d.base_coord]
  · rw [Functor.assoc, liftByMultiplier_covers, ← Functor.assoc, liftByMultiplier_covers,
      Functor.assoc, A.hom_inv_id, Functor.comp_id, Functor.id_comp]

/-- Strict inverse, second half (paper `lem:local` proof): `F⁻¹ ⋙ F_k = 𝟭 O`. -/
theorem liftByMultiplier_inv_comp (d : OEData G p) (A : StrictAut S) (k : S → G) :
    liftByMultiplier d A.inv (fun t => (k (A.inv.obj t))⁻¹) ⋙ liftByMultiplier d A.hom k
      = 𝟭 O := by
  have hAA : ∀ t, A.hom.obj (A.inv.obj t) = t := fun t => Functor.congr_obj A.inv_hom_id t
  refine funct_ext d (fun y => ?_) ?_
  · show d.act (d.base (A.hom.obj (p.obj (d.act (d.base (A.inv.obj (p.obj y)))
          ((k (A.inv.obj (p.obj y)))⁻¹ * d.coord y)))))
        (k (p.obj (d.act (d.base (A.inv.obj (p.obj y))) ((k (A.inv.obj (p.obj y)))⁻¹ * d.coord y)))
          * d.coord (d.act (d.base (A.inv.obj (p.obj y))) ((k (A.inv.obj (p.obj y)))⁻¹ * d.coord y)))
        = y
    rw [d.p_act, d.p_base, d.coord_base, mul_inv_cancel_left, hAA, d.base_coord]
  · rw [Functor.assoc, liftByMultiplier_covers, ← Functor.assoc, liftByMultiplier_covers,
      Functor.assoc, A.inv_hom_id, Functor.comp_id, Functor.id_comp]

/-- The admissible lift defined by a strict base automorphism `A` and a multiplier `k` that is
    constant along every base arrow, bundled as an element of `AutBoxG d` (paper `lem:local`,
    "every such `k` defines an admissible lift"). -/
noncomputable def autBoxGOfMultiplier (d : OEData G p) (A : StrictAut S) (k : S → G)
    (hk : ∀ {s t : S} (_ : s ⟶ t), k s = k t) : AutBoxG d where
  hom := liftByMultiplier d A.hom k
  inv := liftByMultiplier d A.inv (fun t => (k (A.inv.obj t))⁻¹)
  hom_inv_id := liftByMultiplier_comp_inv d A k
  inv_hom_id := liftByMultiplier_inv_comp d A k
  base := A
  equiv := liftByMultiplier_isGEquivariant d A.hom k
  pres := (liftByMultiplier_preservesCleavage_iff d A.hom k).2 hk

/-- (paper `lem:local`) -/
@[simp] theorem autBoxGOfMultiplier_hom (d : OEData G p) (A : StrictAut S) (k : S → G)
    (hk : ∀ {s t : S} (_ : s ⟶ t), k s = k t) :
    (autBoxGOfMultiplier d A k hk).hom = liftByMultiplier d A.hom k := rfl

/-- (paper `lem:local`) -/
@[simp] theorem autBoxGOfMultiplier_inv (d : OEData G p) (A : StrictAut S) (k : S → G)
    (hk : ∀ {s t : S} (_ : s ⟶ t), k s = k t) :
    (autBoxGOfMultiplier d A k hk).inv = liftByMultiplier d A.inv (fun t => (k (A.inv.obj t))⁻¹) :=
  rfl

/-- (paper `lem:local`) -/
@[simp] theorem autBoxGOfMultiplier_base (d : OEData G p) (A : StrictAut S) (k : S → G)
    (hk : ∀ {s t : S} (_ : s ⟶ t), k s = k t) :
    (autBoxGOfMultiplier d A k hk).base = A := rfl

/-- Every admissible lift is the bundled multiplier lift of its base and its own multiplier
    (paper `lem:local`, both directions together; no connectedness). -/
theorem eq_autBoxGOfMultiplier (d : OEData G p) (e : AutBoxG d) :
    e = autBoxGOfMultiplier d e.base (liftMultiplier d e.hom)
      (fun u => liftMultiplier_eq_of_hom d e.pres u) :=
  AutBoxG.ext_hom d (eq_liftByMultiplier d e.equiv e.pres.covers)

/-- The bundled multiplier lift over a subgroup `H` of base automorphisms (paper `lem:local`,
    `def:lifts` with `A ∈ H`). -/
noncomputable def autBoxGOverOfMultiplier (d : OEData G p) (H : Subgroup (StrictAut S)) (A : H)
    (k : S → G) (hk : ∀ {s t : S} (_ : s ⟶ t), k s = k t) : AutBoxGOver d H :=
  ⟨autBoxGOfMultiplier d A.1 k hk, A.2⟩

/-- (paper `lem:local`) -/
@[simp] theorem autBoxGOverOfMultiplier_val (d : OEData G p) (H : Subgroup (StrictAut S))
    (A : H) (k : S → G) (hk : ∀ {s t : S} (_ : s ⟶ t), k s = k t) :
    (autBoxGOverOfMultiplier d H A k hk).1 = autBoxGOfMultiplier d A.1 k hk := rfl

/-! ## 7. Unique factorization on a connected base (paper `thm:strict` proof) -/

/-- On a connected base, every equivariant transport-preserving functor over `A` has a unique
    factorization `Λ_a Ã` (Lean order `Ã ⋙ Λ_a`), with `a` the constant multiplier (paper
    `thm:strict` proof). -/
theorem exists_unique_eq_liftFunctor_comp_Λ (d : OEData G p) [IsConnected S] {F : O ⥤ O}
    {A : S ⥤ S} (hF : IsGEquivariant d F) (pc : PreservesCleavage d F A) :
    ∃! a : G, F = liftFunctor d A ⋙ Λ d a := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  refine ⟨liftMultiplier d F s₀, ?_, ?_⟩
  · have hk : liftMultiplier d F = fun _ => liftMultiplier d F s₀ :=
      funext fun s => liftMultiplier_const d pc s s₀
    beta_reduce
    rw [← liftByMultiplier_const, ← hk]
    exact eq_liftByMultiplier d hF pc.covers
  · intro a ha
    have h := congrArg (fun F' => liftMultiplier d F' s₀) ha
    simp only [← liftByMultiplier_const, liftMultiplier_liftByMultiplier] at h
    exact h.symm

/-! ## 8. The section formulation on a connected base (paragraph after paper `lem:local`) -/

/-- The object equations `F(b_s) = b_{A s} · c` imply the functor equation
    `B ⋙ F = A ⋙ B ⋙ R_c` (paper: "these object equations imply `FB = R_c B A` as functors by
    faithfulness").  Only the covering equation is used; no connectedness. -/
theorem sectionFunctor_comp_eq_of_obj (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S}
    (hc : F ⋙ p = p ⋙ A) (c : G) (h : ∀ s, F.obj (d.base s) = d.act (d.base (A.obj s)) c) :
    d.sectionFunctor ⋙ F = A ⋙ d.sectionFunctor ⋙ d.actFunctor c := by
  refine functor_ext_of_comp_p d h ?_
  rw [Functor.assoc, hc, ← Functor.assoc, d.sectionFunctor_comp_p, Functor.id_comp,
    Functor.assoc, Functor.assoc, actFunctor_comp_p, d.sectionFunctor_comp_p, Functor.comp_id]

/-- Section formulation, object form (paragraph after paper `lem:local`): on a connected base an
    equivariant functor `F` covering `A` preserves transport iff there is one `c ∈ G` with
    `F(b_s) = b_{A s} · c` for every `s`. -/
theorem preservesCleavage_iff_exists_base_obj (d : OEData G p) [IsConnected S] {F : O ⥤ O}
    {A : S ⥤ S} (hF : IsGEquivariant d F) (hc : F ⋙ p = p ⋙ A) :
    PreservesCleavage d F A ↔ ∃ c : G, ∀ s, F.obj (d.base s) = d.act (d.base (A.obj s)) c := by
  constructor
  · intro pc
    obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
    refine ⟨liftMultiplier d F s₀, fun s => ?_⟩
    rw [lift_obj_base d hc, liftMultiplier_const d pc s s₀]
  · rintro ⟨c, hcobj⟩
    refine (preservesCleavage_iff_multiplier d hF hc).2 (fun {s t} _ => ?_)
    simp only [liftMultiplier, hcobj, d.coord_base]

/-- Section formulation (paragraph after paper `lem:local`), in Lean composition order: on a
    connected base an equivariant functor `F` covering `A` preserves transport iff there is
    `c ∈ G` with `B ⋙ F = A ⋙ B ⋙ R_c` as functors, where `B = d.sectionFunctor` and
    `R_c = d.actFunctor c` (paper operator order `FB = R_c B A`). -/
theorem preservesCleavage_iff_exists_section (d : OEData G p) [IsConnected S] {F : O ⥤ O}
    {A : S ⥤ S} (hF : IsGEquivariant d F) (hc : F ⋙ p = p ⋙ A) :
    PreservesCleavage d F A ↔
      ∃ c : G, d.sectionFunctor ⋙ F = A ⋙ d.sectionFunctor ⋙ d.actFunctor c := by
  rw [preservesCleavage_iff_exists_base_obj d hF hc]
  constructor
  · rintro ⟨c, h⟩
    exact ⟨c, sectionFunctor_comp_eq_of_obj d hc c h⟩
  · rintro ⟨c, h⟩
    exact ⟨c, fun s => Functor.congr_obj h s⟩

/-! ## 9. The twisted coordinate description (paper `thm:twisted` proof) -/

/-- Object form of a `θ`-twisted lift (paper `thm:twisted` proof): if
    `F(x · g) = F(x) · θ(g)` and `F` covers `A`, then `F(x) = b_{A(p x)} · (k(p x) θ(g_x))`,
    i.e. `F(s,g) = (A(s), k(s) θ_A(g))`. -/
theorem lift_obj_eq_twisted (d : OEData G p) {θ : MulAut G} {F : O ⥤ O} {A : S ⥤ S}
    (hF : IsTwistedEquivariant d θ F) (hc : F ⋙ p = p ⋙ A) (x : O) :
    F.obj x
      = d.act (d.base (A.obj (p.obj x))) (liftMultiplier d F (p.obj x) * θ (d.coord x)) := by
  have e1 : F.obj x = d.act (F.obj (d.base (p.obj x))) (θ (d.coord x)) := by
    conv_lhs => rw [← d.base_coord x]
    exact hF _ _
  rw [e1, lift_obj_base d hc, d.act_mul]

/-- Twisted object form on normal-form coordinates (paper `thm:twisted` proof):
    `F(b_s · g) = b_{A s} · (k(s) θ(g))`. -/
theorem lift_obj_act_base_twisted (d : OEData G p) {θ : MulAut G} {F : O ⥤ O} {A : S ⥤ S}
    (hF : IsTwistedEquivariant d θ F) (hc : F ⋙ p = p ⋙ A) (s : S) (g : G) :
    F.obj (d.act (d.base s) g) = d.act (d.base (A.obj s)) (liftMultiplier d F s * θ g) := by
  rw [hF, lift_obj_base d hc, d.act_mul]

/-- Uniqueness of the twisted multiplier (paper `thm:twisted` proof). -/
theorem multiplier_unique_twisted (d : OEData G p) {θ : MulAut G} {F : O ⥤ O} {A : S ⥤ S}
    {k : S → G}
    (hk : ∀ x, F.obj x = d.act (d.base (A.obj (p.obj x))) (k (p.obj x) * θ (d.coord x))) :
    k = liftMultiplier d F := by
  funext s
  have h := hk (d.base s)
  rw [d.p_base] at h
  unfold liftMultiplier
  rw [h, d.coord_base, coord_base_one, map_one, mul_one]

/-- Twisted transport criterion (paper `thm:twisted` proof: "since transport preserves
    coordinates, its preservation is again equivalent to constancy of `k` along base arrows"). -/
theorem preservesCleavage_iff_multiplier_twisted (d : OEData G p) {θ : MulAut G} {F : O ⥤ O}
    {A : S ⥤ S} (hF : IsTwistedEquivariant d θ F) (hc : F ⋙ p = p ⋙ A) :
    PreservesCleavage d F A ↔
      ∀ {s t : S} (_ : s ⟶ t), liftMultiplier d F s = liftMultiplier d F t := by
  constructor
  · intro pc s t u
    exact liftMultiplier_eq_of_hom d pc u
  · intro hk
    refine ⟨hc, ?_⟩
    intro s t u y hy
    rw [d.reind_eq, lift_obj_act_base_twisted d hF hc, d.reind_eq, lift_obj_eq_twisted d hF hc y,
      d.coord_base, hy, hk u]

/-- The product-model functor `(s,g) ↦ (A(s), k(s) θ(g))` (paper `thm:twisted` proof). -/
def multiplierProductFunctorθ (A : S ⥤ S) (θ : MulAut G) (k : S → G) :
    S × Pair G ⥤ S × Pair G where
  obj X := (A.obj X.1, ⟨k X.1 * θ X.2.pt⟩)
  map f := (A.map f.1, ⟨⟩)
  map_id X := Prod.ext (A.map_id X.1) (Subsingleton.elim _ _)
  map_comp f g := Prod.ext (A.map_comp f.1 g.1) (Subsingleton.elim _ _)

/-- (paper `thm:twisted`) -/
@[simp] theorem multiplierProductFunctorθ_obj (A : S ⥤ S) (θ : MulAut G) (k : S → G) (s : S)
    (g : G) : (multiplierProductFunctorθ A θ k).obj (s, ⟨g⟩) = (A.obj s, ⟨k s * θ g⟩) := rfl

/-- In the product normal form a `θ`-twisted lift over `A` IS the functor
    `(s,g) ↦ (A(s), k(s) θ(g))`, strictly (paper `thm:twisted` proof). -/
theorem normalForm_lift_eq_twisted (d : OEData G p) {θ : MulAut G} {F : O ⥤ O} {A : S ⥤ S}
    (hF : IsTwistedEquivariant d θ F) (hc : F ⋙ p = p ⋙ A) :
    normalFormFrom d ⋙ F ⋙ normalFormTo d
      = multiplierProductFunctorθ A θ (liftMultiplier d F) := by
  have hobj : ∀ X : S × Pair G,
      ((p.obj (F.obj (d.act (d.base X.1) X.2.pt)), ⟨d.coord (F.obj (d.act (d.base X.1) X.2.pt))⟩) :
        S × Pair G) = (A.obj X.1, ⟨liftMultiplier d F X.1 * θ X.2.pt⟩) := by
    intro X
    rw [lift_obj_act_base_twisted d hF hc, d.p_act, d.p_base, d.coord_base]
  fapply CategoryTheory.Functor.ext
  · exact hobj
  · intro X Y f
    have key : ((p.map (F.map (d.toMinSpec.liftOver f.1 (p_act_base d X.1 X.2.pt)
          (p_act_base d Y.1 Y.2.pt))), ⟨⟩) :
          ((p.obj (F.obj (d.act (d.base X.1) X.2.pt)),
            ⟨d.coord (F.obj (d.act (d.base X.1) X.2.pt))⟩) : S × Pair G) ⟶
          (p.obj (F.obj (d.act (d.base Y.1) Y.2.pt)),
            ⟨d.coord (F.obj (d.act (d.base Y.1) Y.2.pt))⟩))
        = eqToHom (hobj X) ≫
          ((A.map f.1, ⟨⟩) : ((A.obj X.1, ⟨liftMultiplier d F X.1 * θ X.2.pt⟩) : S × Pair G) ⟶
            (A.obj Y.1, ⟨liftMultiplier d F Y.1 * θ Y.2.pt⟩)) ≫ eqToHom (hobj Y).symm := by
      apply prodPairHom_ext
      simp only [prod_comp_fst, eqToHom_prod_fst, covers_map hc, MinSpec.p_map_liftOver,
        Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    exact key

/-- The `θ`-twisted lift defined by a multiplier (paper `thm:twisted` proof): objects
    `x ↦ b_{A(p x)} · (k(p x) θ(g_x))`, arrows the unique lift of `A(p f)`. -/
noncomputable def liftByMultiplierθ (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) (k : S → G) :
    O ⥤ O where
  obj x := d.act (d.base (A.obj (p.obj x))) (k (p.obj x) * θ (d.coord x))
  map {x y} f := d.toMinSpec.liftOver (A.map (p.map f))
    (d.p_liftObjθ A x (k (p.obj x) * θ (d.coord x)))
    (d.p_liftObjθ A y (k (p.obj y) * θ (d.coord y)))
  map_id x := by simp
  map_comp f g := by simp

/-- (paper `thm:twisted`) -/
@[simp] theorem liftByMultiplierθ_obj (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) (k : S → G)
    (x : O) :
    (liftByMultiplierθ d A θ k).obj x
      = d.act (d.base (A.obj (p.obj x))) (k (p.obj x) * θ (d.coord x)) := rfl

/-- At the trivial twist the twisted multiplier lift is the untwisted one (paper `thm:twisted`:
    "the untwisted theorem is the special case of trivial `θ`"). -/
theorem liftByMultiplierθ_one_twist (d : OEData G p) (A : S ⥤ S) (k : S → G) :
    liftByMultiplierθ d A 1 k = liftByMultiplier d A k := rfl

/-- The twisted multiplier lift covers `A` (paper `thm:twisted`). -/
theorem liftByMultiplierθ_covers (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) (k : S → G) :
    liftByMultiplierθ d A θ k ⋙ p = p ⋙ A := by
  fapply CategoryTheory.Functor.ext
  · intro x; exact d.p_liftObjθ A x (k (p.obj x) * θ (d.coord x))
  · intro x y f
    exact d.toMinSpec.p_map_liftOver _ (d.p_liftObjθ A x _) (d.p_liftObjθ A y _)

/-- The twisted multiplier lift is `θ`-twisted equivariant (paper `thm:twisted`). -/
theorem liftByMultiplierθ_isTwistedEquivariant (d : OEData G p) (A : S ⥤ S) (θ : MulAut G)
    (k : S → G) : IsTwistedEquivariant d θ (liftByMultiplierθ d A θ k) := by
  intro x g
  simp only [liftByMultiplierθ_obj]
  rw [d.p_act, d.coord_act, map_mul, d.act_mul, mul_assoc]

/-- The multiplier of `liftByMultiplierθ d A θ k` is `k` (paper `thm:twisted`). -/
theorem liftMultiplier_liftByMultiplierθ (d : OEData G p) (A : S ⥤ S) (θ : MulAut G)
    (k : S → G) : liftMultiplier d (liftByMultiplierθ d A θ k) = k := by
  funext s
  simp only [liftMultiplier, liftByMultiplierθ_obj]
  rw [d.coord_base, d.p_base, coord_base_one, map_one, mul_one]

/-- The twisted multiplier lift preserves transport iff `k` is constant along every base arrow
    (paper `thm:twisted`). -/
theorem liftByMultiplierθ_preservesCleavage_iff (d : OEData G p) (A : S ⥤ S) (θ : MulAut G)
    (k : S → G) :
    PreservesCleavage d (liftByMultiplierθ d A θ k) A ↔ ∀ {s t : S} (_ : s ⟶ t), k s = k t := by
  rw [preservesCleavage_iff_multiplier_twisted d (liftByMultiplierθ_isTwistedEquivariant d A θ k)
    (liftByMultiplierθ_covers d A θ k), liftMultiplier_liftByMultiplierθ]

/-- Every `θ`-twisted functor over `A` is the twisted multiplier lift of its own multiplier
    (paper `thm:twisted` proof). -/
theorem eq_liftByMultiplierθ (d : OEData G p) {θ : MulAut G} {F : O ⥤ O} {A : S ⥤ S}
    (hF : IsTwistedEquivariant d θ F) (hc : F ⋙ p = p ⋙ A) :
    F = liftByMultiplierθ d A θ (liftMultiplier d F) :=
  lift_eq_of_obj_eq d hc (liftByMultiplierθ_covers d A θ _) (lift_obj_eq_twisted d hF hc)

/-- A constant twisted multiplier `k = a` gives `Λ_a Ã_θ`, Lean order `Ã_θ ⋙ Λ_a`
    (paper `thm:twisted`). -/
theorem liftByMultiplierθ_const (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) (a : G) :
    liftByMultiplierθ d A θ (fun _ => a) = liftFunctorθ d A θ ⋙ Λ d a := by
  refine lift_eq_of_obj_eq d (liftByMultiplierθ_covers d A θ _) ?_ (fun x => ?_)
  · rw [Functor.assoc, Λ_comp_p]; exact liftθ_covers d A θ
  · show d.act (d.base (A.obj (p.obj x))) (a * θ (d.coord x))
      = d.act (d.base (p.obj (d.act (d.base (A.obj (p.obj x))) (θ (d.coord x)))))
          (a * d.coord (d.act (d.base (A.obj (p.obj x))) (θ (d.coord x))))
    rw [d.p_act, d.p_base, d.coord_base]

/-- The canonical twisted lift is the twisted multiplier lift with `k = 1`
    (paper `thm:twisted`, `Ã_θ(x) = b_{A(p x)} · θ_A(g_x)`). -/
theorem liftByMultiplierθ_one (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) :
    liftByMultiplierθ d A θ 1 = liftFunctorθ d A θ :=
  lift_eq_of_obj_eq d (liftByMultiplierθ_covers d A θ 1) (liftθ_covers d A θ)
    (fun x => by
      show d.act (d.base (A.obj (p.obj x))) ((1 : S → G) (p.obj x) * θ (d.coord x))
        = d.act (d.base (A.obj (p.obj x))) (θ (d.coord x))
      rw [Pi.one_apply, one_mul])

/-- Twisted strict inverse, first half (paper `thm:twisted` proof: "inverses are obtained using
    `A⁻¹` and `θ_A⁻¹`"): the inverse has object function `(t,h) ↦ (A⁻¹ t, θ⁻¹(k(A⁻¹ t)⁻¹ h))`. -/
theorem liftByMultiplierθ_comp_inv (d : OEData G p) (A : StrictAut S) (θ : MulAut G)
    (k : S → G) :
    liftByMultiplierθ d A.hom θ k ⋙ liftByMultiplierθ d A.inv θ⁻¹ (fun t => θ⁻¹ (k (A.inv.obj t))⁻¹)
      = 𝟭 O := by
  have hAA : ∀ s, A.inv.obj (A.hom.obj s) = s := fun s => Functor.congr_obj A.hom_inv_id s
  refine funct_ext d (fun x => ?_) ?_
  · show d.act (d.base (A.inv.obj (p.obj (d.act (d.base (A.hom.obj (p.obj x)))
          (k (p.obj x) * θ (d.coord x))))))
        (θ⁻¹ (k (A.inv.obj (p.obj (d.act (d.base (A.hom.obj (p.obj x)))
            (k (p.obj x) * θ (d.coord x))))))⁻¹
          * θ⁻¹ (d.coord (d.act (d.base (A.hom.obj (p.obj x))) (k (p.obj x) * θ (d.coord x)))))
        = x
    rw [d.p_act, d.p_base, d.coord_base, hAA, ← map_mul, inv_mul_cancel_left,
      MulAut.inv_apply_self, d.base_coord]
  · rw [Functor.assoc, liftByMultiplierθ_covers, ← Functor.assoc, liftByMultiplierθ_covers,
      Functor.assoc, A.hom_inv_id, Functor.comp_id, Functor.id_comp]

/-- Twisted strict inverse, second half (paper `thm:twisted` proof). -/
theorem liftByMultiplierθ_inv_comp (d : OEData G p) (A : StrictAut S) (θ : MulAut G)
    (k : S → G) :
    liftByMultiplierθ d A.inv θ⁻¹ (fun t => θ⁻¹ (k (A.inv.obj t))⁻¹) ⋙ liftByMultiplierθ d A.hom θ k
      = 𝟭 O := by
  have hAA : ∀ t, A.hom.obj (A.inv.obj t) = t := fun t => Functor.congr_obj A.inv_hom_id t
  refine funct_ext d (fun y => ?_) ?_
  · show d.act (d.base (A.hom.obj (p.obj (d.act (d.base (A.inv.obj (p.obj y)))
          (θ⁻¹ (k (A.inv.obj (p.obj y)))⁻¹ * θ⁻¹ (d.coord y))))))
        (k (p.obj (d.act (d.base (A.inv.obj (p.obj y)))
            (θ⁻¹ (k (A.inv.obj (p.obj y)))⁻¹ * θ⁻¹ (d.coord y))))
          * θ (d.coord (d.act (d.base (A.inv.obj (p.obj y)))
            (θ⁻¹ (k (A.inv.obj (p.obj y)))⁻¹ * θ⁻¹ (d.coord y)))))
        = y
    rw [d.p_act, d.p_base, d.coord_base, map_mul, MulAut.apply_inv_self, MulAut.apply_inv_self,
      mul_inv_cancel_left, hAA, d.base_coord]
  · rw [Functor.assoc, liftByMultiplierθ_covers, ← Functor.assoc, liftByMultiplierθ_covers,
      Functor.assoc, A.inv_hom_id, Functor.comp_id, Functor.id_comp]

/-- The `θ`-twisted admissible lift over `A ∈ H` defined by a multiplier `k` constant along every
    base arrow, bundled as an element of `AutBoxGθOver d H θ` (paper `thm:twisted` proof). -/
noncomputable def autBoxGθOverOfMultiplier (d : OEData G p) (H : Subgroup (StrictAut S))
    (θ : H →* MulAut G) (A : H) (k : S → G) (hk : ∀ {s t : S} (_ : s ⟶ t), k s = k t) :
    AutBoxGθOver d H θ where
  hom := liftByMultiplierθ d A.1.hom (θ A) k
  inv := liftByMultiplierθ d A.1.inv (θ A)⁻¹ (fun t => (θ A)⁻¹ (k (A.1.inv.obj t))⁻¹)
  hom_inv_id := liftByMultiplierθ_comp_inv d A.1 (θ A) k
  inv_hom_id := liftByMultiplierθ_inv_comp d A.1 (θ A) k
  base := A
  equiv := liftByMultiplierθ_isTwistedEquivariant d A.1.hom (θ A) k
  pres := (liftByMultiplierθ_preservesCleavage_iff d A.1.hom (θ A) k).2 hk

/-- (paper `thm:twisted`) -/
@[simp] theorem autBoxGθOverOfMultiplier_hom (d : OEData G p) (H : Subgroup (StrictAut S))
    (θ : H →* MulAut G) (A : H) (k : S → G) (hk : ∀ {s t : S} (_ : s ⟶ t), k s = k t) :
    (autBoxGθOverOfMultiplier d H θ A k hk).hom = liftByMultiplierθ d A.1.hom (θ A) k := rfl

/-- (paper `thm:twisted`) -/
@[simp] theorem autBoxGθOverOfMultiplier_base (d : OEData G p) (H : Subgroup (StrictAut S))
    (θ : H →* MulAut G) (A : H) (k : S → G) (hk : ∀ {s t : S} (_ : s ⟶ t), k s = k t) :
    (autBoxGθOverOfMultiplier d H θ A k hk).base = A := rfl

/-- On a connected base, every `θ`-twisted transport-preserving functor over `A` has a unique
    factorization `Λ_a Ã_θ` (Lean order `Ã_θ ⋙ Λ_a`) (paper `thm:twisted`: "every twisted lift has
    a unique factorization"). -/
theorem exists_unique_eq_liftFunctorθ_comp_Λ (d : OEData G p) [IsConnected S] {θ : MulAut G}
    {F : O ⥤ O} {A : S ⥤ S} (hF : IsTwistedEquivariant d θ F) (pc : PreservesCleavage d F A) :
    ∃! a : G, F = liftFunctorθ d A θ ⋙ Λ d a := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  refine ⟨liftMultiplier d F s₀, ?_, ?_⟩
  · have hk : liftMultiplier d F = fun _ => liftMultiplier d F s₀ :=
      funext fun s => liftMultiplier_const d pc s s₀
    beta_reduce
    rw [← liftByMultiplierθ_const, ← hk]
    exact eq_liftByMultiplierθ d hF pc.covers
  · intro a ha
    have h := congrArg (fun F' => liftMultiplier d F' s₀) ha
    simp only [← liftByMultiplierθ_const, liftMultiplier_liftByMultiplierθ] at h
    exact h.symm
