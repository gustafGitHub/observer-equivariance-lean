import ObserverEquivariance.LocalLifts

/-!
# Disconnected bases and unrestricted lifts (paper `prop:components`, `prop:nocleavage`)

Paper labels covered in this file:

* `prop:components` (Componentwise classification), with no connectedness and no nonemptiness
  hypothesis on the base:
  - the zigzag components `π₀(S) = CategoryTheory.ConnectedComponents S` and the permutation of
    components induced by a strict base automorphism (`componentMap`, `componentPerm`);
  - the action `(A · γ)(c) = γ(A⁻¹ c)` of `H` on `π₀(S) → G`, proved to be a group homomorphism
    `componentAction H G : H →* MulAut (π₀(S) → G)`, which is precomposition with the inverse
    induced permutation (`componentAction_apply_eq_perm`, `componentAction_apply_perm_inv`);
  - the key identity `Ã Λ_δ Ã⁻¹ = Λ_{δ ∘ A⁻¹}` at functor level (`liftFunctor_conj_ΛFun`,
    `liftFunctor_conj_ΛFun_components`) and group level (`liftHomOver_conj_components`), and
    `(1, A) ↦ Ã` (`autBoxGOverMulEquivComponents_symm_inr`);
  - multipliers of transport-preserving lifts descend to `π₀(S)` (`eq_of_zigzag_of_hom`,
    `componentMultiplier`, `liftMultiplier_factors_through_components`);
  - the factorization `F = Λ_γ Ã`, Lean order `liftFunctor d A ⋙ ΛFun d (γ ∘ [·])`, whose
    multiplier at `s` is `γ [A s]` (`liftByMultiplier_components_eq`,
    `autBoxGOverOfComponents_hom_eq`);
  - the group isomorphism
    `autBoxGOverMulEquivComponents d H : AutBoxGOver d H ≃* (π₀(S) → G) ⋊[componentAction H G] H`;
  - the remarks after `prop:components`: for an empty base the first factor is trivial
    (`componentFunctions_unique_of_isEmpty`), for a (pre)connected base the component action is
    trivial (`componentAction_eq_one`) and the first factor is `G`
    (`componentFunctionsMulEquiv`, `autBoxGOverMulEquivProdOfComponents`);
  - the remark "a disconnected base need not give a direct product": the discrete base on `Fin 2`
    with its swap (section 8, `ComponentsSwapExample.componentAction_ne_one`,
    `ComponentsSwapExample.liftHomOver_discSwap_not_comm`).
* `prop:nocleavage` (Unrestricted equivariant lifts), general part:
  - the group `AutEquivOver d H` of strict automorphisms that are only equivariant and cover an
    element of `H` (no transport condition), with projection `ΦEquivOver`;
  - the action `objectAction H G : H →* MulAut (S → G)`, `(A · γ)(s) = γ(A⁻¹ s)`;
  - `autEquivOverMulEquiv d H : AutEquivOver d H ≃* (S → G) ⋊[objectAction H G] H`;
  - the kernel over `id_S`: `kerΦEquivOverMulEquiv d H : (ΦEquivOver d H).ker ≃* (S → G)`;
  - the forgetful embedding `autBoxGOverToAutEquivOver d H : AutBoxGOver d H →* AutEquivOver d H`;
  - "conjugation by `Ã` gives the displayed action" (`autEquivOver_conj_object`,
    `autEquivOverMulEquiv_symm_inr`).

Conventions: `F ⋙ G` is "first `F`, then `G`"; `StrictAut` multiplication is operator order,
`(A * B).hom = B.hom ⋙ A.hom`.  The paper's `Λ_γ Ã` is the Lean functor `Ã ⋙ Λ_γ`.
-/

open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}

namespace Components

/-! ## 1. Components and the induced permutation (paper `prop:components`) -/

/-- The class `[s] ∈ π₀(S)` of an object (paper `prop:components`, `π₀(S)` = zigzag
    components). -/
abbrev compMk (s : S) : CategoryTheory.ConnectedComponents S :=
  Quotient.mk (Zigzag.setoid S) s

/-- A function constant along every base arrow is constant along every zigzag (paper
    `prop:components` proof: "the multiplier is constant on each component"). -/
theorem eq_of_zigzag_of_hom {α : Sort*} (f : S → α) (hf : ∀ {s t : S} (_ : s ⟶ t), f s = f t)
    {a b : S} (h : Zigzag a b) : f a = f b := by
  induction h with
  | refl => rfl
  | tail _ hz ih =>
    refine ih.trans ?_
    rcases hz with ⟨⟨u⟩⟩ | ⟨⟨u⟩⟩
    · exact hf u
    · exact (hf u).symm

/-- The function on components induced by a function constant along base arrows (paper
    `prop:components`). -/
def liftComp {α : Sort*} (f : S → α) (hf : ∀ {s t : S} (_ : s ⟶ t), f s = f t) :
    CategoryTheory.ConnectedComponents S → α :=
  Quotient.lift f (fun _ _ h => eq_of_zigzag_of_hom f hf h)

/-- (paper `prop:components`) -/
@[simp] theorem liftComp_mk {α : Sort*} (f : S → α) (hf : ∀ {s t : S} (_ : s ⟶ t), f s = f t)
    (s : S) : liftComp f hf (compMk s) = f s := rfl

/-- The map of components induced by a base functor (paper `prop:components`, "its induced
    permutation of components"). -/
abbrev componentMap (A : S ⥤ S) :
    CategoryTheory.ConnectedComponents S → CategoryTheory.ConnectedComponents S :=
  A.mapConnectedComponents

/-- (paper `prop:components`) -/
@[simp] theorem componentMap_mk (A : S ⥤ S) (s : S) :
    componentMap A (compMk s) = compMk (A.obj s) := rfl

/-- Functoriality of the induced map of components (paper `prop:components`). -/
theorem componentMap_comp (A B : S ⥤ S) (c : CategoryTheory.ConnectedComponents S) :
    componentMap (A ⋙ B) c = componentMap B (componentMap A c) := by
  induction c using Quotient.ind; rfl

/-- (paper `prop:components`) -/
theorem componentMap_id (c : CategoryTheory.ConnectedComponents S) :
    componentMap (𝟭 S) c = c := by
  induction c using Quotient.ind; rfl

/-- The permutation of `π₀(S)` induced by a strict base automorphism (paper `prop:components`). -/
def componentPerm (A : StrictAut S) : Equiv.Perm (CategoryTheory.ConnectedComponents S) where
  toFun := componentMap A.hom
  invFun := componentMap A.inv
  left_inv c := by rw [← componentMap_comp, A.hom_inv_id, componentMap_id]
  right_inv c := by rw [← componentMap_comp, A.inv_hom_id, componentMap_id]

end Components

open Components

/-! ## 2. The actions of `H` on multiplier functions (paper `prop:components`, `prop:nocleavage`) -/

/-- The action of `H` on component functions, `(A · γ)(c) = γ(A⁻¹ c)` (paper `prop:components`),
    as a group homomorphism `H →* MulAut (π₀(S) → G)`; the first factor has pointwise
    multiplication. -/
def componentAction (H : Subgroup (StrictAut S)) (G : Type*) [Group G] :
    H →* MulAut (CategoryTheory.ConnectedComponents S → G) where
  toFun A :=
    { toFun := fun γ c => γ (componentMap A.1.inv c)
      invFun := fun γ c => γ (componentMap A.1.hom c)
      left_inv := fun γ => funext fun c => by
        show γ (componentMap A.1.inv (componentMap A.1.hom c)) = γ c
        rw [← componentMap_comp, A.1.hom_inv_id, componentMap_id]
      right_inv := fun γ => funext fun c => by
        show γ (componentMap A.1.hom (componentMap A.1.inv c)) = γ c
        rw [← componentMap_comp, A.1.inv_hom_id, componentMap_id]
      map_mul' := fun _ _ => rfl }
  map_one' := MulEquiv.ext fun γ => funext fun c => by
    show γ (componentMap (𝟭 S) c) = γ c
    rw [componentMap_id]
  map_mul' A B := MulEquiv.ext fun γ => funext fun c => by
    show γ (componentMap (A.1.inv ⋙ B.1.inv) c) = γ (componentMap B.1.inv (componentMap A.1.inv c))
    rw [componentMap_comp]

/-- (paper `prop:components`, `(A · γ)(c) = γ(A⁻¹ c)`) -/
@[simp] theorem componentAction_apply (H : Subgroup (StrictAut S)) (A : H)
    (γ : CategoryTheory.ConnectedComponents S → G) (c : CategoryTheory.ConnectedComponents S) :
    componentAction H G A γ c = γ (componentMap A.1.inv c) := rfl

/-- (paper `prop:components`) -/
theorem componentAction_apply_mk (H : Subgroup (StrictAut S)) (A : H)
    (γ : CategoryTheory.ConnectedComponents S → G) (s : S) :
    componentAction H G A γ (compMk s) = γ (compMk (A.1.inv.obj s)) := rfl

/-- The action of `H` on component functions is precomposition with the inverse of the induced
    permutation of components (paper `prop:components`: "`H` acts by its induced permutation of
    components", `(A · γ)(c) = γ(A⁻¹ c)`). -/
theorem componentAction_apply_eq_perm (H : Subgroup (StrictAut S)) (A : H)
    (γ : CategoryTheory.ConnectedComponents S → G) :
    componentAction H G A γ = γ ∘ (componentPerm A.1).symm := rfl

/-- Pointwise form: `(A · γ)(c) = γ(π_{A⁻¹}(c))`, with `π_{A⁻¹} = componentPerm A⁻¹` the permutation
    of components induced by `A⁻¹` (paper `prop:components`). -/
theorem componentAction_apply_perm_inv (H : Subgroup (StrictAut S)) (A : H)
    (γ : CategoryTheory.ConnectedComponents S → G) (c : CategoryTheory.ConnectedComponents S) :
    componentAction H G A γ c = γ (componentPerm A.1⁻¹ c) := rfl

/-- The permutation induced by `A⁻¹` is the inverse of the permutation induced by `A` (paper
    `prop:components`). -/
theorem componentPerm_inv (A : StrictAut S) : componentPerm A⁻¹ = (componentPerm A)⁻¹ := rfl

/-- The action of `H` on object functions, `(A · γ)(s) = γ(A⁻¹ s)` (paper `prop:nocleavage`), as a
    group homomorphism `H →* MulAut (S → G)`. -/
def objectAction (H : Subgroup (StrictAut S)) (G : Type*) [Group G] : H →* MulAut (S → G) where
  toFun A :=
    { toFun := fun γ s => γ (A.1.inv.obj s)
      invFun := fun γ s => γ (A.1.hom.obj s)
      left_inv := fun γ => funext fun s => by
        show γ (A.1.inv.obj (A.1.hom.obj s)) = γ s
        rw [show A.1.inv.obj (A.1.hom.obj s) = s from Functor.congr_obj A.1.hom_inv_id s]
      right_inv := fun γ => funext fun s => by
        show γ (A.1.hom.obj (A.1.inv.obj s)) = γ s
        rw [show A.1.hom.obj (A.1.inv.obj s) = s from Functor.congr_obj A.1.inv_hom_id s]
      map_mul' := fun _ _ => rfl }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

/-- (paper `prop:nocleavage`, `(A · γ)(s) = γ(A⁻¹ s)`) -/
@[simp] theorem objectAction_apply (H : Subgroup (StrictAut S)) (A : H) (γ : S → G) (s : S) :
    objectAction H G A γ s = γ (A.1.inv.obj s) := rfl

/-! ## 3. Multiplier lifts: composition and factorization (paper `prop:components` proof) -/

namespace Components

/-- Composition of multiplier lifts (paper `prop:components` proof, the semidirect law):
    `F_k^A ⋙ F_l^B = F^{A ⋙ B}_{s ↦ l(A s) k(s)}`. -/
theorem liftByMultiplier_comp (d : OEData G p) (A B : S ⥤ S) (k l : S → G) :
    liftByMultiplier d A k ⋙ liftByMultiplier d B l
      = liftByMultiplier d (A ⋙ B) (fun s => l (A.obj s) * k s) := by
  refine lift_eq_of_obj_eq d ?_ (liftByMultiplier_covers d _ _) (fun x => ?_)
  · rw [Functor.assoc, liftByMultiplier_covers, ← Functor.assoc, liftByMultiplier_covers,
      Functor.assoc]
  · show d.act (d.base (B.obj (p.obj (d.act (d.base (A.obj (p.obj x))) (k (p.obj x) * d.coord x)))))
        (l (p.obj (d.act (d.base (A.obj (p.obj x))) (k (p.obj x) * d.coord x)))
          * d.coord (d.act (d.base (A.obj (p.obj x))) (k (p.obj x) * d.coord x)))
      = d.act (d.base (B.obj (A.obj (p.obj x)))) (l (A.obj (p.obj x)) * k (p.obj x) * d.coord x)
    rw [d.p_act, d.p_base, d.coord_base, mul_assoc]

/-- The factorization `F = Λ_γ Ã` of paper `prop:components` / `prop:nocleavage`, Lean order
    `Ã ⋙ ΛFun γ`: its multiplier at `s` is `γ(A s)` (not `γ(s)`), i.e.
    `liftByMultiplier d A (γ ∘ A) = liftFunctor d A ⋙ ΛFun d γ`. -/
theorem liftByMultiplier_eq_liftFunctor_comp_ΛFun (d : OEData G p) (A : S ⥤ S) (γ : S → G) :
    liftByMultiplier d A (fun s => γ (A.obj s)) = liftFunctor d A ⋙ ΛFun d γ := by
  refine lift_eq_of_obj_eq d (liftByMultiplier_covers d _ _) ?_ (fun x => ?_)
  · rw [Functor.assoc, ΛFun_comp_p]; exact (lift_preservesCleavage d A).covers
  · show d.act (d.base (A.obj (p.obj x))) (γ (A.obj (p.obj x)) * d.coord x)
      = d.act (d.base (p.obj (d.act (d.base (A.obj (p.obj x))) (d.coord x))))
          (γ (p.obj (d.act (d.base (A.obj (p.obj x))) (d.coord x)))
            * d.coord (d.act (d.base (A.obj (p.obj x))) (d.coord x)))
    rw [d.p_act, d.p_base, d.coord_base]

/-- The conjugation identity of paper `prop:components` / `prop:nocleavage` at functor level:
    `Ã Λ_γ Ã⁻¹ = Λ_{γ ∘ A⁻¹}`.  In Lean order (first `Ã⁻¹`, then `Λ_γ`, then `Ã`):
    `liftFunctor d A.inv ⋙ ΛFun d γ ⋙ liftFunctor d A.hom = ΛFun d (γ ∘ A.inv)`, for any object
    function `γ : S → G`. -/
theorem liftFunctor_conj_ΛFun (d : OEData G p) (A : StrictAut S) (γ : S → G) :
    liftFunctor d A.inv ⋙ ΛFun d γ ⋙ liftFunctor d A.hom
      = ΛFun d (fun s => γ (A.inv.obj s)) := by
  rw [← Functor.assoc, ← liftByMultiplier_eq_liftFunctor_comp_ΛFun, ← liftByMultiplier_one d A.hom,
    liftByMultiplier_comp, A.inv_hom_id]
  have h := liftByMultiplier_eq_liftFunctor_comp_ΛFun d (𝟭 S) (fun s => γ (A.inv.obj s))
  rw [lift_id, Functor.id_comp] at h
  rw [← h]
  congr 1
  funext s
  exact one_mul _

/-- Elements of `AutBoxGOver d H` are determined by their total functor (paper `def:lifts`). -/
theorem autBoxGOver_ext {d : OEData G p} {H : Subgroup (StrictAut S)} {e₁ e₂ : AutBoxGOver d H}
    (h : e₁.1.hom = e₂.1.hom) : e₁ = e₂ :=
  Subtype.ext (AutBoxG.ext_hom d h)

end Components

/-! ## 4. Multipliers descend to components (paper `prop:components` proof) -/

namespace Components

/-- The multiplier of a transport-preserving functor, as a function on components (paper
    `prop:components` proof: "Lemma `lem:local` makes the multiplier constant on each
    component"). -/
def componentMultiplier (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S} (pc : PreservesCleavage d F A) :
    CategoryTheory.ConnectedComponents S → G :=
  liftComp (liftMultiplier d F) (fun u => liftMultiplier_eq_of_hom d pc u)

/-- (paper `prop:components`) -/
@[simp] theorem componentMultiplier_mk (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S}
    (pc : PreservesCleavage d F A) (s : S) :
    componentMultiplier d pc (compMk s) = liftMultiplier d F s := rfl

/-- The multiplier of a transport-preserving functor factors uniquely through the component
    quotient `S → π₀(S)` (paper `prop:components` proof).  No connectedness or nonemptiness. -/
theorem liftMultiplier_factors_through_components (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S}
    (pc : PreservesCleavage d F A) :
    ∃! κ : CategoryTheory.ConnectedComponents S → G, ∀ s, liftMultiplier d F s = κ (compMk s) :=
  ⟨componentMultiplier d pc, fun _ => rfl, fun κ hκ => funext fun c => by
    induction c using Quotient.ind with
    | _ a => exact (hκ a).symm⟩

/-- The multiplier `s ↦ γ [A s]` of the lift `Λ_γ Ã` (paper `prop:components`; INSTR §5: the
    multiplier is `γ(A s)`, not `γ(s)`). -/
def componentLiftMultiplier (A : S ⥤ S) (γ : CategoryTheory.ConnectedComponents S → G) : S → G :=
  fun s => γ (compMk (A.obj s))

omit [Group G] in
/-- The multiplier `s ↦ γ [A s]` is constant along base arrows (paper `prop:components`). -/
theorem componentLiftMultiplier_hom (A : S ⥤ S) (γ : CategoryTheory.ConnectedComponents S → G)
    {s t : S} (u : s ⟶ t) : componentLiftMultiplier A γ s = componentLiftMultiplier A γ t :=
  congrArg γ (Quotient.sound (Zigzag.of_hom (A.map u)))

/-- The factorization of paper `prop:components`: the multiplier lift with multiplier
    `s ↦ γ [A s]` is `Λ_γ Ã`, Lean order `liftFunctor d A ⋙ ΛFun d (γ ∘ [·])`. -/
theorem liftByMultiplier_components_eq (d : OEData G p) (A : S ⥤ S)
    (γ : CategoryTheory.ConnectedComponents S → G) :
    liftByMultiplier d A (componentLiftMultiplier A γ)
      = liftFunctor d A ⋙ ΛFun d (fun s => γ (compMk s)) :=
  liftByMultiplier_eq_liftFunctor_comp_ΛFun d A (fun s => γ (compMk s))

end Components

/-! ## 5. The componentwise classification (paper `prop:components`) -/

/-- The admissible lift `Λ_γ Ã` attached to `(γ, A) ∈ (π₀(S) → G) ⋊ H` (paper `prop:components`
    proof). -/
noncomputable def autBoxGOverOfComponents (d : OEData G p) (H : Subgroup (StrictAut S))
    (x : (CategoryTheory.ConnectedComponents S → G) ⋊[componentAction H G] H) : AutBoxGOver d H :=
  autBoxGOverOfMultiplier d H x.right (componentLiftMultiplier x.right.1.hom x.left)
    (fun u => componentLiftMultiplier_hom _ _ u)

/-- The lift attached to `(γ, A)` is `Λ_γ Ã`, Lean order `Ã ⋙ ΛFun d (γ ∘ [·])` (paper
    `prop:components` proof). -/
theorem autBoxGOverOfComponents_hom_eq (d : OEData G p) (H : Subgroup (StrictAut S))
    (x : (CategoryTheory.ConnectedComponents S → G) ⋊[componentAction H G] H) :
    (autBoxGOverOfComponents d H x).1.hom
      = liftFunctor d x.right.1.hom ⋙ ΛFun d (fun s => x.left (compMk s)) :=
  liftByMultiplier_components_eq d _ _

/-- The multiplier of the lift attached to `(γ, A)` at `s` is `γ [A s]` (paper `prop:components`,
    INSTR §5 parametrization). -/
theorem liftMultiplier_autBoxGOverOfComponents (d : OEData G p) (H : Subgroup (StrictAut S))
    (x : (CategoryTheory.ConnectedComponents S → G) ⋊[componentAction H G] H) (s : S) :
    liftMultiplier d (autBoxGOverOfComponents d H x).1.hom s = x.left (compMk (x.right.1.hom.obj s)) := by
  show liftMultiplier d (liftByMultiplier d _ _) s = _
  rw [liftMultiplier_liftByMultiplier]; rfl

/-- The component data `(γ, A)` of an admissible lift: `A = Φ(e)` and `γ [t] = k(A⁻¹ t)` with `k`
    the multiplier (paper `prop:components` proof). -/
def autBoxGOverToComponents (d : OEData G p) (H : Subgroup (StrictAut S)) (e : AutBoxGOver d H) :
    (CategoryTheory.ConnectedComponents S → G) ⋊[componentAction H G] H :=
  ⟨fun c => componentMultiplier d e.1.pres (componentMap e.1.base.inv c), ΦOver d H e⟩

/-- `(γ, A) ↦ Λ_γ Ã` is a group homomorphism for the semidirect law (paper `prop:components`).
    The paper's identity `Ã Λ_δ Ã⁻¹ = Λ_{δ ∘ A⁻¹}` is stated separately as
    `liftHomOver_conj_components` (group level) and `liftFunctor_conj_ΛFun_components`
    (functor level). -/
noncomputable def semidirectComponentsToAutBoxGOver (d : OEData G p) (H : Subgroup (StrictAut S)) :
    (CategoryTheory.ConnectedComponents S → G) ⋊[componentAction H G] H →* AutBoxGOver d H where
  toFun := autBoxGOverOfComponents d H
  map_one' := autBoxGOver_ext (by
    exact (liftByMultiplier_one d (𝟭 S)).trans (lift_id d))
  map_mul' x y := autBoxGOver_ext (by
    show liftByMultiplier d (y.right.1.hom ⋙ x.right.1.hom)
        (fun s => x.left (compMk (x.right.1.hom.obj (y.right.1.hom.obj s)))
          * y.left (compMk (x.right.1.inv.obj (x.right.1.hom.obj (y.right.1.hom.obj s)))))
      = liftByMultiplier d y.right.1.hom (fun s => y.left (compMk (y.right.1.hom.obj s)))
        ⋙ liftByMultiplier d x.right.1.hom (fun s => x.left (compMk (x.right.1.hom.obj s)))
    rw [liftByMultiplier_comp]
    congr 1
    funext s
    rw [show x.right.1.inv.obj (x.right.1.hom.obj (y.right.1.hom.obj s)) = y.right.1.hom.obj s
      from Functor.congr_obj x.right.1.hom_inv_id _])

/-- `autBoxGOverToComponents` is a left inverse of `autBoxGOverOfComponents` (paper
    `prop:components`: the expression `Λ_γ Ã` is unique). -/
theorem autBoxGOverToComponents_ofComponents (d : OEData G p) (H : Subgroup (StrictAut S))
    (x : (CategoryTheory.ConnectedComponents S → G) ⋊[componentAction H G] H) :
    autBoxGOverToComponents d H (autBoxGOverOfComponents d H x) = x := by
  refine SemidirectProduct.ext (funext fun c => ?_) rfl
  induction c using Quotient.ind with
  | _ a =>
    show liftMultiplier d (liftByMultiplier d x.right.1.hom (componentLiftMultiplier x.right.1.hom x.left))
        (x.right.1.inv.obj a) = x.left (compMk a)
    rw [liftMultiplier_liftByMultiplier]
    show x.left (compMk (x.right.1.hom.obj (x.right.1.inv.obj a))) = x.left (compMk a)
    rw [show x.right.1.hom.obj (x.right.1.inv.obj a) = a from Functor.congr_obj x.right.1.inv_hom_id a]

/-- `autBoxGOverOfComponents` is a left inverse of `autBoxGOverToComponents` (paper
    `prop:components`: every lift has an expression `Λ_γ Ã`). -/
theorem autBoxGOverOfComponents_toComponents (d : OEData G p) (H : Subgroup (StrictAut S))
    (e : AutBoxGOver d H) :
    autBoxGOverOfComponents d H (autBoxGOverToComponents d H e) = e := by
  refine autBoxGOver_ext ?_
  show liftByMultiplier d e.1.base.hom
      (fun s => liftMultiplier d e.1.hom (e.1.base.inv.obj (e.1.base.hom.obj s))) = e.1.hom
  have h : (fun s => liftMultiplier d e.1.hom (e.1.base.inv.obj (e.1.base.hom.obj s)))
      = liftMultiplier d e.1.hom := funext fun s => by
    rw [show e.1.base.inv.obj (e.1.base.hom.obj s) = s from Functor.congr_obj e.1.base.hom_inv_id s]
  rw [h]
  exact (eq_liftByMultiplier d e.1.equiv e.1.pres.covers).symm

/-- Componentwise classification (paper `prop:components`): for ANY base `S` (no connectedness,
    no nonemptiness),
    `Sym_H(p) ≃* (π₀(S) → G) ⋊ H`, `(A · γ)(c) = γ(A⁻¹ c)`.  The inverse sends `(γ, A)` to
    `Λ_γ Ã` (Lean `liftFunctor d A ⋙ ΛFun d (γ ∘ [·])`, `autBoxGOverOfComponents_hom_eq`). -/
noncomputable def autBoxGOverMulEquivComponents (d : OEData G p) (H : Subgroup (StrictAut S)) :
    AutBoxGOver d H ≃* (CategoryTheory.ConnectedComponents S → G) ⋊[componentAction H G] H :=
  (MulEquiv.mk
    ⟨semidirectComponentsToAutBoxGOver d H, autBoxGOverToComponents d H,
      autBoxGOverToComponents_ofComponents d H, autBoxGOverOfComponents_toComponents d H⟩
    (semidirectComponentsToAutBoxGOver d H).map_mul).symm

/-- (paper `prop:components`) -/
@[simp] theorem autBoxGOverMulEquivComponents_apply (d : OEData G p) (H : Subgroup (StrictAut S))
    (e : AutBoxGOver d H) :
    autBoxGOverMulEquivComponents d H e = autBoxGOverToComponents d H e := rfl

/-- (paper `prop:components`) -/
@[simp] theorem autBoxGOverMulEquivComponents_symm_apply (d : OEData G p)
    (H : Subgroup (StrictAut S))
    (x : (CategoryTheory.ConnectedComponents S → G) ⋊[componentAction H G] H) :
    (autBoxGOverMulEquivComponents d H).symm x = autBoxGOverOfComponents d H x := rfl

/-- The second coordinate of the classification is the base projection `ΦOver` (paper
    `prop:components`). -/
theorem autBoxGOverMulEquivComponents_right (d : OEData G p) (H : Subgroup (StrictAut S))
    (e : AutBoxGOver d H) : (autBoxGOverMulEquivComponents d H e).right = ΦOver d H e := rfl

/-- The first factor is realized by the componentwise translations: `(γ, 1) ↦ Λ_γ`, Lean
    `ΛFun d (γ ∘ [·])` (paper `prop:components` proof, `Λ_γ(s,g) = (s, γ([s]) g)`). -/
theorem autBoxGOverMulEquivComponents_symm_inl_hom (d : OEData G p) (H : Subgroup (StrictAut S))
    (γ : CategoryTheory.ConnectedComponents S → G) :
    ((autBoxGOverMulEquivComponents d H).symm (SemidirectProduct.inl γ)).1.hom
      = ΛFun d (fun s => γ (compMk s)) := by
  rw [autBoxGOverMulEquivComponents_symm_apply, autBoxGOverOfComponents_hom_eq]
  show liftFunctor d (𝟭 S) ⋙ _ = _
  rw [lift_id, Functor.id_comp]; rfl

/-- The second factor is realized by the canonical lifts: `(1, A) ↦ Ã = liftHomOver d H A` (paper
    `prop:components` proof, `γ = 1` in `Λ_γ Ã`). -/
theorem autBoxGOverMulEquivComponents_symm_inr (d : OEData G p) (H : Subgroup (StrictAut S))
    (A : H) :
    (autBoxGOverMulEquivComponents d H).symm (SemidirectProduct.inr A) = liftHomOver d H A := by
  refine autBoxGOver_ext ?_
  rw [autBoxGOverMulEquivComponents_symm_apply, autBoxGOverOfComponents_hom_eq]
  show _ ⋙ ΛFun d 1 = liftFunctor d A.1.hom
  rw [ΛFun_one, Functor.comp_id]; rfl

/-- Functor form of `autBoxGOverMulEquivComponents_symm_inr`: `(1, A) ↦ Ã = liftFunctor d A`
    (paper `prop:components` proof). -/
theorem autBoxGOverMulEquivComponents_symm_inr_hom (d : OEData G p) (H : Subgroup (StrictAut S))
    (A : H) :
    ((autBoxGOverMulEquivComponents d H).symm (SemidirectProduct.inr A)).1.hom
      = liftFunctor d A.1.hom := by
  rw [autBoxGOverMulEquivComponents_symm_inr]; rfl

/-- The key conjugation identity of paper `prop:components`, at group level in `AutBoxGOver d H`:
    `Ã Λ_δ Ã⁻¹ = Λ_{δ ∘ A⁻¹}`, where `Λ_δ` is the image of `(δ, 1)`, `Ã = liftHomOver d H A`, and
    `δ ∘ A⁻¹ = componentAction H G A δ`.  (Group multiplication is operator order.) -/
theorem liftHomOver_conj_components (d : OEData G p) (H : Subgroup (StrictAut S)) (A : H)
    (δ : CategoryTheory.ConnectedComponents S → G) :
    liftHomOver d H A * (autBoxGOverMulEquivComponents d H).symm (SemidirectProduct.inl δ)
        * (liftHomOver d H A)⁻¹
      = (autBoxGOverMulEquivComponents d H).symm
          (SemidirectProduct.inl (componentAction H G A δ)) := by
  rw [← autBoxGOverMulEquivComponents_symm_inr, ← map_inv, ← map_mul, ← map_mul,
    ← map_inv SemidirectProduct.inr, SemidirectProduct.inl_aut]

/-- The key conjugation identity of paper `prop:components` at functor level:
    `Ã Λ_δ Ã⁻¹ = Λ_{δ ∘ A⁻¹}`, Lean order
    `liftFunctor d A⁻¹ ⋙ ΛFun d (δ ∘ [·]) ⋙ liftFunctor d A = ΛFun d ((A · δ) ∘ [·])`. -/
theorem liftFunctor_conj_ΛFun_components (d : OEData G p) (H : Subgroup (StrictAut S)) (A : H)
    (δ : CategoryTheory.ConnectedComponents S → G) :
    liftFunctor d A.1.inv ⋙ ΛFun d (fun s => δ (compMk s)) ⋙ liftFunctor d A.1.hom
      = ΛFun d (fun s => componentAction H G A δ (compMk s)) :=
  liftFunctor_conj_ΛFun d A.1 _

/-! ## 6. Empty and connected bases (remarks after paper `prop:components`) -/

namespace Components

omit [Group G] in
/-- For an empty base the component functions form the trivial group (remark after paper
    `prop:components`: "For an empty base, `G^{π₀(S)}` is the trivial group"). -/
theorem componentFunctions_unique_of_isEmpty [IsEmpty S] :
    Nonempty (Unique (CategoryTheory.ConnectedComponents S → G)) := by
  haveI : IsEmpty (CategoryTheory.ConnectedComponents S) :=
    ⟨fun c => Quotient.inductionOn c (fun s => isEmptyElim s)⟩
  exact ⟨Pi.uniqueOfIsEmpty _⟩

/-- A preconnected base has at most one component (remark after paper `prop:components`). -/
theorem components_subsingleton [IsPreconnected S] :
    Subsingleton (CategoryTheory.ConnectedComponents S) :=
  ⟨fun c₁ c₂ => Quotient.inductionOn₂ c₁ c₂ (fun a b => Quotient.sound (isPreconnected_zigzag a b))⟩

/-- A connected base has exactly one component (remark after paper `prop:components`). -/
@[reducible] noncomputable def componentsUnique [IsConnected S] : Unique (CategoryTheory.ConnectedComponents S) :=
  { default := compMk (Classical.arbitrary S)
    uniq := fun c => (components_subsingleton).elim c _ }

end Components

/-- On a (pre)connected base the component action is trivial (remark after paper
    `prop:components`). -/
theorem componentAction_eq_one [IsPreconnected S] (H : Subgroup (StrictAut S)) :
    componentAction H G = 1 := by
  haveI := components_subsingleton (S := S)
  refine MonoidHom.ext fun A => MulEquiv.ext fun γ => funext fun c => ?_
  show γ (componentMap A.1.inv c) = γ c
  rw [Subsingleton.elim (componentMap A.1.inv c) c]

/-- On a connected base the first factor is `G` (remark after paper `prop:components`):
    evaluation at the unique component. -/
noncomputable def componentFunctionsMulEquiv [IsConnected S] :
    (CategoryTheory.ConnectedComponents S → G) ≃* G :=
  @MulEquiv.piUnique _ (fun _ => G) _ componentsUnique

/-- On a connected base the componentwise classification reduces to the direct product `G × H`
    (remark after paper `prop:components`; compare `autBoxGOverMulEquivProd`). -/
noncomputable def autBoxGOverMulEquivProdOfComponents (d : OEData G p)
    (H : Subgroup (StrictAut S)) [IsConnected S] : AutBoxGOver d H ≃* G × H :=
  (autBoxGOverMulEquivComponents d H).trans
    ((SemidirectProduct.congr (φ₂ := (1 : H →* MulAut G)) componentFunctionsMulEquiv
      (MulEquiv.refl H) (fun A => MulEquiv.ext fun γ => by
        haveI := components_subsingleton (S := S)
        show γ (componentMap A.1.inv _) = γ _
        exact congrArg γ (Subsingleton.elim _ _))).trans
      SemidirectProduct.mulEquivProd)

/-! ## 7. Unrestricted equivariant lifts (paper `prop:nocleavage`) -/

/-- An unrestricted equivariant lift over `H` (paper `prop:nocleavage`): a strict automorphism
    `hom` of `O` (with strict inverse `inv`) that is `G`-equivariant and covers `base ∈ H`,
    `hom ⋙ p = p ⋙ base.hom`.  NO transport-preservation condition is imposed. -/
@[ext]
structure AutEquivOver (d : OEData G p) (H : Subgroup (StrictAut S)) where
  hom : O ⥤ O
  inv : O ⥤ O
  hom_inv_id : hom ⋙ inv = 𝟭 O
  inv_hom_id : inv ⋙ hom = 𝟭 O
  base : H
  equiv : IsGEquivariant d hom
  covers : hom ⋙ p = p ⋙ base.1.hom

namespace AutEquivOver

variable {d : OEData G p} {H : Subgroup (StrictAut S)}

omit [Group G] in
/-- The covering equation is closed under composition (paper `prop:nocleavage`). -/
theorem covers_comp {F F' : O ⥤ O} {A A' : S ⥤ S} (hc : F ⋙ p = p ⋙ A)
    (hc' : F' ⋙ p = p ⋙ A') : (F ⋙ F') ⋙ p = p ⋙ (A ⋙ A') := by
  rw [Functor.assoc, hc', ← Functor.assoc, hc, Functor.assoc]

omit [Group G] in
/-- The covering equation transfers to strict inverses (paper `prop:nocleavage`). -/
theorem covers_inv {F Finv : O ⥤ O} {B : StrictAut S} (ih : Finv ⋙ F = 𝟭 O)
    (hc : F ⋙ p = p ⋙ B.hom) : Finv ⋙ p = p ⋙ B.inv := by
  have h1 : (Finv ⋙ p) ⋙ B.hom = p := by
    rw [Functor.assoc, ← hc, ← Functor.assoc, ih, Functor.id_comp]
  calc Finv ⋙ p
      = (Finv ⋙ p) ⋙ B.hom ⋙ B.inv := by rw [B.hom_inv_id, Functor.comp_id]
    _ = ((Finv ⋙ p) ⋙ B.hom) ⋙ B.inv := rfl
    _ = p ⋙ B.inv := by rw [h1]

/-- The group of unrestricted equivariant lifts over `H` (paper `prop:nocleavage`);
    multiplication is operator order, `(e₁ * e₂).hom = e₂.hom ⋙ e₁.hom`. -/
instance : Group (AutEquivOver d H) where
  mul e₁ e₂ :=
    { hom := e₂.hom ⋙ e₁.hom
      inv := e₁.inv ⋙ e₂.inv
      hom_inv_id := by
        show e₂.hom ⋙ (e₁.hom ⋙ e₁.inv) ⋙ e₂.inv = 𝟭 O
        rw [e₁.hom_inv_id, Functor.id_comp, e₂.hom_inv_id]
      inv_hom_id := by
        show e₁.inv ⋙ (e₂.inv ⋙ e₂.hom) ⋙ e₁.hom = 𝟭 O
        rw [e₂.inv_hom_id, Functor.id_comp, e₁.inv_hom_id]
      base := e₁.base * e₂.base
      equiv := isGEquivariant_comp d e₂.equiv e₁.equiv
      covers := covers_comp e₂.covers e₁.covers }
  one := ⟨𝟭 O, 𝟭 O, rfl, rfl, 1, id_isGEquivariant d, rfl⟩
  inv e :=
    { hom := e.inv
      inv := e.hom
      hom_inv_id := e.inv_hom_id
      inv_hom_id := e.hom_inv_id
      base := e.base⁻¹
      equiv := isGEquivariant_inv d e.hom_inv_id e.inv_hom_id e.equiv
      covers := covers_inv (B := e.base.1) e.inv_hom_id e.covers }
  mul_assoc a b c := by refine AutEquivOver.ext ?_ ?_ ?_ <;> rfl
  one_mul a := by refine AutEquivOver.ext ?_ ?_ ?_ <;> rfl
  mul_one a := by refine AutEquivOver.ext ?_ ?_ ?_ <;> rfl
  inv_mul_cancel a := by
    refine AutEquivOver.ext ?_ ?_ ?_ <;> first | exact a.hom_inv_id | exact inv_mul_cancel _

/-- (paper `prop:nocleavage`) -/
@[simp] lemma mul_hom (e₁ e₂ : AutEquivOver d H) : (e₁ * e₂).hom = e₂.hom ⋙ e₁.hom := rfl
/-- (paper `prop:nocleavage`) -/
@[simp] lemma mul_base (e₁ e₂ : AutEquivOver d H) : (e₁ * e₂).base = e₁.base * e₂.base := rfl
/-- (paper `prop:nocleavage`) -/
@[simp] lemma one_hom : (1 : AutEquivOver d H).hom = 𝟭 O := rfl
/-- (paper `prop:nocleavage`) -/
@[simp] lemma one_base : (1 : AutEquivOver d H).base = 1 := rfl
/-- (paper `prop:nocleavage`) -/
@[simp] lemma inv_hom (e : AutEquivOver d H) : e⁻¹.hom = e.inv := rfl

/-- An unrestricted lift is determined by its total functor and its base (paper
    `prop:nocleavage`; the strict inverse is unique). -/
theorem ext_hom {e₁ e₂ : AutEquivOver d H} (h : e₁.hom = e₂.hom) (hb : e₁.base = e₂.base) :
    e₁ = e₂ := by
  refine AutEquivOver.ext h ?_ hb
  calc e₁.inv = e₁.inv ⋙ (e₂.hom ⋙ e₂.inv) := by rw [e₂.hom_inv_id, Functor.comp_id]
    _ = e₁.inv ⋙ (e₁.hom ⋙ e₂.inv) := by rw [h]
    _ = (e₁.inv ⋙ e₁.hom) ⋙ e₂.inv := rfl
    _ = e₂.inv := by rw [e₁.inv_hom_id, Functor.id_comp]

end AutEquivOver

/-- The base projection `AutEquivOver d H →* H` (paper `prop:nocleavage`). -/
def ΦEquivOver (d : OEData G p) (H : Subgroup (StrictAut S)) : AutEquivOver d H →* H where
  toFun e := e.base
  map_one' := rfl
  map_mul' _ _ := rfl

/-- (paper `prop:nocleavage`) -/
@[simp] theorem ΦEquivOver_apply (d : OEData G p) (H : Subgroup (StrictAut S))
    (e : AutEquivOver d H) : ΦEquivOver d H e = e.base := rfl

/-- The unrestricted lift over `A ∈ H` defined by an arbitrary multiplier `k : S → G` (paper
    `prop:nocleavage` proof: "the first part of Lemma `lem:local` applies to every function `k`,
    without the constancy condition"). -/
noncomputable def autEquivOverOfMultiplier (d : OEData G p) (H : Subgroup (StrictAut S)) (A : H)
    (k : S → G) : AutEquivOver d H where
  hom := liftByMultiplier d A.1.hom k
  inv := liftByMultiplier d A.1.inv (fun t => (k (A.1.inv.obj t))⁻¹)
  hom_inv_id := liftByMultiplier_comp_inv d A.1 k
  inv_hom_id := liftByMultiplier_inv_comp d A.1 k
  base := A
  equiv := liftByMultiplier_isGEquivariant d A.1.hom k
  covers := liftByMultiplier_covers d A.1.hom k

/-- The unrestricted lift `Λ_γ Ã` attached to `(γ, A) ∈ (S → G) ⋊ H` (paper `prop:nocleavage`
    proof); its multiplier at `s` is `γ(A s)`. -/
noncomputable def autEquivOverOfObject (d : OEData G p) (H : Subgroup (StrictAut S))
    (x : (S → G) ⋊[objectAction H G] H) : AutEquivOver d H :=
  autEquivOverOfMultiplier d H x.right (fun s => x.left (x.right.1.hom.obj s))

/-- The lift attached to `(γ, A)` is `Λ_γ Ã`, Lean order `Ã ⋙ ΛFun d γ` with
    `Λ_γ(s,g) = (s, γ(s) g)` (paper `prop:nocleavage` proof). -/
theorem autEquivOverOfObject_hom_eq (d : OEData G p) (H : Subgroup (StrictAut S))
    (x : (S → G) ⋊[objectAction H G] H) :
    (autEquivOverOfObject d H x).hom = liftFunctor d x.right.1.hom ⋙ ΛFun d x.left :=
  liftByMultiplier_eq_liftFunctor_comp_ΛFun d _ _

/-- The data `(γ, A)` of an unrestricted lift: `A` its base and `γ(t) = k(A⁻¹ t)` with `k` its
    multiplier (paper `prop:nocleavage` proof). -/
def autEquivOverToObject (d : OEData G p) (H : Subgroup (StrictAut S)) (e : AutEquivOver d H) :
    (S → G) ⋊[objectAction H G] H :=
  ⟨fun t => liftMultiplier d e.hom (e.base.1.inv.obj t), e.base⟩

/-- `(γ, A) ↦ Λ_γ Ã` is a group homomorphism for the semidirect law (paper `prop:nocleavage`).
    The paper's "conjugation by `Ã` gives the displayed action" is stated separately as
    `autEquivOver_conj_object` (group level) and `Components.liftFunctor_conj_ΛFun`
    (functor level). -/
noncomputable def semidirectObjectToAutEquivOver (d : OEData G p) (H : Subgroup (StrictAut S)) :
    (S → G) ⋊[objectAction H G] H →* AutEquivOver d H where
  toFun := autEquivOverOfObject d H
  map_one' := AutEquivOver.ext_hom ((liftByMultiplier_one d (𝟭 S)).trans (lift_id d)) rfl
  map_mul' x y := AutEquivOver.ext_hom (by
    show liftByMultiplier d (y.right.1.hom ⋙ x.right.1.hom)
        (fun s => x.left (x.right.1.hom.obj (y.right.1.hom.obj s))
          * y.left (x.right.1.inv.obj (x.right.1.hom.obj (y.right.1.hom.obj s))))
      = liftByMultiplier d y.right.1.hom (fun s => y.left (y.right.1.hom.obj s))
        ⋙ liftByMultiplier d x.right.1.hom (fun s => x.left (x.right.1.hom.obj s))
    rw [liftByMultiplier_comp]
    congr 1
    funext s
    rw [show x.right.1.inv.obj (x.right.1.hom.obj (y.right.1.hom.obj s)) = y.right.1.hom.obj s
      from Functor.congr_obj x.right.1.hom_inv_id _]) rfl

/-- (paper `prop:nocleavage`: the expression `Λ_γ Ã` is unique) -/
theorem autEquivOverToObject_ofObject (d : OEData G p) (H : Subgroup (StrictAut S))
    (x : (S → G) ⋊[objectAction H G] H) :
    autEquivOverToObject d H (autEquivOverOfObject d H x) = x := by
  refine SemidirectProduct.ext (funext fun t => ?_) rfl
  show liftMultiplier d (liftByMultiplier d x.right.1.hom (fun s => x.left (x.right.1.hom.obj s)))
      (x.right.1.inv.obj t) = x.left t
  rw [liftMultiplier_liftByMultiplier]
  show x.left (x.right.1.hom.obj (x.right.1.inv.obj t)) = x.left t
  rw [show x.right.1.hom.obj (x.right.1.inv.obj t) = t from Functor.congr_obj x.right.1.inv_hom_id t]

/-- (paper `prop:nocleavage`: every unrestricted lift has an expression `Λ_γ Ã`) -/
theorem autEquivOverOfObject_toObject (d : OEData G p) (H : Subgroup (StrictAut S))
    (e : AutEquivOver d H) : autEquivOverOfObject d H (autEquivOverToObject d H e) = e := by
  refine AutEquivOver.ext_hom ?_ rfl
  show liftByMultiplier d e.base.1.hom
      (fun s => liftMultiplier d e.hom (e.base.1.inv.obj (e.base.1.hom.obj s))) = e.hom
  have h : (fun s => liftMultiplier d e.hom (e.base.1.inv.obj (e.base.1.hom.obj s)))
      = liftMultiplier d e.hom := funext fun s => by
    rw [show e.base.1.inv.obj (e.base.1.hom.obj s) = s from Functor.congr_obj e.base.1.hom_inv_id s]
  rw [h]
  exact (eq_liftByMultiplier d e.equiv e.covers).symm

/-- Unrestricted equivariant lifts (paper `prop:nocleavage`): retaining the normalized datum but
    imposing only covering and equivariance, the group over `H` is
    `(S → G) ⋊ H`, `(A · γ)(s) = γ(A⁻¹ s)`.  No connectedness or nonemptiness. -/
noncomputable def autEquivOverMulEquiv (d : OEData G p) (H : Subgroup (StrictAut S)) :
    AutEquivOver d H ≃* (S → G) ⋊[objectAction H G] H :=
  (MulEquiv.mk
    ⟨semidirectObjectToAutEquivOver d H, autEquivOverToObject d H,
      autEquivOverToObject_ofObject d H, autEquivOverOfObject_toObject d H⟩
    (semidirectObjectToAutEquivOver d H).map_mul).symm

/-- (paper `prop:nocleavage`) -/
@[simp] theorem autEquivOverMulEquiv_apply (d : OEData G p) (H : Subgroup (StrictAut S))
    (e : AutEquivOver d H) : autEquivOverMulEquiv d H e = autEquivOverToObject d H e := rfl

/-- (paper `prop:nocleavage`) -/
@[simp] theorem autEquivOverMulEquiv_symm_apply (d : OEData G p) (H : Subgroup (StrictAut S))
    (x : (S → G) ⋊[objectAction H G] H) :
    (autEquivOverMulEquiv d H).symm x = autEquivOverOfObject d H x := rfl

/-- The second coordinate is the base projection (paper `prop:nocleavage`). -/
theorem autEquivOverMulEquiv_right (d : OEData G p) (H : Subgroup (StrictAut S))
    (e : AutEquivOver d H) : (autEquivOverMulEquiv d H e).right = ΦEquivOver d H e := rfl

/-- The kernel over `id_S` (paper `prop:nocleavage`: "Its kernel over `id_S` is `G^{Ob(S)}`"):
    `(ΦEquivOver d H).ker ≃* (S → G)`, `e ↦ γ` with `e = Λ_γ`. -/
noncomputable def kerΦEquivOverMulEquiv (d : OEData G p) (H : Subgroup (StrictAut S)) :
    (ΦEquivOver d H).ker ≃* (S → G) where
  toFun e := (autEquivOverMulEquiv d H e.1).left
  invFun γ := ⟨(autEquivOverMulEquiv d H).symm (SemidirectProduct.inl γ), MonoidHom.mem_ker.2 rfl⟩
  left_inv e := by
    have hr : (autEquivOverMulEquiv d H e.1).right = 1 := MonoidHom.mem_ker.1 e.2
    refine Subtype.ext ?_
    apply (autEquivOverMulEquiv d H).injective
    rw [MulEquiv.apply_symm_apply]
    exact SemidirectProduct.ext rfl hr.symm
  right_inv γ := by
    show (autEquivOverMulEquiv d H ((autEquivOverMulEquiv d H).symm (SemidirectProduct.inl γ))).left
      = γ
    rw [MulEquiv.apply_symm_apply]; rfl
  map_mul' e₁ e₂ := by
    have hr : (autEquivOverMulEquiv d H e₁.1).right = 1 := MonoidHom.mem_ker.1 e₁.2
    show (autEquivOverMulEquiv d H (e₁.1 * e₂.1)).left
      = (autEquivOverMulEquiv d H e₁.1).left * (autEquivOverMulEquiv d H e₂.1).left
    rw [map_mul, SemidirectProduct.mul_left, hr, map_one, MulAut.one_apply]

/-- The kernel element attached to `γ : S → G` is the object-function translation `Λ_γ`, Lean
    `ΛFun d γ` (paper `prop:nocleavage`). -/
theorem kerΦEquivOverMulEquiv_symm_hom (d : OEData G p) (H : Subgroup (StrictAut S))
    (γ : S → G) : ((kerΦEquivOverMulEquiv d H).symm γ).1.hom = ΛFun d γ := by
  show (autEquivOverOfObject d H (SemidirectProduct.inl γ)).hom = ΛFun d γ
  rw [autEquivOverOfObject_hom_eq]
  show liftFunctor d (𝟭 S) ⋙ _ = _
  rw [lift_id, Functor.id_comp]; rfl

/-- An unrestricted lift preserves the chosen transport iff its first coordinate `γ` is constant
    along every base arrow (paper `prop:nocleavage` vs `prop:components`). -/
theorem autEquivOver_preservesCleavage_iff (d : OEData G p) (H : Subgroup (StrictAut S))
    (e : AutEquivOver d H) :
    PreservesCleavage d e.hom e.base.1.hom ↔
      ∀ {s t : S} (_ : s ⟶ t),
        (autEquivOverMulEquiv d H e).left s = (autEquivOverMulEquiv d H e).left t := by
  rw [preservesCleavage_iff_multiplier d e.equiv e.covers]
  have hAA : ∀ s, e.base.1.inv.obj (e.base.1.hom.obj s) = s :=
    fun s => Functor.congr_obj e.base.1.hom_inv_id s
  constructor
  · intro h s t u
    exact h (e.base.1.inv.map u)
  · intro h s t u
    have h' : liftMultiplier d e.hom (e.base.1.inv.obj (e.base.1.hom.obj s))
        = liftMultiplier d e.hom (e.base.1.inv.obj (e.base.1.hom.obj t)) := h (e.base.1.hom.map u)
    rwa [hAA, hAA] at h'

/-- Forgetting transport preservation embeds the admissible lifts into the unrestricted ones
    (paper `prop:nocleavage` vs `def:lifts`). -/
def autBoxGOverToAutEquivOver (d : OEData G p) (H : Subgroup (StrictAut S)) :
    AutBoxGOver d H →* AutEquivOver d H where
  toFun e := ⟨e.1.hom, e.1.inv, e.1.hom_inv_id, e.1.inv_hom_id, ΦOver d H e, e.1.equiv,
    e.1.pres.covers⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- (paper `prop:nocleavage`) -/
@[simp] theorem autBoxGOverToAutEquivOver_hom (d : OEData G p) (H : Subgroup (StrictAut S))
    (e : AutBoxGOver d H) : (autBoxGOverToAutEquivOver d H e).hom = e.1.hom := rfl

/-- The forgetful map is injective (paper `prop:nocleavage`). -/
theorem autBoxGOverToAutEquivOver_injective (d : OEData G p) (H : Subgroup (StrictAut S)) :
    Function.Injective (autBoxGOverToAutEquivOver d H) :=
  fun _ _ h => autBoxGOver_ext (congrArg AutEquivOver.hom h)

/-- The forgetful map commutes with the base projections (paper `prop:nocleavage`). -/
theorem ΦEquivOver_comp_autBoxGOverToAutEquivOver (d : OEData G p) (H : Subgroup (StrictAut S)) :
    (ΦEquivOver d H).comp (autBoxGOverToAutEquivOver d H) = ΦOver d H := rfl

/-- The image of the forgetful map is exactly the transport-preserving unrestricted lifts (paper
    `prop:nocleavage` vs `def:lifts`). -/
theorem mem_range_autBoxGOverToAutEquivOver_iff (d : OEData G p) (H : Subgroup (StrictAut S))
    (e : AutEquivOver d H) :
    e ∈ (autBoxGOverToAutEquivOver d H).range ↔ PreservesCleavage d e.hom e.base.1.hom := by
  constructor
  · rintro ⟨e', rfl⟩
    exact e'.1.pres
  · intro pc
    exact ⟨⟨⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id, e.base.1, e.equiv, pc⟩, e.base.2⟩, rfl⟩

/-- The second factor of paper `prop:nocleavage` is realized by the canonical lifts, functor form:
    `(1, A) ↦ Ã = liftFunctor d A`. -/
theorem autEquivOverMulEquiv_symm_inr_hom (d : OEData G p) (H : Subgroup (StrictAut S)) (A : H) :
    ((autEquivOverMulEquiv d H).symm (SemidirectProduct.inr A)).hom = liftFunctor d A.1.hom := by
  rw [autEquivOverMulEquiv_symm_apply, autEquivOverOfObject_hom_eq]
  show _ ⋙ ΛFun d 1 = _
  rw [ΛFun_one, Functor.comp_id]; rfl

/-- `(1, A)` goes to the canonical lift `liftHomOver d H A`, viewed as an unrestricted lift
    (paper `prop:nocleavage` proof). -/
theorem autEquivOverMulEquiv_symm_inr (d : OEData G p) (H : Subgroup (StrictAut S)) (A : H) :
    (autEquivOverMulEquiv d H).symm (SemidirectProduct.inr A)
      = autBoxGOverToAutEquivOver d H (liftHomOver d H A) :=
  AutEquivOver.ext_hom (autEquivOverMulEquiv_symm_inr_hom d H A) rfl

/-- Paper `prop:nocleavage` proof, "conjugation by `Ã` gives the displayed action", at group level
    in `AutEquivOver d H`: `Ã Λ_δ Ã⁻¹ = Λ_{δ ∘ A⁻¹}` for every object function `δ : S → G`, with
    `δ ∘ A⁻¹ = objectAction H G A δ`.  The functor-level form is `liftFunctor_conj_ΛFun`. -/
theorem autEquivOver_conj_object (d : OEData G p) (H : Subgroup (StrictAut S)) (A : H)
    (δ : S → G) :
    autBoxGOverToAutEquivOver d H (liftHomOver d H A)
        * (autEquivOverMulEquiv d H).symm (SemidirectProduct.inl δ)
        * (autBoxGOverToAutEquivOver d H (liftHomOver d H A))⁻¹
      = (autEquivOverMulEquiv d H).symm (SemidirectProduct.inl (objectAction H G A δ)) := by
  rw [← autEquivOverMulEquiv_symm_inr, ← map_inv, ← map_mul, ← map_mul,
    ← map_inv SemidirectProduct.inr, SemidirectProduct.inl_aut]

/-! ## 8. Example: a disconnected base need not give a direct product

Remark after paper `prop:components`: "A disconnected base need not give a direct product: `H` may
permute its components."  Witness: the discrete base on `Fin 2` (two components) with the swap
`i ↦ i.rev`; for any `H` containing the swap and any nontrivial `G`, the component action is
nontrivial, and in `Sym_H(p)` the canonical lift of the swap does not commute with a componentwise
translation (contrast `ΛHomOver_comm_liftHomOver` in the connected case). -/

namespace ComponentsSwapExample

/-- The swap `i ↦ i.rev` of the discrete two-object base (remark after paper `prop:components`). -/
def discSwapFunctor : Discrete (Fin 2) ⥤ Discrete (Fin 2) :=
  Discrete.functor (fun i => Discrete.mk i.rev)

/-- The swap is an involution (remark after paper `prop:components`). -/
theorem discSwapFunctor_comp_self :
    discSwapFunctor ⋙ discSwapFunctor = 𝟭 (Discrete (Fin 2)) :=
  CategoryTheory.Functor.ext (fun i => by
    show Discrete.mk i.as.rev.rev = i
    rw [Fin.rev_rev]) (fun _ _ _ => Subsingleton.elim _ _)

/-- The swap as a strict base automorphism (remark after paper `prop:components`). -/
def discSwapAut : StrictAut (Discrete (Fin 2)) :=
  ⟨discSwapFunctor, discSwapFunctor, discSwapFunctor_comp_self, discSwapFunctor_comp_self⟩

/-- The discrete base on `Fin 2` has two distinct components (remark after paper
    `prop:components`: a disconnected base). -/
theorem compMk_zero_ne_one :
    compMk (Discrete.mk (0 : Fin 2)) ≠ compMk (Discrete.mk (1 : Fin 2)) := by
  intro h
  have := congrArg (liftComp (fun s : Discrete (Fin 2) => s.as)
    (fun u => Discrete.eq_of_hom u)) h
  exact absurd this (by decide)

/-- The swap sends the component of `0` to the component of `1` (remark after paper
    `prop:components`). -/
theorem componentPerm_discSwapAut_zero :
    componentPerm discSwapAut (compMk (Discrete.mk 0)) = compMk (Discrete.mk 1) := rfl

/-- The swap permutes the components nontrivially (remark after paper `prop:components`: "`H` may
    permute its components"). -/
theorem componentPerm_discSwapAut_ne_one : componentPerm discSwapAut ≠ 1 := fun h =>
  compMk_zero_ne_one ((congrArg (fun π => π (compMk (Discrete.mk 0))) h).symm.trans
    componentPerm_discSwapAut_zero)

/-- The component function equal to `g` on the component of `0` and to `1` on the other one
    (remark after paper `prop:components`). -/
def indicatorZero (g : G) : CategoryTheory.ConnectedComponents (Discrete (Fin 2)) → G :=
  liftComp (fun s : Discrete (Fin 2) => if s.as = 0 then g else 1)
    (fun u => by rw [Discrete.eq_of_hom u])

/-- For `g ≠ 1`, the swap moves `indicatorZero g` (remark after paper `prop:components`). -/
theorem componentAction_discSwap_indicatorZero_ne {g : G} (hg : g ≠ 1)
    (H : Subgroup (StrictAut (Discrete (Fin 2)))) (hH : discSwapAut ∈ H) :
    componentAction H G ⟨discSwapAut, hH⟩ (indicatorZero g) ≠ indicatorZero g := fun h =>
  hg ((congrFun h (compMk (Discrete.mk 0))).symm.trans (by rfl))

/-- A disconnected base need not give a direct product (remark after paper `prop:components`): for
    nontrivial `G` and any `H` containing the swap, the component action is nontrivial, so the
    semidirect product `(π₀(S) → G) ⋊ H` of `prop:components` is not the direct one. -/
theorem componentAction_ne_one [Nontrivial G] (H : Subgroup (StrictAut (Discrete (Fin 2))))
    (hH : discSwapAut ∈ H) : componentAction H G ≠ 1 := by
  intro h
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact componentAction_discSwap_indicatorZero_ne hg H hH
    (DFunLike.congr_fun (DFunLike.congr_fun h ⟨discSwapAut, hH⟩) (indicatorZero g))

/-- The case `H = ⟨swap⟩`, the subgroup generated by the swap (remark after paper
    `prop:components`). -/
theorem componentAction_zpowers_ne_one [Nontrivial G] :
    componentAction (Subgroup.zpowers discSwapAut) G ≠ 1 :=
  componentAction_ne_one (Subgroup.zpowers discSwapAut) (Subgroup.mem_zpowers _)

/-- In `Sym_H(p)` over the discrete two-object base, the canonical lift of the swap does not
    commute with the componentwise translation `Λ_γ`, `γ = indicatorZero g`, `g ≠ 1` (remark after
    paper `prop:components`; contrast `ΛHomOver_comm_liftHomOver`). -/
theorem liftHomOver_discSwap_not_comm {q : O ⥤ Discrete (Fin 2)} (d : OEData G q)
    (H : Subgroup (StrictAut (Discrete (Fin 2)))) (hH : discSwapAut ∈ H) {g : G} (hg : g ≠ 1) :
    liftHomOver d H ⟨discSwapAut, hH⟩
        * (autBoxGOverMulEquivComponents d H).symm (SemidirectProduct.inl (indicatorZero g))
      ≠ (autBoxGOverMulEquivComponents d H).symm (SemidirectProduct.inl (indicatorZero g))
        * liftHomOver d H ⟨discSwapAut, hH⟩ := by
  intro h
  rw [← autBoxGOverMulEquivComponents_symm_inr, ← map_mul, ← map_mul] at h
  have h' := congrArg SemidirectProduct.left ((autBoxGOverMulEquivComponents d H).symm.injective h)
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left] at h'
  apply componentAction_discSwap_indicatorZero_ne hg H hH
  simpa using h'

end ComponentsSwapExample
