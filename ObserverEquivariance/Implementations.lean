import ObserverEquivariance.Comparisons
import ObserverEquivariance.LocalLifts

/-!
# Invariant implementations of twisted lifts (`prop:data-implementation`)

The criterion is for one selected base transformation. It asserts no automatic
coherence for a family of implementations indexed by a group.
-/

open CategoryTheory

variable {S C G : Type*} [Category S] [Category C] [Group G]

namespace ResidualData

/-- Pull residual data back along a base functor and a fibre automorphism. -/
def twisted (D : ResidualData S C G) (A : S ⥤ S) (θ : MulAut G) :
    ResidualData S C G where
  E := A ⋙ D.E
  σ s := (D.σ (A.obj s)).comp θ.toMonoidHom
  natural u r := D.natural (A.map u) (θ r)

/-- Computation of the residual data after the canonical twisted product lift. -/
theorem twisted_presentationFunctor (D : ResidualData S C G) (A : S ⥤ S) (θ : MulAut G) :
    multiplierProductFunctorθ A θ (fun _ => 1) ⋙ D.presentationFunctor =
      (D.twisted A θ).presentationFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun X Y f => ?_)
  change (D.σ (A.obj X.1) (1 * θ Y.2.pt * (1 * θ X.2.pt)⁻¹)).hom ≫
    D.E.map (A.map f.1) =
      𝟙 _ ≫ ((D.σ (A.obj X.1) (θ (Y.2.pt * X.2.pt⁻¹))).hom ≫
        D.E.map (A.map f.1)) ≫ 𝟙 _
  simp only [one_mul, map_mul, map_inv, Category.id_comp, Category.comp_id]

/-- The product formula is the canonical lift of `thm:twisted`, including its action on arrows. -/
theorem canonical_product_lift_eq (A : S ⥤ S) (θ : MulAut G) :
    liftFunctorθ (productData S G) A θ = multiplierProductFunctorθ A θ (fun _ => 1) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun X Y f => ?_)
  apply ProductModel.productHom_ext
  have h := Functor.congr_hom (liftθ_covers (productData S G) A θ) f
  change ((liftFunctorθ (productData S G) A θ).map f).1 =
    𝟙 _ ≫ A.map f.1 ≫ 𝟙 _ at h ⊢
  exact h

theorem liftFunctorθ_comp_presentationFunctor (D : ResidualData S C G)
    (A : S ⥤ S) (θ : MulAut G) :
    liftFunctorθ (productData S G) A θ ⋙ D.presentationFunctor =
      (D.twisted A θ).presentationFunctor := by
  rw [canonical_product_lift_eq, twisted_presentationFunctor]

/-- Invariant implementation of the residual data of a canonical twisted lift. -/
def InvariantImplementation (D : ResidualData S C G) (A : S ⥤ S) (θ : MulAut G) :=
  {α : (D.twisted A θ).presentationFunctor ≅ D.presentationFunctor //
    IsInvariantNatTrans (productData S G) (D.twisted A θ).presentationFunctor_isInvariant
      D.presentationFunctor_isInvariant α.hom}

/-- Base-level isomorphism satisfying the twisted intertwining equations. -/
def TwistedIntertwiner (D : ResidualData S C G) (A : S ⥤ S) (θ : MulAut G) :=
  {β : A ⋙ D.E ≅ D.E // ∀ (s : S) (r : G),
    (D.σ (A.obj s) (θ r)).hom ≫ β.hom.app s = β.hom.app s ≫ (D.σ s r).hom}

/-- The bijection in `prop:data-implementation`. -/
def implementationEquiv (D : ResidualData S C G) (A : S ⥤ S) (θ : MulAut G) :
    D.InvariantImplementation A θ ≃ D.TwistedIntertwiner A θ where
  toFun α := ⟨restrictComparisonIso α.val, by
    have h := (comparison_invariant_iff (restrictComparison α.val.hom)).mp
      ((comparison_restrictComparison α.val.hom).symm ▸ α.property)
    exact h⟩
  invFun β := ⟨comparisonIso β.val,
    (comparison_invariant_iff (D := D.twisted A θ) (D' := D) β.val.hom).mpr β.property⟩
  left_inv α := by
    apply Subtype.ext
    apply Iso.ext
    exact comparison_restrictComparison α.val.hom
  right_inv β := by
    apply Subtype.ext
    apply Iso.ext
    exact restrictComparison_comparison (D := D.twisted A θ) (D' := D) β.val.hom

/-- Invariant implementations have the coordinate-independent components stated in
    `prop:data-implementation`. -/
theorem implementation_app (D : ResidualData S C G) (A : S ⥤ S) (θ : MulAut G)
    (α : D.InvariantImplementation A θ) (s : S) (a : G) :
    α.val.hom.app (s, ⟨a⟩) = (D.implementationEquiv A θ α).val.hom.app s := by
  change α.val.hom.app (s, ⟨a⟩) = α.val.hom.app (s, ⟨1⟩)
  exact (invariant_iff_constant α.val.hom).mp α.property s a

theorem invariant_implementation_iff (D : ResidualData S C G) (A : S ⥤ S) (θ : MulAut G) :
    Nonempty (D.InvariantImplementation A θ) ↔
      ∃ β : A ⋙ D.E ≅ D.E, ∀ (s : S) (r : G),
        (D.σ (A.obj s) (θ r)).hom ≫ β.hom.app s = β.hom.app s ≫ (D.σ s r).hom := by
  constructor
  · rintro ⟨α⟩
    exact ⟨(D.implementationEquiv A θ α).val, (D.implementationEquiv A θ α).property⟩
  · rintro ⟨β, hβ⟩
    exact ⟨(D.implementationEquiv A θ).symm ⟨β, hβ⟩⟩

theorem multiplier_product_lift_eq (A : S ⥤ S) (θ : MulAut G) (k : S → G) :
    liftByMultiplierθ (productData S G) A θ k = multiplierProductFunctorθ A θ k := by
  refine CategoryTheory.Functor.ext (fun X => ?_) (fun X Y f => ?_)
  · simp [liftByMultiplierθ, multiplierProductFunctorθ, productData]
  · apply ProductModel.productHom_ext
    have h := Functor.congr_hom (liftByMultiplierθ_covers (productData S G) A θ k) f
    change ((liftByMultiplierθ (productData S G) A θ k).map f).1 =
      𝟙 _ ≫ A.map f.1 ≫ 𝟙 _ at h ⊢
    exact h

/-- With an abelian presentation group, constant fibre translations do not change
the residual data after a twisted lift. -/
theorem translated_twisted_presentationFunctor {K : Type*} [CommGroup K]
    (D : ResidualData S C K) (A : S ⥤ S) (θ : MulAut K) (a : K) :
    multiplierProductFunctorθ A θ (fun _ => a) ⋙ D.presentationFunctor =
      (D.twisted A θ).presentationFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun X Y f => ?_)
  have h : a * θ Y.2.pt * (a * θ X.2.pt)⁻¹ = θ (Y.2.pt * X.2.pt⁻¹) := by
    simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
  change (D.σ (A.obj X.1) (a * θ Y.2.pt * (a * θ X.2.pt)⁻¹)).hom ≫
    D.E.map (A.map f.1) =
      𝟙 _ ≫ ((D.σ (A.obj X.1) (θ (Y.2.pt * X.2.pt⁻¹))).hom ≫
        D.E.map (A.map f.1)) ≫ 𝟙 _
  rw [h]
  simp only [Category.id_comp, Category.comp_id]

theorem translated_lift_comp_presentationFunctor {K : Type*} [CommGroup K]
    (D : ResidualData S C K) (A : S ⥤ S) (θ : MulAut K) (a : K) :
    (liftFunctorθ (productData S K) A θ ⋙ Λ (productData S K) a) ⋙
        D.presentationFunctor = (D.twisted A θ).presentationFunctor := by
  rw [← liftByMultiplierθ_const, multiplier_product_lift_eq,
    translated_twisted_presentationFunctor]

end ResidualData
