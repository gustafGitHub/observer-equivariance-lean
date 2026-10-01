import ObserverEquivariance.Calibration
import ObserverEquivariance.ProductModel

/-!
# Comparisons and prescribed targets (`prop:comparisons`)

The statements are expressed in the strict product normal form, with arbitrary
base and target categories. `ResidualData.presentationFunctor` is the
functor `residualQ S G ⋙ D.toFunctor`, not an additional hypothesis on the data.
All natural transformations are recovered from their components at coordinate 1.
-/

open CategoryTheory

variable {S C G : Type*} [Category S] [Category C] [Group G]

namespace ResidualData

abbrev presentationFunctor (D : ResidualData S C G) :=
  residualQ.{_, _, _, 0} S G ⋙ D.toFunctor

private theorem one_aut_hom {X : C} : (1 : CategoryTheory.Aut X).hom = 𝟙 X := rfl
private theorem one_aut_inv {X : C} : (1 : CategoryTheory.Aut X).inv = 𝟙 X := rfl
attribute [local simp] one_aut_hom one_aut_inv

private theorem self_casts {X Y : C} (h : X = X) (f : X ⟶ Y) (h' : Y = Y) :
    eqToHom h ≫ f ≫ eqToHom h' = f := by simp

theorem presentation_map_section (D : ResidualData S C G) {s t : S} (u : s ⟶ t) :
    D.presentationFunctor.map (Residual.pairArr u (1 : G) 1) = D.E.map u := by
  change (D.σ s (1 * 1⁻¹)).hom ≫ D.E.map u = D.E.map u
  rw [inv_one, mul_one, map_one]
  exact Category.id_comp _

theorem presentation_map_vertical (D : ResidualData S C G) (s : S) (a : G) :
    D.presentationFunctor.map (Residual.pairArr (𝟙 s) (1 : G) a) = (D.σ s a).hom := by
  change (D.σ s (a * 1⁻¹)).hom ≫ D.E.map (𝟙 s) = (D.σ s a).hom
  rw [inv_one, mul_one, D.E.map_id]
  exact Category.comp_id _

theorem presentationFunctor_isInvariant (D : ResidualData S C G) :
    OEData.IsInvariant (productData S G) D.presentationFunctor := by
  intro h
  rw [productData_actFunctor, presentationFunctor, ← Functor.assoc, residualQ_invariant]

/-- The unrestricted comparison from the base data has components `σ_s(a)`. -/
def presentationIso (D : ResidualData S C G) :
    CategoryTheory.Prod.fst S (Pair G) ⋙ D.E ≅ D.presentationFunctor :=
  NatIso.ofComponents (fun X => D.σ X.1 X.2.pt) (by
    intro X Y f
    change D.E.map f.1 ≫ (D.σ Y.1 Y.2.pt).hom =
      (D.σ X.1 X.2.pt).hom ≫
        ((D.σ X.1 (Y.2.pt * X.2.pt⁻¹)).hom ≫ D.E.map f.1)
    simp only [map_mul, Aut.Aut_mul_def, Iso.trans_hom, map_inv,
      Aut.Aut_inv_def, Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
    exact (D.natural f.1 Y.2.pt).symm)

/-- Extend any natural transformation of base data, without an intertwining assumption. -/
def comparison {D D' : ResidualData S C G} (β : D.E ⟶ D'.E) :
    D.presentationFunctor ⟶ D'.presentationFunctor :=
  D.presentationIso.inv ≫ Functor.whiskerLeft (CategoryTheory.Prod.fst S (Pair G)) β ≫
    D'.presentationIso.hom

@[simp] theorem comparison_app {D D' : ResidualData S C G} (β : D.E ⟶ D'.E)
    (s : S) (a : G) :
    (comparison β).app (s, ⟨a⟩) = (D.σ s a).inv ≫ β.app s ≫ (D'.σ s a).hom := rfl

theorem comparison_app_residual {D D' : ResidualData S C G} (β : D.E ⟶ D'.E)
    (s : S) (a : G) :
    (comparison β).app (s, ⟨a⟩) =
      (D.σ s a⁻¹).hom ≫ β.app s ≫ (D'.σ s a).hom := by
  simp only [comparison_app, map_inv, Aut.Aut_inv_def, Iso.symm_hom]

/-- Restrict a comparison to the chosen section `(s,1)`. -/
def restrictComparison {D D' : ResidualData S C G}
    (α : D.presentationFunctor ⟶ D'.presentationFunctor) : D.E ⟶ D'.E where
  app s := α.app (s, ⟨1⟩)
  naturality {s t} u := by
    have h := α.naturality (Residual.pairArr u (1 : G) 1)
    rw [presentation_map_section, presentation_map_section] at h
    exact h

@[simp] theorem restrictComparison_comparison {D D' : ResidualData S C G}
    (β : D.E ⟶ D'.E) : restrictComparison (comparison β) = β := by
  ext s
  simp [restrictComparison, comparison_app]

@[simp] theorem comparison_restrictComparison {D D' : ResidualData S C G}
    (α : D.presentationFunctor ⟶ D'.presentationFunctor) :
    comparison (restrictComparison α) = α := by
  ext X
  rcases X with ⟨s, ⟨a⟩⟩
  have h := α.naturality (Residual.pairArr (𝟙 s) (1 : G) a)
  have h' : (D.σ s a).hom ≫ α.app (s, ⟨a⟩) =
      α.app (s, ⟨1⟩) ≫ (D'.σ s a).hom := by
    rw [presentation_map_vertical, presentation_map_vertical] at h
    exact h
  simpa [comparison_app, restrictComparison, Category.assoc] using
    (congrArg (fun k => (D.σ s a).inv ≫ k) h').symm

/-- The bijection in `prop:comparisons`. -/
def comparisonEquiv (D D' : ResidualData S C G) :
    (D.presentationFunctor ⟶ D'.presentationFunctor) ≃ (D.E ⟶ D'.E) where
  toFun := restrictComparison
  invFun := comparison
  left_inv := comparison_restrictComparison
  right_inv := restrictComparison_comparison

def comparisonIso {D D' : ResidualData S C G} (β : D.E ≅ D'.E) :
    D.presentationFunctor ≅ D'.presentationFunctor :=
  D.presentationIso.symm ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.Prod.fst S (Pair G)) β ≪≫ D'.presentationIso

def restrictComparisonIso {D D' : ResidualData S C G}
    (α : D.presentationFunctor ≅ D'.presentationFunctor) : D.E ≅ D'.E :=
  NatIso.ofComponents (fun s => α.app (s, ⟨1⟩)) (fun u => (restrictComparison α.hom).naturality u)

/-- A comparison is invertible exactly when its section restriction is invertible. -/
theorem isIso_comparison_iff {D D' : ResidualData S C G} (β : D.E ⟶ D'.E) :
    IsIso (comparison β) ↔ IsIso β := by
  constructor
  · intro h
    letI := h
    have h' : IsIso (restrictComparison (comparison β)) := by
      let e := restrictComparisonIso (asIso (comparison β))
      change IsIso e.hom
      infer_instance
    simpa using h'
  · intro h
    letI := h
    change IsIso (comparisonIso (asIso β)).hom
    infer_instance

/-- Invariance is exactly independence of the presentation coordinate. -/
theorem invariant_iff_constant {D D' : ResidualData S C G}
    (α : D.presentationFunctor ⟶ D'.presentationFunctor) :
    IsInvariantNatTrans (productData S G) D.presentationFunctor_isInvariant
      D'.presentationFunctor_isInvariant α ↔
        ∀ (s : S) (a : G), α.app (s, ⟨a⟩) = α.app (s, ⟨1⟩) := by
  constructor
  · intro h s a
    have ha := h a (s, ⟨1⟩)
    dsimp only [productData_act] at ha
    rw [one_mul] at ha
    exact ha.trans (self_casts _ _ _)
  · intro h r X
    simpa [productData_act] using
      (h X.1 (X.2.pt * r)).trans (h X.1 X.2.pt).symm

/-- The invariant part of the comparison bijection is precisely the intertwiner condition. -/
theorem comparison_invariant_iff {D D' : ResidualData S C G} (β : D.E ⟶ D'.E) :
    IsInvariantNatTrans (productData S G) D.presentationFunctor_isInvariant
      D'.presentationFunctor_isInvariant (comparison β) ↔
      ∀ (s : S) (r : G), (D.σ s r).hom ≫ β.app s = β.app s ≫ (D'.σ s r).hom := by
  rw [invariant_iff_constant]
  constructor
  · intro h s r
    have hr : (D.σ s r).inv ≫ β.app s ≫ (D'.σ s r).hom = β.app s := by
      simpa using h s r
    simpa [Category.assoc] using
      (congrArg (fun k => (D.σ s r).hom ≫ k) hr).symm
  · intro h s r
    simp only [comparison_app, map_one]
    simpa [Category.assoc] using
      (congrArg (fun k => (D.σ s r).inv ≫ k) (h s r)).symm

/-- Trivial residual data attached to a prescribed base functor. -/
def trivial (L : S ⥤ C) : ResidualData S C G where
  E := L
  σ _ := 1
  natural u _ := by simp

@[simp] theorem trivial_presentationFunctor (L : S ⥤ C) :
    (trivial (G := G) L).presentationFunctor = CategoryTheory.Prod.fst S (Pair G) ⋙ L := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun X Y f => ?_)
  change (1 : CategoryTheory.Aut (L.obj X.1)).hom ≫ L.map f.1 =
    𝟙 _ ≫ L.map f.1 ≫ 𝟙 _
  simp

/-- Unrestricted calibration to a fixed target requires the base data to be isomorphic. -/
theorem prescribed_iso_iff (D : ResidualData S C G) (L : S ⥤ C) :
    Nonempty (D.presentationFunctor ≅ CategoryTheory.Prod.fst S (Pair G) ⋙ L) ↔
      Nonempty (D.E ≅ L) := by
  rw [← trivial_presentationFunctor (G := G) L]
  exact ⟨fun ⟨α⟩ => ⟨restrictComparisonIso α⟩,
    fun ⟨β⟩ => ⟨comparisonIso β⟩⟩

/-- Invariant calibration to a prescribed target requires both base agreement and trivial
residual action. The target is represented by `trivial L`, whose functor is `p ⋙ L`. -/
theorem prescribed_invariant_iso_iff (D : ResidualData S C G) (L : S ⥤ C) :
    (∃ α : D.presentationFunctor ≅ (trivial (G := G) L).presentationFunctor,
      IsInvariantNatTrans (productData S G) D.presentationFunctor_isInvariant
        (trivial L).presentationFunctor_isInvariant α.hom) ↔
      Nonempty (D.E ≅ L) ∧ ∀ s, D.σ s = 1 := by
  constructor
  · rintro ⟨α, hα⟩
    let β := restrictComparisonIso α
    refine ⟨⟨β⟩, fun s => ?_⟩
    have hcomp : comparison β.hom = α.hom := comparison_restrictComparison α.hom
    have hint := (comparison_invariant_iff β.hom).mp (hcomp.symm ▸ hα)
    exact (Calibration.action_trivial_iff_of_intertwining (D.σ s) 1 (β.app s)
      (hint s)).mpr rfl
  · rintro ⟨⟨β⟩, hσ⟩
    refine ⟨comparisonIso β, ?_⟩
    apply (comparison_invariant_iff (D := D) (D' := trivial L) β.hom).mpr
    intro s r
    rw [hσ s]
    change 𝟙 _ ≫ β.hom.app s = β.hom.app s ≫ 𝟙 _
    simp

end ResidualData
