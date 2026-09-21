import ObserverEquivariance.Implementations
import ObserverEquivariance.Examples.Twist
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# A twisted lift without an invariant complex-linear implementation

Revision r4, `ex:complex-obstruction`. This uses the existing `C₃`, base
interchange, and inversion twist from `Examples.Twist`.
-/

open CategoryTheory

namespace ComplexObstruction

noncomputable section

local instance : Category.{0} (Pair (Fin 2)) := inferInstance

private theorem cast_self {X Y : ModuleCat.{0} ℂ} (h : X = X) (f : X ⟶ Y)
    (h' : Y = Y) : eqToHom h ≫ f ≫ eqToHom h' = f := by simp

def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem omega_primitive : IsPrimitiveRoot omega 3 :=
  Complex.isPrimitiveRoot_exp 3 (by decide)

theorem omega_pow_three : omega ^ 3 = 1 := omega_primitive.pow_eq_one

theorem omega_ne_zero : omega ≠ 0 := Complex.exp_ne_zero _

theorem omega_inv_ne : omega⁻¹ ≠ omega := by
  intro h
  have h2 : omega ^ 2 = 1 := by
    calc
      omega ^ 2 = omega⁻¹ * omega := by rw [pow_two, h]
      _ = 1 := inv_mul_cancel₀ omega_ne_zero
  exact (omega_primitive.pow_ne_one_of_pos_of_lt (l := 2) (by decide) (by decide)) h2

def omegaUnit : ℂˣ where
  val := omega
  inv := omega ^ 2
  val_inv := by simpa [pow_succ, mul_comm] using omega_pow_three
  inv_val := by simpa [pow_succ] using omega_pow_three

theorem omegaUnit_pow_three : omegaUnit ^ 3 = 1 := by
  apply Units.ext
  exact omega_pow_three

def intCharacter : ℤ →+ Additive ℂˣ where
  toFun n := Additive.ofMul (omegaUnit ^ n)
  map_zero' := by change omegaUnit ^ (0 : ℤ) = 1; simp
  map_add' m n := by change omegaUnit ^ (m + n) = omegaUnit ^ m * omegaUnit ^ n; rw [zpow_add]

theorem intCharacter_three : intCharacter 3 = 0 := by
  change omegaUnit ^ (3 : ℤ) = 1
  exact (zpow_natCast omegaUnit 3).trans omegaUnit_pow_three

def character : G3 →* ℂˣ :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift 3 ⟨intCharacter, intCharacter_three⟩)

@[simp] theorem character_generator : character twistR = omegaUnit := by
  change (ZMod.lift 3 ⟨intCharacter, intCharacter_three⟩ (1 : ZMod 3)).toMul = omegaUnit
  have h := ZMod.lift_coe 3 ⟨intCharacter, intCharacter_three⟩ (1 : ℤ)
  simpa [intCharacter] using congrArg Additive.toMul h

def scalarIso (u : ℂˣ) : CategoryTheory.Aut (ModuleCat.of ℂ ℂ) where
  hom := ModuleCat.ofHom ((u : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
  inv := ModuleCat.ofHom (((u⁻¹ : ℂˣ) : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((u⁻¹ : ℂˣ) : ℂ) * ((u : ℂ) * z) = z
    simp
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (u : ℂ) * (((u⁻¹ : ℂˣ) : ℂ) * z) = z
    simp

def scalarRepresentation : ℂˣ →* CategoryTheory.Aut (ModuleCat.of ℂ ℂ) where
  toFun := scalarIso
  map_one' := by
    apply Iso.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (1 : ℂ) * z = z
    exact one_mul z
  map_mul' u v := by
    apply Iso.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((u * v : ℂˣ) : ℂ) * z = (u : ℂ) * ((v : ℂ) * z)
    simp [mul_assoc]

def representation : G3 →* CategoryTheory.Aut (ModuleCat.of ℂ ℂ) :=
  scalarRepresentation.comp character

@[simp] theorem representation_apply (g : G3) (z : ℂ) :
    (representation g).hom.hom z = (character g : ℂ) * z := rfl

def complexData : ResidualData (Pair (Fin 2)) (ModuleCat.{0} ℂ) G3 where
  E := (Functor.const (Pair (Fin 2))).obj (ModuleCat.of ℂ ℂ)
  σ _ := representation
  natural _ _ := (Category.comp_id _).trans (Category.id_comp _).symm

abbrev F := complexData.presentationFunctor

theorem F_isInvariant : OEData.IsInvariant twistData F :=
  complexData.presentationFunctor_isInvariant

/-- The underlying base data are unchanged by the interchange. -/
def baseIso : swapFunctor ⋙ complexData.E ≅ complexData.E :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change 𝟙 (ModuleCat.of ℂ ℂ) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rfl)

/-- Any complex-linear intertwiner between the inverse character and the original
character vanishes. No assumption of invertibility is needed. -/
theorem intertwiner_eq_zero (f : ℂ →ₗ[ℂ] ℂ)
    (h : ∀ z : ℂ, f (omega⁻¹ * z) = omega * f z) : f = 0 := by
  apply LinearMap.ext
  intro z
  have hf : omega⁻¹ * f z = omega * f z := by
    simpa only [← smul_eq_mul, map_smul] using h z
  have hz : (omega⁻¹ - omega) * f z = 0 := by rw [sub_mul, hf, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr omega_inv_ne)

/-- The canonical inversion-twisted lift has no invariant complex-linear implementation. -/
theorem no_invariant_complex_implementation :
    ¬ Nonempty (complexData.InvariantImplementation swapFunctor (twistθ twistHSwap)) := by
  intro h
  obtain ⟨β, hβ⟩ :=
    (complexData.invariant_implementation_iff swapFunctor (twistθ twistHSwap)).mp h
  let s : Pair (Fin 2) := ⟨0⟩
  let b : ℂ ≃ₗ[ℂ] ℂ := (β.app s).toLinearEquiv
  have hz : b.toLinearMap = 0 := by
    apply intertwiner_eq_zero
    intro z
    have he := congrArg
      (fun f : ModuleCat.of ℂ ℂ ⟶ ModuleCat.of ℂ ℂ => (f.hom z : ℂ)) (hβ s twistR)
    change b ((character (twistθ twistHSwap twistR) : ℂ) * z) =
      (character twistR : ℂ) * b z at he
    rw [twistθ_swap_apply, map_inv, character_generator, Units.val_inv_eq_inv_val] at he
    exact he
  have h1 : b (1 : ℂ) = 0 := congrArg (fun f : ℂ →ₗ[ℂ] ℂ => f (1 : ℂ)) hz
  exact one_ne_zero (b.injective (h1.trans (map_zero b).symm))

/-- The same obstruction holds for every transport-preserving inversion-twisted
lift over the interchange, using the existing classification of all such lifts. -/
theorem no_invariant_complex_implementation_any_lift
    (T : Pair (Fin 2) × Pair G3 ⥤ Pair (Fin 2) × Pair G3)
    (hT : IsTwistedEquivariant twistData (twistθ twistHSwap) T)
    (hpc : PreservesCleavage twistData T swapFunctor) :
    ¬ ∃ (hTF : OEData.IsInvariant twistData (T ⋙ F)) (α : T ⋙ F ≅ F),
      IsInvariantNatTrans twistData hTF F_isInvariant α.hom := by
  obtain ⟨a, ha, _⟩ := exists_unique_eq_liftFunctorθ_comp_Λ twistData hT hpc
  have hf : T ⋙ F = (complexData.twisted swapFunctor (twistθ twistHSwap)).presentationFunctor := by
    rw [ha]
    exact complexData.translated_lift_comp_presentationFunctor swapFunctor (twistθ twistHSwap) a
  rintro ⟨hTF, α, hα⟩
  let α' := (eqToIso hf).symm ≪≫ α
  apply no_invariant_complex_implementation
  refine ⟨⟨α', (ResidualData.invariant_iff_constant α'.hom).mpr ?_⟩⟩
  intro s a
  have hc (x : Pair (Fin 2) × Pair G3) : α'.hom.app x = α.hom.app x := by
    change (eqToHom hf.symm).app x ≫ α.hom.app x = α.hom.app x
    rw [eqToHom_app]
    exact Category.id_comp _
  rw [hc, hc]
  have h := hα a (s, ⟨1⟩)
  dsimp only [productData_act] at h
  rw [one_mul] at h
  exact h.trans (cast_self _ _ _)

/-- An unrestricted complex-linear implementation exists. -/
def unrestrictedImplementation :
    (complexData.twisted swapFunctor (twistθ twistHSwap)).presentationFunctor ≅ F :=
  ResidualData.comparisonIso baseIso

theorem unrestrictedImplementation_app (s : Pair (Fin 2)) (g : G3) (z : ℂ) :
    (unrestrictedImplementation.hom.app (s, ⟨g⟩)).hom z = (character g : ℂ) ^ 2 * z := by
  change (character g : ℂ) *
    ((((character (twistθ twistHSwap g))⁻¹ : ℂˣ) : ℂ) * z) = _
  simp [twistθ_swap_apply, map_inv, pow_two, mul_assoc]

theorem unrestrictedImplementation_not_invariant :
    ¬ IsInvariantNatTrans twistData
      (complexData.twisted swapFunctor (twistθ twistHSwap)).presentationFunctor_isInvariant
      complexData.presentationFunctor_isInvariant unrestrictedImplementation.hom := by
  intro h
  exact no_invariant_complex_implementation ⟨⟨unrestrictedImplementation, h⟩⟩

theorem omega_conj : starRingEnd ℂ omega = omega⁻¹ := by
  rw [omega, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem character_conj (g : G3) :
    starRingEnd ℂ (character g : ℂ) = (character g : ℂ)⁻¹ := by
  have cases3 : ∀ g : G3, g = 1 ∨ g = twistR ∨ g = twistR ^ 2 := by decide
  rcases cases3 g with rfl | rfl | rfl
  · simp
  · rw [character_generator]
    exact omega_conj
  · simp [map_pow, character_generator, omegaUnit, omega_conj, inv_pow]

def realification : ModuleCat.{0} ℂ ⥤ ModuleCat.{0} ℝ :=
  ModuleCat.restrictScalars (algebraMap ℝ ℂ)

def realData : ResidualData (Pair (Fin 2)) (ModuleCat.{0} ℝ) G3 where
  E := complexData.E ⋙ realification
  σ s := (Functor.mapAut (complexData.E.obj s) realification).comp (complexData.σ s)
  natural u g := by
    change realification.map (complexData.σ _ g).hom ≫ realification.map (complexData.E.map u) =
      realification.map (complexData.E.map u) ≫ realification.map (complexData.σ _ g).hom
    rw [← realification.map_comp, ← realification.map_comp, complexData.natural]

theorem realData_presentationFunctor : realData.presentationFunctor = F ⋙ realification := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun X Y f => ?_)
  change realification.map (complexData.σ X.1 (Y.2.pt * X.2.pt⁻¹)).hom ≫
    realification.map (complexData.E.map f.1) =
      𝟙 _ ≫ realification.map
        ((complexData.σ X.1 (Y.2.pt * X.2.pt⁻¹)).hom ≫ complexData.E.map f.1) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact (realification.map_comp _ _).symm

/-- Conjugation becomes an allowed isomorphism after restriction of scalars to `ℝ`. -/
def conjugationIso : ModuleCat.of ℝ ℂ ≅ ModuleCat.of ℝ ℂ :=
  Complex.conjAe.toLinearEquiv.toModuleIso

def realBaseIso : swapFunctor ⋙ realData.E ≅ realData.E :=
  NatIso.ofComponents (fun _ => conjugationIso) (by
    intro X Y f
    change realification.map (𝟙 (ModuleCat.of ℂ ℂ)) ≫ conjugationIso.hom =
      conjugationIso.hom ≫ realification.map (𝟙 (ModuleCat.of ℂ ℂ))
    rw [realification.map_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

theorem real_intertwines (s : Pair (Fin 2)) (g : G3) :
    (realData.σ (swapFunctor.obj s) (twistθ twistHSwap g)).hom ≫ realBaseIso.hom.app s =
      realBaseIso.hom.app s ≫ (realData.σ s g).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change ℂ at z
  change starRingEnd ℂ ((character (twistθ twistHSwap g) : ℂ) * z) =
    (character g : ℂ) * starRingEnd ℂ z
  rw [twistθ_swap_apply, map_inv, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
    character_conj, inv_inv]

def realImplementation : realData.InvariantImplementation swapFunctor (twistθ twistHSwap) :=
  (realData.implementationEquiv swapFunctor (twistθ twistHSwap)).symm
    ⟨realBaseIso, real_intertwines⟩

theorem realImplementation_app (s : Pair (Fin 2)) (a : G3) (z : ℂ) :
    (realImplementation.val.hom.app (s, ⟨a⟩)).hom z = starRingEnd ℂ z := by
  have h := realData.implementation_app swapFunctor (twistθ twistHSwap) realImplementation s a
  have hc : realImplementation.val.hom.app (s, ⟨a⟩) = realBaseIso.hom.app s := by
    simpa only [realImplementation, Equiv.apply_symm_apply] using h
  rw [hc]
  rfl

theorem conjugation_involution (z : ℂ) :
    conjugationIso.hom.hom (conjugationIso.hom.hom z) = z := by
  change starRingEnd ℂ (starRingEnd ℂ z) = z
  simp

theorem realImplementation_involution (s : Pair (Fin 2)) (a : G3) (z : ℂ) :
    (realImplementation.val.hom.app (s, ⟨a⟩)).hom
      ((realImplementation.val.hom.app (swapFunctor.obj s, ⟨twistθ twistHSwap a⟩)).hom z) = z := by
  rw [realImplementation_app, realImplementation_app]
  simp

end

end ComplexObstruction
