import ObserverEquivariance.Examples.RecordsCalibration
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Measurement calculations for the record model (`sec:records`, `sec:lean-modules`)

Information access, naturality under restriction, the sign-orbit target,
linear coinvariants, reference calibration, and fixed trajectories.
-/

open CategoryTheory

namespace RecordsRecovery

noncomputable section

/-- A procedure with no presentation-coordinate argument. Naturality is a separate condition. -/
abbrev Procedure (τ : ℝ) := ∀ I : RecDom, recordSpace τ I → recordSpace τ I

def IsEven {τ : ℝ} (K : Procedure τ) : Prop := ∀ I y, K I (-y) = K I y

def RespectsRestrictions {τ : ℝ} (K : Procedure τ) : Prop :=
  ∀ {I J : RecDom} (u : I ⟶ J) (y : recordSpace τ I),
    K J (recRestrict τ (RecDom.subset_of_hom u) y) =
      recRestrict τ (RecDom.subset_of_hom u) (K I y)

theorem identity_not_even (τ : ℝ) : ¬ IsEven (τ := τ) (fun _ y => y) := by
  intro h
  have he := h RecDom.full (recordOne τ RecDom.full)
  have he' := congrArg (fun y : recordSpace τ RecDom.full => y.val ⟨0, Finset.mem_univ _⟩) he
  norm_num [recordOne] at he'

def maxMagnitude (τ : ℝ) (I : RecDom) (y : recordSpace τ I) : ℝ :=
  I.dom.sup' I.nonempty (fun j => if h : j ∈ I.dom then |y.val ⟨j, h⟩| else 0)

def maxProcedure (τ : ℝ) : Procedure τ := fun I y => maxMagnitude τ I y • recordOne τ I

theorem maxProcedure_even (τ : ℝ) : IsEven (maxProcedure τ) := by
  intro I y
  unfold maxProcedure
  congr 1
  apply Finset.sup'_congr I.nonempty rfl
  intro j hj
  simp [hj]

/-- The even procedure `max |y_j| · 1` does not commute with restriction. -/
theorem maxProcedure_not_natural (τ : ℝ) (hτ : τ ≠ 0) :
    ¬ RespectsRestrictions (maxProcedure τ) := by
  intro h
  let y := recIdxRecord τ hτ RecDom.full
  let u := RecDom.fromFull (RecDom.single 0)
  have hfull : maxMagnitude τ RecDom.full y = 2 := by
    have hfin : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    norm_num [maxMagnitude, y, recIdxRecord, RecDom.full, hfin,
      Finset.sup'_insert, Finset.sup'_singleton]
  have hzero : maxMagnitude τ (RecDom.single 0)
      (recRestrict τ (RecDom.subset_of_hom u) y) = 0 := by
    simp [maxMagnitude, RecDom.single, y, recIdxRecord, recRestrict]
    change ((0 : ℕ) : ℝ) = 0
    exact Nat.cast_zero
  have he := h u y
  have he' := congrArg
    (fun z : recordSpace τ (RecDom.single 0) => z.val ⟨0, by simp [RecDom.single]⟩) he
  change maxMagnitude τ (RecDom.single 0) (recRestrict τ (RecDom.subset_of_hom u) y) * 1 =
    maxMagnitude τ RecDom.full y * 1 at he'
  rw [hzero, hfull] at he'
  norm_num at he'

/-- The equivalence relation identifying a vector with its negative. -/
def signSetoid (V : Type*) [AddCommGroup V] : Setoid V where
  r x y := x = y ∨ x = -y
  iseqv := ⟨fun _ => Or.inl rfl, by
    intro x y h
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (by rw [h, neg_neg]), by
    intro x y z hxy hyz
    rcases hxy with rfl | hxy
    · exact hyz
    · rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inl (by rw [hxy, hyz, neg_neg])⟩

abbrev SignOrbit (V : Type*) [AddCommGroup V] := Quotient (signSetoid V)

def orbitClass {V : Type*} [AddCommGroup V] (v : V) : SignOrbit V := Quotient.mk _ v

theorem orbitClass_eq_iff {V : Type*} [AddCommGroup V] (x y : V) :
    orbitClass x = orbitClass y ↔ x = y ∨ x = -y := Quotient.eq

def orbitMap {V W : Type*} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) :
    SignOrbit V → SignOrbit W := Quotient.map f (by
      intro x y h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (by rw [h, map_neg]))

/-- Sign orbits inherit natural restriction maps. -/
def orbitFunctor (τ : ℝ) : RecDom ⥤ Type where
  obj I := SignOrbit (recordSpace τ I)
  map u := TypeCat.ofHom (orbitMap (recRestrict τ (RecDom.subset_of_hom u)).toAddMonoidHom)
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun y => ?_)
    rfl
  map_comp u v := by
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun y => ?_)
    rfl

theorem orbitClass_sign (τ : ℝ) (I : RecDom) (ε : ℤˣ) (y : recordSpace τ I) :
    orbitClass (((ε : ℤ) : ℝ) • y) = orbitClass y := by
  apply Quotient.sound
  rcases Int.units_eq_one_or ε with rfl | rfl
  · left
    rw [recSign_one, one_smul]
  · right
    rw [recSign_neg_one]
    exact neg_one_smul ℝ y

/-- The orbit target permits exact recovery of the orbit from raw records, naturally. -/
def orbitRecovery (τ : ℝ) :
    recD τ ⋙ forget (ModuleCat.{0} ℝ) ⟶ recP ⋙ orbitFunctor τ where
  app X := TypeCat.ofHom (fun y : recordSpace τ X.1 => orbitClass y)
  naturality {X Y} f := by
    apply ConcreteCategory.hom_ext
    intro y
    change orbitClass (((recD τ).map f).hom y) =
      orbitClass (recRestrict τ (RecDom.subset_of_hom f.1) y)
    have he : ((recD τ).map f).hom y =
        (((Y.2.pt * X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ) •
          recRestrict τ (RecDom.subset_of_hom f.1) y := by
      apply Subtype.ext
      funext j
      rfl
    rw [he]
    exact orbitClass_sign τ Y.1 _ _

theorem orbitRecovery_invariant (τ : ℝ) :
    IsInvariantNatTrans recData (recD_forget_isInvariant τ)
      (isInvariant_comp_p recData (orbitFunctor τ)) (orbitRecovery τ) := by
  intro h X
  exact (RecordsCalibration.eqToHom_comp_comp_eqToHom_self
    _ ((orbitRecovery τ).app X) _).symm

/-- The relations defining linear coinvariants of the sign action. -/
def signRelations (V : Type*) [AddCommGroup V] [Module ℝ V] : Submodule ℝ V :=
  Submodule.span ℝ (Set.range (fun y : V => -y - y))

theorem signRelations_eq_top (V : Type*) [AddCommGroup V] [Module ℝ V] :
    signRelations V = ⊤ := by
  apply top_unique
  intro x _
  have hx : -((- (1 / 2 : ℝ)) • x) - ((- (1 / 2 : ℝ)) • x) ∈ signRelations V :=
    Submodule.subset_span ⟨(- (1 / 2 : ℝ)) • x, rfl⟩
  have he : -((- (1 / 2 : ℝ)) • x) - ((- (1 / 2 : ℝ)) • x) = x := by
    simp only [sub_eq_add_neg, ← neg_smul, ← add_smul]
    norm_num
  rwa [he] at hx

theorem linear_coinvariants_zero (V : Type*) [AddCommGroup V] [Module ℝ V] (x : V) :
    (Submodule.Quotient.mk x : V ⧸ signRelations V) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (signRelations V)).mpr
  rw [signRelations_eq_top]
  trivial

theorem linear_coinvariants_subsingleton (V : Type*) [AddCommGroup V] [Module ℝ V] :
    Subsingleton (V ⧸ signRelations V) := by
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂ a b (fun x y => ?_)
  exact (linear_coinvariants_zero V x).trans (linear_coinvariants_zero V y).symm

/-- A nonzero reference observation determines the sign. -/
theorem reference_determines_sign (ε : ℤˣ) (qref : ℝ) (hq : qref ≠ 0) :
    ((((ε : ℤ) : ℝ) * qref) / qref) = ((ε : ℤ) : ℝ) :=
  mul_div_cancel_right₀ _ hq

theorem reference_recovers_value (ε : ℤˣ) (qref : ℝ) (hq : qref ≠ 0) (q : ℝ) :
    ((((ε : ℤ) : ℝ) * qref) / qref) * (((ε : ℤ) : ℝ) * q) = q := by
  rw [reference_determines_sign ε qref hq, ← mul_assoc, recSign_mul_self, one_mul]

def reflectTrajectory (τ : ℝ) (qv : ℝ × ℝ) : ℝ × ℝ :=
  (qv.1 + 2 * τ * qv.2, -qv.2)

theorem reflectTrajectory_involution (τ : ℝ) (qv : ℝ × ℝ) :
    reflectTrajectory τ (reflectTrajectory τ qv) = qv := by
  apply Prod.ext <;> dsimp [reflectTrajectory] <;> ring

theorem reflectTrajectory_fixed_iff (τ : ℝ) (qv : ℝ × ℝ) :
    reflectTrajectory τ qv = qv ↔ qv.2 = 0 := by
  constructor
  · intro h
    have h' := congrArg Prod.snd h
    change -qv.2 = qv.2 at h'
    linarith
  · intro h
    apply Prod.ext <;> simp [reflectTrajectory, h]

def trajectoryRecord (τ : ℝ) (I : RecDom) (q v : ℝ) : recordSpace τ I :=
  ⟨fun j => q + v * (((j : Fin 3) : ℕ) : ℝ) * τ, q, v, fun _ => rfl⟩

/-- The parameter calculation agrees with the natural time-reflection map `recα`. -/
theorem recα_trajectory (τ : ℝ) (I : RecDom) (q v : ℝ) :
    ((recα τ).hom.app I).hom (trajectoryRecord τ I.rev q v) =
      trajectoryRecord τ I (q + 2 * τ * v) (-v) := by
  apply Subtype.ext
  funext j
  rw [recα_hom_app_apply]
  change q + v * (((recρ j : Fin 3) : ℕ) : ℝ) * τ =
    q + 2 * τ * v + -v * (((j : Fin 3) : ℕ) : ℝ) * τ
  rw [recρ_cast]
  ring

end

end RecordsRecovery
