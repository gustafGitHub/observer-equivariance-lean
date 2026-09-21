import ObserverEquivariance.Examples.Records
import ObserverEquivariance.Calibration

/-!
# Free-particle records and sensor polarity, second half (paper `sec:records`)

Paper labels covered (all in `sec:records`, using `prop:residual` and
`cor:invariant-calibration`):
* paragraph "Raw records and calibrated records": the raw-record functor
  `𝒟 : O ⥤ Vect_ℝ`, `𝒟(I, ε) = L(I)`, `𝒟((I,ε) → (J,δ)) = δ ε⁻¹ r_{IJ}` (`recD`,
  `recD_map_apply`, `recD_map_vert`),
  its functoriality, its strict invariance `𝒟 R_h = 𝒟` (`recD_isInvariant`), its residual factor
  `E = L` with the sign action (`recEcal`, `residualQ_comp_recEcal`; read through
  `functorProdBGEquivResidualData` of `prop:residual`, its base functor is `L`,
  `recEcal_residualData_E`, and its action is `σ_I(h) = h · id`, `recEcal_residualData_σ_hom`),
  the residual action as the
  sign representation `σ_I(h) = h · id` (`recD_residualAction_hom`), the vertical polarity change
  acting as `-id` (`recD_map_vertical_neg`), and the failure of strict factorization through `p`
  (`recD_not_factors`); the calibration `C : 𝒟 ≅ L p`, `C_{(I,ε)} = ε⁻¹ · id` (`recC`), its
  naturality, its convention dependence `(C R_h)_{(I,ε)} = h⁻¹ C_{(I,ε)}` and `C R_{-1} = -C`
  (`recC_hom_app_act`, `recC_hom_app_act_neg_one`, and with additive negation
  `recC_hom_app_act_eq_neg`), non-invariance (`recC_not_invariant`),
  vanishing of
  every invariant natural transformation `𝒟 ⟶ L p` (`recD_invariantNatTrans_eq_zero`), and
  non-existence of an invariant natural isomorphism (`recD_no_invariant_iso`,
  `recD_no_invariant_calibration`, the latter via `cor:invariant-calibration`);
* paragraph "Two information conditions for calibration": for the underlying set-valued functors
  (composition with `forget (ModuleCat ℝ)`), an invariant natural transformation `K` has even
  components `K_I(-y) = K_I(y)` without any linearity (`recInfo_even`), in fact naturality along
  the vertical arrow is precisely evenness (`recInfo_vertical_naturality_iff_even`), such a
  component is never the identity (`recInfo_invariant_ne_id`), and exact recovery
  `K_I(ε q) = q` for all `q` and both signs is impossible for arbitrary maps (`recInfo_no_recovery`).

## Conventions
* Signs are `ε : ℤˣ` acting by the real scalar `((ε : ℤ) : ℝ)` (as in `Records`).
* An arrow `(I, ε) ⟶ (J, δ)` of `O = RecDom × Pair ℤˣ` is a pair `(u, ⟨⟩)`; its polarity factor
  `δ ε⁻¹` is read off the endpoints.
* Morphisms of `ModuleCat ℝ` form real vector spaces (`Linear ℝ`), so `c • f` is scalar
  multiplication of linear maps.
-/

open CategoryTheory

/-! ## Helpers -/

namespace RecordsCalibration

/-- Composition in `Vect_ℝ` evaluated on an element (helper for paper `sec:records`). -/
theorem modComp_apply {A B Z : ModuleCat.{0} ℝ} (f : A ⟶ B) (g : B ⟶ Z) (x : A) :
    (f ≫ g).hom x = g.hom (f.hom x) := rfl

/-- Self-casts on both sides of a morphism collapse (helper for paper `sec:records`, used for
    the invariance casts of `prop:residual` whose endpoints agree definitionally). -/
theorem eqToHom_comp_comp_eqToHom_self {𝒞 : Type*} [Category 𝒞] {A B : 𝒞} (e₁ : A = A)
    (f : A ⟶ B) (e₂ : B = B) : eqToHom e₁ ≫ f ≫ eqToHom e₂ = f := by
  simp

end RecordsCalibration

open RecordsCalibration

/-! ## The projection and scalar endomorphisms -/

/-- The projection `p : O = S × Pair(G) ⥤ S`, `p(I, ε) = I`, of the presentation `recData`
    (paper `sec:records`, "Presentations and their comparisons"), with hom universes pinned. -/
abbrev recP : CategoryTheory.Functor.{0, 0} (RecDom × Pair ℤˣ) RecDom :=
  CategoryTheory.Prod.fst RecDom (Pair ℤˣ)

/-- Scalar multiplication `c · id_{L(I)}` as an endomorphism of `L(I)` in `Vect_ℝ` (paper
    `sec:records`: the sign action `σ_I(h) = h id_{L(I)}` and the calibration components
    `ε⁻¹ id_{L(I)}`). -/
noncomputable def recScalar (τ : ℝ) (I : RecDom) (c : ℝ) : (L₀ τ).obj I ⟶ (L₀ τ).obj I :=
  ModuleCat.ofHom (c • (LinearMap.id : recordSpace τ I →ₗ[ℝ] recordSpace τ I))

/-- Values of `c · id` (paper `sec:records`). -/
theorem recScalar_apply (τ : ℝ) (I : RecDom) (c : ℝ) (y : recordSpace τ I) (j : ↥I.dom) :
    Subtype.val ((recScalar τ I c).hom y) j = c * Subtype.val y j := rfl

/-- Scalar endomorphisms with different scalars differ, because `L(I)` is nonzero (paper
    `sec:records`: "each `L(I)` is nonzero"; used for `σ_I(-1) = -id ≠ id` and `C R_{-1} ≠ C`). -/
theorem recScalar_ne (τ : ℝ) (I : RecDom) {c c' : ℝ} (hc : c ≠ c') :
    recScalar τ I c ≠ recScalar τ I c' := by
  intro e
  obtain ⟨j, hj⟩ := I.nonempty
  have h := congrArg (fun k : (L₀ τ).obj I ⟶ (L₀ τ).obj I =>
    Subtype.val (k.hom (recordOne τ I)) ⟨j, hj⟩) e
  change c * 1 = c' * 1 at h
  rw [mul_one, mul_one] at h
  exact hc h

/-! ## The raw-record functor `𝒟` (paper `sec:records`, "Raw records and calibrated records") -/

/-- The raw-record functor `𝒟 : O ⥤ Vect_ℝ` (paper `sec:records`):
    `𝒟(I, ε) = L(I)` and `𝒟((I, ε) → (J, δ)) = δ ε⁻¹ r_{IJ}`, the signs acting by their real
    scalars.  Functoriality: along two comparisons the intermediate polarity factors cancel,
    `(ζ δ⁻¹)(δ ε⁻¹) = ζ ε⁻¹`, and restrictions compose. -/
noncomputable def recD (τ : ℝ) :
    CategoryTheory.Functor.{0, 0} (RecDom × Pair ℤˣ) (ModuleCat.{0} ℝ) where
  obj X := (L₀ τ).obj X.1
  map {X Y} f := ModuleCat.ofHom
    ((((Y.2.pt * X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ) • recRestrict τ (RecDom.subset_of_hom f.1))
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext j
    change (((X.2.pt * X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ) * Subtype.val y j = Subtype.val y j
    rw [mul_inv_cancel, recSign_one, one_mul]
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext j
    change (((Z.2.pt * X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ) * Subtype.val y ⟨j.1, _⟩
      = (((Z.2.pt * Y.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ)
        * ((((Y.2.pt * X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ) * Subtype.val y ⟨j.1, _⟩)
    rw [← mul_assoc, ← recSign_mul,
      show Z.2.pt * Y.2.pt⁻¹ * (Y.2.pt * X.2.pt⁻¹) = Z.2.pt * X.2.pt⁻¹ by group]

/-- Objects of `𝒟` (paper `sec:records`): `𝒟(I, ε) = L(I)`. -/
theorem recD_obj (τ : ℝ) (X : RecDom × Pair ℤˣ) : (recD τ).obj X = (L₀ τ).obj X.1 := rfl

/-- Values of `𝒟` on arrows (paper `sec:records`):
    `(𝒟((I,ε) → (J,δ)) y)_j = δ ε⁻¹ y_j`. -/
theorem recD_map_apply (τ : ℝ) {X Y : RecDom × Pair ℤˣ} (f : X ⟶ Y) (y : recordSpace τ X.1)
    (j : ↥Y.1.dom) :
    Subtype.val (((recD τ).map f).hom y) j
      = (((Y.2.pt * X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ) * Subtype.val y ⟨j.1, RecDom.subset_of_hom f.1 j.2⟩ :=
  rfl

/-- The composite of two scalar endomorphisms (paper `sec:records`):
    `(c' · id) ∘ (c · id) = (c' c) · id`. -/
theorem recScalar_comp (τ : ℝ) (I : RecDom) (c c' : ℝ) :
    recScalar τ I c ≫ recScalar τ I c' = recScalar τ I (c' * c) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  funext j
  change c' * (c * Subtype.val y j) = (c' * c) * Subtype.val y j
  rw [mul_assoc]

/-- `1 · id = id` (paper `sec:records`). -/
theorem recScalar_one (τ : ℝ) (I : RecDom) : recScalar τ I 1 = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  funext j
  change 1 * Subtype.val y j = Subtype.val y j
  rw [one_mul]

/-! ## Vertical arrows, strict invariance and the residual sign action -/

/-- The vertical comparison `(I, ε) ⟶ (I, ε h)` over `id_I`, i.e. the change of polarity
    convention at a fixed observation domain (paper `sec:records`, "a vertical change of
    polarity"). -/
def recVert (X : RecDom × Pair ℤˣ) (h : ℤˣ) : (X ⟶ recData.act X h : Type) := (𝟙 X.1, ⟨⟩)

/-- `𝒟` sends the vertical arrow `(I, ε) ⟶ (I, ε h)` to `h · id_{L(I)}` (paper `sec:records`:
    the polarity factor is `(ε h) ε⁻¹ = h`). -/
theorem recD_map_vert (τ : ℝ) (X : RecDom × Pair ℤˣ) (h : ℤˣ) :
    (recD τ).map (recVert X h) = recScalar τ X.1 (((h : ℤ) : ℝ)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  funext j
  change (((X.2.pt * h * X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ) * Subtype.val y j
    = ((h : ℤ) : ℝ) * Subtype.val y j
  rw [mul_comm X.2.pt h, mul_inv_cancel_right]

/-- A vertical change of polarity acts on raw records as `-id_{L(I)}`, not as the identity
    (paper `sec:records`, "Raw records and calibrated records"). -/
theorem recD_map_vertical_neg (τ : ℝ) (X : RecDom × Pair ℤˣ) :
    (recD τ).map (recVert X (-1)) = recScalar τ X.1 (-1) := by
  rw [recD_map_vert, recSign_neg_one]

/-- The residual factor `Ecal : S × BG ⥤ Vect_ℝ` of `𝒟` (paper `sec:records`, via
    `prop:residual`): `Ecal(I, *) = L(I)` and `Ecal(u_{IJ}, h) = h r_{IJ}`, i.e. `E = L` together
    with the sign action `σ_I(h) = h id_{L(I)}`, natural because scalar multiplication commutes
    with every restriction. -/
noncomputable def recEcal (τ : ℝ) :
    CategoryTheory.Functor.{0, 0} (RecDom × SingleObj ℤˣ) (ModuleCat.{0} ℝ) where
  obj X := (L₀ τ).obj X.1
  map {X Y} f := ModuleCat.ofHom
    ((((show ℤˣ from f.2) : ℤ) : ℝ) • recRestrict τ (RecDom.subset_of_hom f.1))
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext j
    change (((1 : ℤˣ) : ℤ) : ℝ) * Subtype.val y j = Subtype.val y j
    rw [recSign_one, one_mul]
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext j
    change (((((show ℤˣ from g.2) * (show ℤˣ from f.2)) : ℤˣ) : ℤ) : ℝ) * Subtype.val y ⟨j.1, _⟩
      = ((((show ℤˣ from g.2)) : ℤ) : ℝ)
        * (((((show ℤˣ from f.2)) : ℤ) : ℝ) * Subtype.val y ⟨j.1, _⟩)
    rw [recSign_mul, mul_assoc]

/-- `𝒟 = Ecal Q` (paper `sec:records`: "In Proposition `prop:residual`, it corresponds to
    `E = L` with the sign action"). -/
theorem residualQ_comp_recEcal (τ : ℝ) : residualQ RecDom ℤˣ ⋙ recEcal τ = recD τ := rfl

/-- The base functor of the residual data of `𝒟` is the law: `E = L` (paper `sec:records`:
    "it corresponds to `E = L` with the sign action", read through the equivalence
    `functorProdBGEquivResidualData` of `prop:residual`, `E(u) = Ecal(u, 1) = 1 · r_{IJ}`). -/
theorem recEcal_residualData_E (τ : ℝ) :
    (functorProdBGEquivResidualData (recEcal τ)).E = L₀ τ := by
  fapply CategoryTheory.Functor.ext
  · intro I; rfl
  · intro I J u
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; apply Subtype.ext; funext j
    simp only [functorProdBGEquivResidualData_E_map]
    change (((1 : ℤˣ) : ℤ) : ℝ) * _ = _
    rw [recSign_one, one_mul]
    rfl

/-- The residual action in the residual data of `𝒟` is the sign action `σ_I(h) = h id_{L(I)}`
    (paper `sec:records`, via `functorProdBGEquivResidualData` of `prop:residual`:
    `σ_I(h) = Ecal(𝟙_I, h)`). -/
theorem recEcal_residualData_σ_hom (τ : ℝ) (I : RecDom) (h : ℤˣ) :
    ((functorProdBGEquivResidualData (recEcal τ)).σ I h).hom = recScalar τ I ((h : ℤ) : ℝ) := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; apply Subtype.ext; funext j
  rfl

/-- The residual factor of `𝒟` is unique (paper `sec:records`, uniqueness in `prop:residual`). -/
theorem recEcal_unique (τ : ℝ) (E : CategoryTheory.Functor.{0, 0} (RecDom × SingleObj ℤˣ)
    (ModuleCat.{0} ℝ)) (hE : residualQ RecDom ℤˣ ⋙ E = recD τ) : E = recEcal τ :=
  residualQ_cancel (hE.trans (residualQ_comp_recEcal τ).symm)

/-- `𝒟` is strictly invariant under simultaneous right changes of convention, `𝒟 R_h = 𝒟`
    (paper `sec:records`), because it factors through the invariant functor `Q`. -/
theorem recD_isInvariant (τ : ℝ) : OEData.IsInvariant recData (recD τ) := by
  intro h
  rw [← residualQ_comp_recEcal τ, ← Functor.assoc]
  exact congrArg (· ⋙ recEcal τ) (residualQ_invariant h)

/-- A morphism followed by a self-cast (helper for paper `sec:records`). -/
theorem RecordsCalibration.comp_eqToHom_self {𝒞 : Type*} [Category 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (e : B = B) : f ≫ eqToHom e = f := by
  simp

/-- For the presentation `recData`, the vertical arrow `v_{I,r} : (I, 1) ⟶ (I, r)` of
    `cor:invariant-calibration` is the polarity change `recVert` (paper `sec:records`; both lie
    over `id_I` and `p` is faithful). -/
theorem recVertArr_eq (I : RecDom) (r : ℤˣ) :
    recData.vertArr I r = recVert (recData.base I) r :=
  ProductModel.productHom_ext (Subsingleton.elim _ _)

/-- The residual action of `𝒟` is the sign representation, `σ_I(r) = r · id_{L(I)}`
    (paper `sec:records`: "the sign action `σ_I(h) = h id_{L(I)}`", `prop:residual`). -/
theorem recD_residualAction_hom (τ : ℝ) (I : RecDom) (r : ℤˣ) :
    (residualAction recData (recD τ) (recD_isInvariant τ) I r).hom
      = recScalar τ I (((r : ℤ) : ℝ)) := by
  rw [residualAction_hom, recVertArr_eq, recD_map_vert]
  exact RecordsCalibration.comp_eqToHom_self _ _

/-- The residual action of `𝒟` is nontrivial at every observation domain: `σ_I(-1) = -id ≠ id`,
    because `L(I)` is nonzero (paper `sec:records`). -/
theorem recD_residualAction_ne_one (τ : ℝ) (I : RecDom) :
    residualAction recData (recD τ) (recD_isInvariant τ) I ≠ 1 := by
  intro h
  have h1 : (residualAction recData (recD τ) (recD_isInvariant τ) I (-1)).hom = 𝟙 _ := by
    rw [h]; rfl
  rw [recD_residualAction_hom, recSign_neg_one] at h1
  exact recScalar_ne τ I (by norm_num) (h1.trans (recScalar_one τ I).symm)

/-- `𝒟` does not factor strictly through `p` (paper `sec:records`), by the criterion
    `(ii) ↔ (iii)` of `cor:invariant-calibration` and the nontrivial residual action. -/
theorem recD_not_factors (τ : ℝ) :
    ¬ ∃ E : CategoryTheory.Functor.{0, 0} RecDom (ModuleCat.{0} ℝ), recP ⋙ E = recD τ :=
  fun hE => recD_residualAction_ne_one τ RecDom.full
    ((calibration_ii_iff_iii recData (recD τ) (recD_isInvariant τ)).mp hE RecDom.full)

/-- `𝒟` is not vertically trivial (paper `sec:records`: raw data "retain a nontrivial response
    to vertical comparisons"; via `thm:descent`). -/
theorem recD_not_verticallyTrivial (τ : ℝ) : ¬ VerticallyTrivial recP (recD τ) :=
  fun hv => recD_not_factors τ ((recData.descent (recD τ)).mp hv).exists

/-- The calibrated functor `L̂ = L p` is vertically trivial (paper `sec:records`). -/
theorem recLp_verticallyTrivial (τ : ℝ) : VerticallyTrivial recP (recP ⋙ L₀ τ) :=
  verticallyTrivial_comp recP (L₀ τ)

/-! ## The calibration `C : 𝒟 ≅ L p` -/

/-- The calibration component `C_{(I,ε)} = ε⁻¹ id_{L(I)}`, an isomorphism with inverse
    `ε id_{L(I)}` (paper `sec:records`: "Calibration sends a raw record `y` to `ε⁻¹ y`"). -/
noncomputable def recCIso (τ : ℝ) (I : RecDom) (ε : ℤˣ) : (L₀ τ).obj I ≅ (L₀ τ).obj I where
  hom := recScalar τ I (((ε⁻¹ : ℤˣ) : ℤ) : ℝ)
  inv := recScalar τ I (((ε : ℤˣ) : ℤ) : ℝ)
  hom_inv_id := by
    rw [recScalar_comp, ← recSign_mul, mul_inv_cancel, recSign_one, recScalar_one]
  inv_hom_id := by
    rw [recScalar_comp, ← recSign_mul, inv_mul_cancel, recSign_one, recScalar_one]

/-- The calibration natural isomorphism `C : 𝒟 ≅ L p`, `C_{(I,ε)} = ε⁻¹ id_{L(I)}` (paper
    `sec:records`).  Naturality is `C_{(J,δ)} 𝒟((I,ε) → (J,δ)) = r_{IJ} C_{(I,ε)}`, i.e.
    `δ⁻¹ (δ ε⁻¹) = ε⁻¹`. -/
noncomputable def recC (τ : ℝ) : recD τ ≅ recP ⋙ L₀ τ :=
  NatIso.ofComponents (fun X => recCIso τ X.1 X.2.pt) (fun {X Y} f => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext j
    change (((Y.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ)
        * ((((Y.2.pt * X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ) * Subtype.val y ⟨j.1, _⟩)
      = (((X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ) * Subtype.val y ⟨j.1, _⟩
    rw [← mul_assoc, ← recSign_mul,
      show Y.2.pt⁻¹ * (Y.2.pt * X.2.pt⁻¹) = X.2.pt⁻¹ by group])

/-- Components of the calibration (paper `sec:records`): `C_{(I,ε)} = ε⁻¹ id_{L(I)}`. -/
theorem recC_hom_app (τ : ℝ) (X : RecDom × Pair ℤˣ) :
    (recC τ).hom.app X = recScalar τ X.1 (((X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ) := rfl

/-- Inverse components of the calibration (paper `sec:records`): `C⁻¹_{(I,ε)} = ε id_{L(I)}`. -/
theorem recC_inv_app (τ : ℝ) (X : RecDom × Pair ℤˣ) :
    (recC τ).inv.app X = recScalar τ X.1 (((X.2.pt : ℤˣ) : ℤ) : ℝ) := rfl

/-- Naturality of the calibration (paper `sec:records`, displayed equation):
    `C_{(J,δ)} 𝒟((I,ε) → (J,δ)) = r_{IJ} C_{(I,ε)}`. -/
theorem recC_naturality (τ : ℝ) {X Y : RecDom × Pair ℤˣ} (f : X ⟶ Y) :
    (recD τ).map f ≫ (recC τ).hom.app Y = (recC τ).hom.app X ≫ (L₀ τ).map f.1 :=
  (recC τ).hom.naturality f

/-- The calibration depends on the convention (paper `sec:records`):
    `(C R_h)_{(I,ε)} = (ε h)⁻¹ id_{L(I)} = h⁻¹ C_{(I,ε)}`. -/
theorem recC_hom_app_act (τ : ℝ) (X : RecDom × Pair ℤˣ) (h : ℤˣ) :
    (recC τ).hom.app (recData.act X h)
      = recScalar τ X.1 (((h⁻¹ : ℤˣ) : ℤ) : ℝ) ≫ (recC τ).hom.app X := by
  change recScalar τ X.1 ((((X.2.pt * h)⁻¹ : ℤˣ) : ℤ) : ℝ)
    = recScalar τ X.1 (((h⁻¹ : ℤˣ) : ℤ) : ℝ) ≫ recScalar τ X.1 (((X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ)
  rw [recScalar_comp, ← recSign_mul, mul_inv_rev, mul_comm h⁻¹]

/-- `C R_{-1} = -C` (paper `sec:records`), written as composition with `(-1) · id_{L(I)}`:
    `(C R_{-1})_{(I,ε)} = (-1) · C_{(I,ε)}`. -/
theorem recC_hom_app_act_neg_one (τ : ℝ) (X : RecDom × Pair ℤˣ) :
    (recC τ).hom.app (recData.act X (-1)) = recScalar τ X.1 (-1) ≫ (recC τ).hom.app X := by
  rw [recC_hom_app_act, recSign_inv, recSign_neg_one]

/-- `C R_{-1} = -C` with the additive negation of `Vect_ℝ` (paper `sec:records`: "In particular,
    `C R_{-1} = -C`"): the component of `C` at `(I, ε) · (-1)` is the negative of the
    component at `(I, ε)`. -/
theorem recC_hom_app_act_eq_neg (τ : ℝ) (X : RecDom × Pair ℤˣ) :
    (recC τ).hom.app (recData.act X (-1)) = -(recC τ).hom.app X := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  funext j
  change ((((X.2.pt * (-1))⁻¹ : ℤˣ) : ℤ) : ℝ) * Subtype.val y j
    = -((((X.2.pt⁻¹ : ℤˣ) : ℤ) : ℝ) * Subtype.val y j)
  rw [mul_inv_rev, recSign_mul, recSign_inv (-1), recSign_neg_one]
  ring

/-- The calibration `C` is not an invariant natural transformation (paper `sec:records`:
    "In particular, `C R_{-1} = -C`, so `C` is not invariant"). -/
theorem recC_not_invariant (τ : ℝ) :
    ¬ IsInvariantNatTrans recData (recD_isInvariant τ) (isInvariant_comp_p recData (L₀ τ))
      (recC τ).hom := by
  intro hC
  have e : (recC τ).hom.app (recData.act (RecDom.full, ⟨1⟩) (-1))
      = (recC τ).hom.app (RecDom.full, ⟨1⟩) :=
    (hC (-1) (RecDom.full, ⟨1⟩)).trans (eqToHom_comp_comp_eqToHom_self _ _ _)
  rw [recC_hom_app_act_neg_one] at e
  change recScalar τ RecDom.full (-1) ≫ recScalar τ RecDom.full ((((1 : ℤˣ)⁻¹ : ℤˣ) : ℤ) : ℝ)
    = recScalar τ RecDom.full ((((1 : ℤˣ)⁻¹ : ℤˣ) : ℤ) : ℝ) at e
  rw [recScalar_comp] at e
  have hne : (((((1 : ℤˣ)⁻¹ : ℤˣ) : ℤ) : ℝ) * (-1)) ≠ ((((1 : ℤˣ)⁻¹ : ℤˣ) : ℤ) : ℝ) := by
    rw [recSign_inv, recSign_one]
    norm_num
  exact recScalar_ne τ RecDom.full hne e

/-! ## Invariant natural transformations `𝒟 ⟶ L p` vanish -/

/-- Naturality of an invariant `T : 𝒟 ⟶ L p` along the vertical arrow `(I,ε) → (I,εh)`: since
    `T_{(I,εh)} = T_{(I,ε)}` and `L p` sends the arrow to the identity, `T_I (h · id) = T_I`
    (paper `sec:records`: invariant transformations "intertwine the sign and trivial actions"). -/
theorem recD_invariantNatTrans_vertical (τ : ℝ) (T : recD τ ⟶ recP ⋙ L₀ τ)
    (hT : IsInvariantNatTrans recData (recD_isInvariant τ) (isInvariant_comp_p recData (L₀ τ)) T)
    (X : RecDom × Pair ℤˣ) (h : ℤˣ) :
    recScalar τ X.1 (((h : ℤ) : ℝ)) ≫ T.app X = T.app X := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have e := congrArg
    (fun k : (recD τ).obj X ⟶ (recP ⋙ L₀ τ).obj (recData.act X h) => k.hom y)
    (T.naturality (recVert X h))
  have hinv : T.app (recData.act X h) = T.app X :=
    (hT h X).trans (eqToHom_comp_comp_eqToHom_self _ _ _)
  have e2 := congrArg
    (fun k : (recD τ).obj (recData.act X h) ⟶ (recP ⋙ L₀ τ).obj (recData.act X h) =>
      k.hom (((recD τ).map (recVert X h)).hom y)) hinv
  rw [recD_map_vert] at e e2
  change (T.app X).hom ((recScalar τ X.1 (((h : ℤ) : ℝ))).hom y) = (T.app X).hom y
  exact e2.symm.trans e

/-- Every component of an invariant natural transformation `T : 𝒟 ⟶ L p` vanishes
    pointwise: `T_I(-y) = T_I(y)` by vertical naturality, and linearity gives `T_I(y) = 0` over
    `ℝ` (paper `sec:records`: "`T_I(-id) = T_I`, hence `T_I = 0` over `ℝ`"). -/
theorem recD_invariantNatTrans_apply_eq_zero (τ : ℝ) (T : recD τ ⟶ recP ⋙ L₀ τ)
    (hT : IsInvariantNatTrans recData (recD_isInvariant τ) (isInvariant_comp_p recData (L₀ τ)) T)
    (X : RecDom × Pair ℤˣ) (y : (L₀ τ).obj X.1) : (T.app X).hom y = 0 := by
  have e := congrArg (fun k : (L₀ τ).obj X.1 ⟶ (L₀ τ).obj X.1 => k.hom y)
    (recD_invariantNatTrans_vertical τ T hT X (-1))
  have hlin : (T.app X).hom ((recScalar τ X.1 (((-1 : ℤˣ) : ℤ) : ℝ)).hom y)
      = (((-1 : ℤˣ) : ℤ) : ℝ) • (T.app X).hom y :=
    map_smul (T.app X).hom (((-1 : ℤˣ) : ℤ) : ℝ) y
  have e2 : (((-1 : ℤˣ) : ℤ) : ℝ) • (T.app X).hom y = (T.app X).hom y := hlin.symm.trans e
  apply Subtype.ext
  funext j
  have ej := congrArg (fun w : recordSpace τ X.1 => Subtype.val w j) e2
  change (((-1 : ℤˣ) : ℤ) : ℝ) * Subtype.val ((T.app X).hom y) j
    = Subtype.val ((T.app X).hom y) j at ej
  rw [recSign_neg_one] at ej
  change Subtype.val ((T.app X).hom y) j = 0
  linarith

/-- Every invariant natural transformation `T : 𝒟 ⟶ L p` has zero components, `T_I = 0`
    (paper `sec:records`). -/
theorem recD_invariantNatTrans_app_eq_zero (τ : ℝ) (T : recD τ ⟶ recP ⋙ L₀ τ)
    (hT : IsInvariantNatTrans recData (recD_isInvariant τ) (isInvariant_comp_p recData (L₀ τ)) T)
    (X : RecDom × Pair ℤˣ) : T.app X = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact recD_invariantNatTrans_apply_eq_zero τ T hT X y

/-- Every invariant natural transformation `𝒟 ⟶ L p` is zero (paper `sec:records`). -/
theorem recD_invariantNatTrans_eq_zero (τ : ℝ) (T : recD τ ⟶ recP ⋙ L₀ τ)
    (hT : IsInvariantNatTrans recData (recD_isInvariant τ) (isInvariant_comp_p recData (L₀ τ))
      T) : T = 0 := by
  apply NatTrans.ext
  funext X
  rw [NatTrans.app_zero]
  exact recD_invariantNatTrans_app_eq_zero τ T hT X

/-- There is no invariant natural isomorphism `𝒟 ≅ L p`: its components would vanish, but
    `L(I)` is nonzero (paper `sec:records`). -/
theorem recD_no_invariant_iso (τ : ℝ) :
    ¬ ∃ α : recD τ ≅ recP ⋙ L₀ τ,
      IsInvariantNatTrans recData (recD_isInvariant τ) (isInvariant_comp_p recData (L₀ τ))
        α.hom := by
  rintro ⟨α, hα⟩
  have h0 := recD_invariantNatTrans_apply_eq_zero τ α.hom hα (RecDom.full, ⟨1⟩)
    (recordOne τ RecDom.full)
  have h1 : (α.inv.app (RecDom.full, ⟨1⟩)).hom
      ((α.hom.app (RecDom.full, ⟨1⟩)).hom (recordOne τ RecDom.full))
      = recordOne τ RecDom.full := by
    have := congrArg (fun k : (recD τ).obj (RecDom.full, ⟨1⟩) ⟶ (recD τ).obj (RecDom.full, ⟨1⟩) =>
      k.hom (recordOne τ RecDom.full)) (α.hom_inv_id_app (RecDom.full, ⟨1⟩))
    exact this
  rw [h0, map_zero] at h1
  exact recordOne_ne_zero τ RecDom.full h1.symm

/-- For no functor `L` is there an invariant natural isomorphism `𝒟 ≅ L p`, as predicted by
    `cor:invariant-calibration` ((i) ↔ (iii)) from the nontrivial sign action (paper
    `sec:records`). -/
theorem recD_no_invariant_calibration (τ : ℝ) :
    ¬ ∃ (L : CategoryTheory.Functor.{0, 0} RecDom (ModuleCat.{0} ℝ)) (α : recD τ ≅ recP ⋙ L),
      IsInvariantNatTrans recData (recD_isInvariant τ) (isInvariant_comp_p recData L) α.hom :=
  fun h => recD_residualAction_ne_one τ RecDom.full
    ((calibration_i_iff_iii recData (recD τ) (recD_isInvariant τ)).mp h RecDom.full)

/-! ## Two information conditions for calibration (paper `sec:records`) -/

/-- The underlying set-valued raw-record functor `𝒟` is strictly invariant (paper
    `sec:records`, "View `𝒟` and `L p` as functors to sets"). -/
theorem recD_forget_isInvariant (τ : ℝ) :
    OEData.IsInvariant recData (recD τ ⋙ forget (ModuleCat.{0} ℝ)) := fun h => by
  rw [← Functor.assoc, recD_isInvariant τ h]

/-- An invariant natural transformation of set-valued functors `K : 𝒟 ⟶ L p` has a common
    component at `(I, ε)` and `(I, ε h)` (paper `sec:records`: "a common component `K_I` at
    `(I,+1)` and `(I,-1)`"). -/
theorem recInfo_common_component (τ : ℝ)
    (K : recD τ ⋙ forget (ModuleCat.{0} ℝ) ⟶ recP ⋙ L₀ τ ⋙ forget (ModuleCat.{0} ℝ))
    (hK : IsInvariantNatTrans recData (recD_forget_isInvariant τ)
      (isInvariant_comp_p recData (L₀ τ ⋙ forget (ModuleCat.{0} ℝ))) K)
    (X : RecDom × Pair ℤˣ) (h : ℤˣ) : K.app (recData.act X h) = K.app X :=
  (hK h X).trans (eqToHom_comp_comp_eqToHom_self _ _ _)

/-- Vertical naturality of an invariant set-valued `K : 𝒟 ⟶ L p`: `K_I(h y) = K_I(y)`; no
    linearity is used (paper `sec:records`, "Two information conditions for calibration"). -/
theorem recInfo_vertical (τ : ℝ)
    (K : recD τ ⋙ forget (ModuleCat.{0} ℝ) ⟶ recP ⋙ L₀ τ ⋙ forget (ModuleCat.{0} ℝ))
    (hK : IsInvariantNatTrans recData (recD_forget_isInvariant τ)
      (isInvariant_comp_p recData (L₀ τ ⋙ forget (ModuleCat.{0} ℝ))) K)
    (X : RecDom × Pair ℤˣ) (h : ℤˣ) (y : (L₀ τ).obj X.1) :
    K.app X ((recScalar τ X.1 (((h : ℤ) : ℝ))).hom y) = K.app X y := by
  have nat : K.app (recData.act X h) (((recD τ).map (recVert X h)).hom y) = K.app X y := by
    have e := types_congr_hom (K.naturality (recVert X h)) y
    rw [types_comp_apply, types_comp_apply] at e
    exact e
  rw [recInfo_common_component τ K hK X h, recD_map_vert] at nat
  exact nat

/-- An invariant natural transformation of the set-valued functors `K : 𝒟 ⟶ L p` has even
    components, `K_I(-y) = K_I(y)`, without any linearity assumption (paper `sec:records`). -/
theorem recInfo_even (τ : ℝ)
    (K : recD τ ⋙ forget (ModuleCat.{0} ℝ) ⟶ recP ⋙ L₀ τ ⋙ forget (ModuleCat.{0} ℝ))
    (hK : IsInvariantNatTrans recData (recD_forget_isInvariant τ)
      (isInvariant_comp_p recData (L₀ τ ⋙ forget (ModuleCat.{0} ℝ))) K)
    (X : RecDom × Pair ℤˣ) (y : (L₀ τ).obj X.1) : K.app X (-y) = K.app X y := by
  have e := recInfo_vertical τ K hK X (-1) y
  have hy : (recScalar τ X.1 (((-1 : ℤˣ) : ℤ) : ℝ)).hom y = -y := by
    change (((-1 : ℤˣ) : ℤ) : ℝ) • y = -y
    rw [recSign_neg_one, neg_one_smul]
  rw [hy] at e
  exact e

/-- Naturality of a common component `k` along the vertical arrow `(I,ε) → (I,-ε)` is
    precisely evenness, `k(-y) = k(y)` (paper `sec:records`: "`𝒟` sends it to `-id`, `L p` to
    `id`; naturality is therefore precisely `K_I(-y) = K_I(y)`"). -/
theorem recInfo_vertical_naturality_iff_even (τ : ℝ) (X : RecDom × Pair ℤˣ)
    (k : (recD τ ⋙ forget (ModuleCat.{0} ℝ)).obj X
      ⟶ (recP ⋙ L₀ τ ⋙ forget (ModuleCat.{0} ℝ)).obj X) :
    (recD τ ⋙ forget (ModuleCat.{0} ℝ)).map (recVert X (-1)) ≫ k
        = k ≫ (recP ⋙ L₀ τ ⋙ forget (ModuleCat.{0} ℝ)).map (recVert X (-1))
      ↔ ∀ y : (L₀ τ).obj X.1, k (-y) = k y := by
  have hD : ∀ y : (L₀ τ).obj X.1,
      ((recD τ ⋙ forget (ModuleCat.{0} ℝ)).map (recVert X (-1)) ≫ k) y = k (-y) := by
    intro y
    have hy : ((recD τ).map (recVert X (-1))).hom y = -y := by
      rw [recD_map_vert]
      change (((-1 : ℤˣ) : ℤ) : ℝ) • y = -y
      rw [recSign_neg_one, neg_one_smul]
    exact (types_comp_apply _ _ _).trans (TypeCat.congr_arg k hy)
  have hL : ∀ y : (L₀ τ).obj X.1,
      (k ≫ (recP ⋙ L₀ τ ⋙ forget (ModuleCat.{0} ℝ)).map (recVert X (-1))) y = k y :=
    fun y => rfl
  constructor
  · intro hsq y
    exact (hD y).symm.trans ((types_congr_hom hsq y).trans (hL y))
  · intro hev
    exact ConcreteCategory.hom_ext _ _ fun y => (hD y).trans ((hev y).trans (hL y).symm)

/-- An invariant set-valued `K : 𝒟 ⟶ L p` never has the identity as a component, although
    exact recovery would force `K_I = id` (paper `sec:records`: "`K_I` must be even, while exact
    recovery requires it to be the identity on a nonzero record space"). -/
theorem recInfo_invariant_ne_id (τ : ℝ)
    (K : recD τ ⋙ forget (ModuleCat.{0} ℝ) ⟶ recP ⋙ L₀ τ ⋙ forget (ModuleCat.{0} ℝ))
    (hK : IsInvariantNatTrans recData (recD_forget_isInvariant τ)
      (isInvariant_comp_p recData (L₀ τ ⋙ forget (ModuleCat.{0} ℝ))) K)
    (X : RecDom × Pair ℤˣ) : ¬ ∀ y : (L₀ τ).obj X.1, K.app X y = y := by
  intro hid
  have e := recInfo_even τ K hK X (recordOne τ X.1)
  rw [hid, hid] at e
  obtain ⟨j, hj⟩ := X.1.nonempty
  have ej := congrArg (fun w : recordSpace τ X.1 => Subtype.val w ⟨j, hj⟩) e
  change -(1 : ℝ) = 1 at ej
  norm_num at ej

/-- Exact recovery without the polarity label is impossible at every observation domain, even
    for an arbitrary (non-linear) map: no `k : L(I) → L(I)` satisfies `k(ε q) = q` for all
    `q ∈ L(I)` and `ε ∈ {+1, -1}` (paper `sec:records`: `ε = +1` forces `k = id`, then a nonzero
    `q` would need `-q = q`). -/
theorem recInfo_no_recovery_at (τ : ℝ) (I : RecDom) :
    ¬ ∃ k : (L₀ τ).obj I → (L₀ τ).obj I,
      ∀ (q : (L₀ τ).obj I) (ε : ℤˣ), k ((((ε : ℤ) : ℝ)) • q) = q := by
  rintro ⟨k, hk⟩
  have h1 := hk (-(recordOne τ I : (L₀ τ).obj I)) 1
  have h2 := hk (recordOne τ I) (-1)
  rw [recSign_one, one_smul] at h1
  rw [recSign_neg_one, neg_one_smul] at h2
  have e := h1.symm.trans h2
  obtain ⟨j, hj⟩ := I.nonempty
  have ej := congrArg (fun w : recordSpace τ I => Subtype.val w ⟨j, hj⟩) e
  change -(1 : ℝ) = 1 at ej
  norm_num at ej

/-- Exact recovery of the signed record by one convention-independent map `K_I` at each
    observation domain is impossible (paper `sec:records`, "Two information conditions for
    calibration"). -/
theorem recInfo_no_recovery (τ : ℝ) :
    ¬ ∃ K : ∀ I : RecDom, (L₀ τ).obj I → (L₀ τ).obj I,
      ∀ (I : RecDom) (q : (L₀ τ).obj I) (ε : ℤˣ), K I ((((ε : ℤ) : ℝ)) • q) = q :=
  fun ⟨K, hK⟩ => recInfo_no_recovery_at τ RecDom.full ⟨K RecDom.full, hK RecDom.full⟩
