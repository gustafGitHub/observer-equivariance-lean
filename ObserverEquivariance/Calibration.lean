import ObserverEquivariance.Residual

/-!
# The invariant calibration criterion (paper `cor:invariant-calibration`)

All statements use the canonical O-level residual action of `ObserverEquivariance.Residual`:
the vertical arrows `v_{s,r} = d.vertArr s r : b_s ⟶ b_s · r`, the residual endomorphisms
`hF.residualHom s r = F(v_{s,r}) ≫ cast`, and `residualAction d F hF s : G →* Aut (F b_s)`.

Paper labels covered in this file:

* The paragraph before `cor:invariant-calibration` ("Such an `α` has components
  `α_(s,a) = α_(s,1)`; naturality along vertical arrows is exactly the intertwining condition"):
  the forward direction, invariant natural transformations intertwine the residual actions
  (`Calibration.residualAction_intertwines`); the converse construction of an invariant `α` with
  `α_x = β_{p x}` from a basepoint family `β` natural along the section arrows and intertwining
  the residual actions (`Calibration.invariantNatTransOfResidual`,
  `Calibration.isInvariantNatTrans_invariantNatTransOfResidual`,
  `Calibration.invariantNatTransOfResidual_app_base`); and the iff with uniqueness
  (`Calibration.existsUnique_invariantNatTrans_iff`).
* `cor:invariant-calibration`, for strictly invariant `F`:
  (i) `∃ L, ∃ α : F ≅ p ⋙ L` invariant; (ii) `∃ E, p ⋙ E = F`; (iii) every `σ_s` is trivial.
  Separate implications `residualAction_trivial_of_invariant_iso` ((i) → (iii), the paper's proof:
  naturality along `v_{s,r}`, invariance of `α`, cancellation of the iso),
  `invariant_iso_of_factors` ((ii) → (i), the identity transformation),
  `residualAction_trivial_of_factors` ((ii) → (iii)),
  `verticallyTrivial_of_residualAction_trivial` + `thm:descent` ((iii) → (ii)); the iffs
  `calibration_i_iff_ii`, `calibration_ii_iff_iii` (= `invariant_descends_iff_residual_trivial`),
  `calibration_i_iff_iii`, the bundled `invariant_calibration_tfae` and its `List.TFAE` form
  `invariant_calibration_list_tfae`.
* The discussion after `cor:invariant-calibration`: triviality of a `G`-action is invariant under
  isomorphism in `C^{BG}` (`Calibration.action_trivial_iff_of_intertwining`, and its instance
  for invariant natural isomorphisms `Calibration.residualAction_trivial_iff_of_invariant_iso`);
  a nontrivial residual action rules out an invariant comparison with strictly shared data
  (`no_invariant_calibration_of_residualAction_ne_one`); and factorization up to an
  UNRESTRICTED natural isomorphism is automatic, with no invariance hypothesis
  (`unrestricted_calibration_exists`, from `prop:weak-descent`, with explicit witness
  `unrestrictedCalibration`); for invariant `F` this unrestricted calibration is invariant iff
  every residual action is trivial (`unrestrictedCalibration_invariant_iff`).
* Not formalized: the remark "The diagonal orbit category is `O/G ≅ S × BG` in the chosen
  coordinates" after `cor:invariant-calibration` (no orbit category is constructed; see the
  unique factorization `invariant_iff_factors` through `N ⋙ Q` in `Residual`).  The claim that
  an unrestricted iso can identify functors with DIFFERENT residual actions is formalized only
  in the `sec:records` instance (`Examples.RecordsCalibration`).
-/

open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}
variable {C : Type*} [Category C]

namespace Calibration

/-! ## Invariant transformations intertwine residual actions -/

/-- An invariant natural transformation `α : F ⟶ F'` intertwines the residual actions:
    `α_{b_s} σ_s(r) = σ'_s(r) α_{b_s}` (operator order).  Proof as in the paper: naturality of
    `α` along the vertical arrow `v_{s,r}` and invariance `α_{b_s · r} = α_{b_s}` (paragraph
    before paper `cor:invariant-calibration`: "naturality along vertical arrows is exactly the
    intertwining condition"; used in the proof of `cor:invariant-calibration`).  This is only the
    forward direction; the converse is `invariantNatTransOfResidual` and the iff is
    `existsUnique_invariantNatTrans_iff`. -/
theorem residualAction_intertwines (d : OEData G p) {F F' : O ⥤ C}
    (hF : OEData.IsInvariant d F) (hF' : OEData.IsInvariant d F') (α : F ⟶ F')
    (hα : IsInvariantNatTrans d hF hF' α) (s : S) (r : G) :
    (residualAction d F hF s r).hom ≫ α.app (d.base s)
      = α.app (d.base s) ≫ (residualAction d F' hF' s r).hom := by
  have h1 : eqToHom (hF.obj_eq r (d.base s)) ≫ α.app (d.base s)
      = α.app (d.act (d.base s) r) ≫ eqToHom (hF'.obj_eq r (d.base s)) := by
    rw [hα r (d.base s)]
    simp
  have nat : F.map (d.vertArr s r) ≫ α.app (d.act (d.base s) r)
      = α.app (d.base s) ≫ F'.map (d.vertArr s r) :=
    α.naturality (d.vertArr s r)
  rw [residualAction_hom, residualAction_hom, Category.assoc, h1]
  simp only [← Category.assoc, nat]

/-- Transport of a basepoint family along an equality of base objects (helper for the paragraph
    before paper `cor:invariant-calibration`). -/
theorem basepointFamily_cast (d : OEData G p) {F F' : O ⥤ C}
    (β : ∀ s : S, F.obj (d.base s) ⟶ F'.obj (d.base s)) {s t : S} (e : s = t) :
    β s = eqToHom (congrArg (fun u => F.obj (d.base u)) e) ≫ β t
      ≫ eqToHom (congrArg (fun u => F'.obj (d.base u)) e).symm := by
  subst e
  simp

/-- An abstract conjugated naturality square over variable objects (helper for the paragraph
    before paper `cor:invariant-calibration`): from `E(u) β_t = β_s E'(u)` and
    `σ β_s = β_s σ'`, the cast-conjugated square commutes. -/
theorem conj_square_aux {P₀ P₁ P₂ P₃ Q₀ Q₁ Q₂ Q₃ : C}
    (a a' : P₀ = P₁) (σ : P₁ ⟶ P₁) (FB : P₁ ⟶ P₂) (b : P₂ = P₃) (b' : P₃ = P₂)
    (βs : P₁ ⟶ Q₁) (βt : P₂ ⟶ Q₂) (c c' : Q₂ = Q₃) (e : Q₁ = Q₀) (e' : Q₀ = Q₁)
    (σ' : Q₁ ⟶ Q₁) (F'B : Q₁ ⟶ Q₂)
    (hB : FB ≫ βt = βs ≫ F'B) (hI : σ ≫ βs = βs ≫ σ') :
    (eqToHom a ≫ σ ≫ FB ≫ eqToHom b) ≫ (eqToHom b' ≫ βt ≫ eqToHom c)
      = (eqToHom a' ≫ βs ≫ eqToHom e) ≫ (eqToHom e' ≫ σ' ≫ F'B ≫ eqToHom c') := by
  subst a b e
  simp [reassoc_of% hB, reassoc_of% hI]

/-- The converse of `residualAction_intertwines` (paragraph before paper
    `cor:invariant-calibration`: "Such an `α` has components `α_(s,a) = α_(s,1)`; naturality along
    vertical arrows is exactly the intertwining condition"): a family `β_s : F(b_s) ⟶ F'(b_s)`
    that is natural along the section arrows `B(u)` and intertwines the residual actions defines
    the natural transformation `α_x = β_{p x}`, constant on fibers up to the casts
    `F(x) = F(b_{p x})`. -/
def invariantNatTransOfResidual (d : OEData G p) {F F' : O ⥤ C} (hF : OEData.IsInvariant d F)
    (hF' : OEData.IsInvariant d F') (β : ∀ s : S, F.obj (d.base s) ⟶ F'.obj (d.base s))
    (hnat : ∀ (s t : S) (u : s ⟶ t),
      F.map (d.sectionFunctor.map u) ≫ β t = β s ≫ F'.map (d.sectionFunctor.map u))
    (hint : ∀ (s : S) (r : G),
      (residualAction d F hF s r).hom ≫ β s = β s ≫ (residualAction d F' hF' s r).hom) :
    F ⟶ F' where
  app x := eqToHom (hF.obj_base_eq x).symm ≫ β (p.obj x) ≫ eqToHom (hF'.obj_base_eq x)
  naturality x y f := by
    rw [hF.map_eq_residualAction f (hF.obj_base_eq x).symm (hF.obj_base_eq y),
      hF'.map_eq_residualAction f (hF'.obj_base_eq x).symm (hF'.obj_base_eq y)]
    exact conj_square_aux (hB := hnat (p.obj x) (p.obj y) (p.map f))
      (hI := hint (p.obj x) (d.coord y * (d.coord x)⁻¹)) ..

/-- Components of `invariantNatTransOfResidual`: `α_x = β_{p x}` up to the casts (paragraph
    before paper `cor:invariant-calibration`). -/
theorem invariantNatTransOfResidual_app (d : OEData G p) {F F' : O ⥤ C}
    (hF : OEData.IsInvariant d F) (hF' : OEData.IsInvariant d F')
    (β : ∀ s : S, F.obj (d.base s) ⟶ F'.obj (d.base s)) hnat hint (x : O) :
    (invariantNatTransOfResidual d hF hF' β hnat hint).app x
      = eqToHom (hF.obj_base_eq x).symm ≫ β (p.obj x) ≫ eqToHom (hF'.obj_base_eq x) := rfl

/-- `invariantNatTransOfResidual` has basepoint components `α_{b_s} = β_s` (paragraph before
    paper `cor:invariant-calibration`). -/
theorem invariantNatTransOfResidual_app_base (d : OEData G p) {F F' : O ⥤ C}
    (hF : OEData.IsInvariant d F) (hF' : OEData.IsInvariant d F')
    (β : ∀ s : S, F.obj (d.base s) ⟶ F'.obj (d.base s)) hnat hint (s : S) :
    (invariantNatTransOfResidual d hF hF' β hnat hint).app (d.base s) = β s := by
  rw [invariantNatTransOfResidual_app, basepointFamily_cast d β (d.p_base s)]
  simp

/-- `invariantNatTransOfResidual` is an invariant natural transformation, `α R_h = α`
    (paragraph before paper `cor:invariant-calibration`). -/
theorem isInvariantNatTrans_invariantNatTransOfResidual (d : OEData G p) {F F' : O ⥤ C}
    (hF : OEData.IsInvariant d F) (hF' : OEData.IsInvariant d F')
    (β : ∀ s : S, F.obj (d.base s) ⟶ F'.obj (d.base s)) hnat hint :
    IsInvariantNatTrans d hF hF' (invariantNatTransOfResidual d hF hF' β hnat hint) := by
  intro h x
  rw [invariantNatTransOfResidual_app, invariantNatTransOfResidual_app,
    basepointFamily_cast d β (d.p_act x h)]
  simp

/-- "Naturality along vertical arrows is exactly the intertwining condition", as an iff
    (paragraph before paper `cor:invariant-calibration`): for a family
    `β_s : F(b_s) ⟶ F'(b_s)` between strictly invariant functors, there is a UNIQUE invariant
    natural transformation `α : F ⟶ F'` with basepoint components `α_{b_s} = β_s` iff `β` is
    natural along the section arrows `B(u)` and intertwines the residual actions,
    `σ'_s(r) β_s = β_s σ_s(r)` (operator order). -/
theorem existsUnique_invariantNatTrans_iff (d : OEData G p) {F F' : O ⥤ C}
    (hF : OEData.IsInvariant d F) (hF' : OEData.IsInvariant d F')
    (β : ∀ s : S, F.obj (d.base s) ⟶ F'.obj (d.base s)) :
    (∃! α : F ⟶ F', IsInvariantNatTrans d hF hF' α ∧ ∀ s, α.app (d.base s) = β s)
      ↔ (∀ (s t : S) (u : s ⟶ t),
          F.map (d.sectionFunctor.map u) ≫ β t = β s ≫ F'.map (d.sectionFunctor.map u))
        ∧ ∀ (s : S) (r : G),
          (residualAction d F hF s r).hom ≫ β s = β s ≫ (residualAction d F' hF' s r).hom := by
  constructor
  · rintro ⟨α, ⟨hα, hβ⟩, -⟩
    refine ⟨fun s t u => ?_, fun s r => ?_⟩
    · rw [← hβ s, ← hβ t]
      exact α.naturality (d.sectionFunctor.map u)
    · rw [← hβ s]
      exact residualAction_intertwines d hF hF' α hα s r
  · rintro ⟨hnat, hint⟩
    refine ⟨invariantNatTransOfResidual d hF hF' β hnat hint,
      ⟨isInvariantNatTrans_invariantNatTransOfResidual d hF hF' β hnat hint,
        invariantNatTransOfResidual_app_base d hF hF' β hnat hint⟩, ?_⟩
    rintro α ⟨hα, hβ⟩
    ext x
    have key : ∀ {X Y : O} (e : X = Y), α.app Y
        = eqToHom (congrArg F.obj e).symm ≫ α.app X ≫ eqToHom (congrArg F'.obj e) := by
      intro X Y e
      subst e
      simp
    rw [invariantNatTransOfResidual_app, ← hβ (p.obj x), key (d.base_coord x),
      hα (d.coord x) (d.base (p.obj x))]
    simp

/-- Triviality of a `G`-action is invariant under isomorphism in `C^{BG}`: if `φ : X ≅ Y`
    intertwines `ρ` and `ρ'`, then `ρ` is trivial iff `ρ'` is (discussion after paper
    `cor:invariant-calibration`). -/
theorem action_trivial_iff_of_intertwining {X Y : C} (ρ : G →* CategoryTheory.Aut X)
    (ρ' : G →* CategoryTheory.Aut Y) (φ : X ≅ Y)
    (hφ : ∀ r : G, (ρ r).hom ≫ φ.hom = φ.hom ≫ (ρ' r).hom) : ρ = 1 ↔ ρ' = 1 := by
  constructor
  · intro h
    refine MonoidHom.ext fun r => Iso.ext ?_
    have e : φ.hom ≫ (ρ' r).hom = φ.hom ≫ 𝟙 Y := by
      rw [← hφ r, h, Category.comp_id]
      exact Category.id_comp φ.hom
    show (ρ' r).hom = 𝟙 Y
    simpa using congrArg (fun k : X ⟶ Y => φ.inv ≫ k) e
  · intro h
    refine MonoidHom.ext fun r => Iso.ext ?_
    have e : (ρ r).hom ≫ φ.hom = 𝟙 X ≫ φ.hom := by
      rw [hφ r, h, Category.id_comp]
      exact Category.comp_id φ.hom
    show (ρ r).hom = 𝟙 X
    simpa using congrArg (fun k : X ⟶ Y => k ≫ φ.inv) e

/-- For an invariant natural isomorphism `α : F ≅ F'` between strictly invariant functors, the
    residual action of `F` at `s` is trivial iff that of `F'` is: `α_{b_s}` is an isomorphism in
    `C^{BG}` (discussion after paper `cor:invariant-calibration`: "triviality of a `G`-action is
    invariant under isomorphism in `C^{BG}`"). -/
theorem residualAction_trivial_iff_of_invariant_iso (d : OEData G p) {F F' : O ⥤ C}
    (hF : OEData.IsInvariant d F) (hF' : OEData.IsInvariant d F') (α : F ≅ F')
    (hα : IsInvariantNatTrans d hF hF' α.hom) (s : S) :
    residualAction d F hF s = 1 ↔ residualAction d F' hF' s = 1 :=
  action_trivial_iff_of_intertwining _ _ (α.app (d.base s))
    (residualAction_intertwines d hF hF' α.hom hα s)

end Calibration

/-! ## The invariant calibration criterion (paper `cor:invariant-calibration`) -/

/-- (ii) → (iii): if `F = p ⋙ E` strictly, every residual action is trivial, since
    `p ⋙ E` sends the vertical arrows `v_{s,r}` to identities (paper
    `cor:invariant-calibration`, via `prop:residual` and `thm:descent`). -/
theorem residualAction_trivial_of_factors (d : OEData G p) {F : O ⥤ C}
    (hF : OEData.IsInvariant d F) (hE : ∃ E : S ⥤ C, p ⋙ E = F) (s : S) :
    residualAction d F hF s = 1 :=
  (invariant_descends_iff_residual_trivial d F hF).mp hE s

/-- (iii) → vertical triviality: if every residual action of the invariant functor `F` is
    trivial, then `F` sends every vertical arrow to an identity (paper `prop:residual`, last
    assertion, and `cor:invariant-calibration`). -/
theorem verticallyTrivial_of_residualAction_trivial (d : OEData G p) {F : O ⥤ C}
    (hF : OEData.IsInvariant d F) (h1 : ∀ s, residualAction d F hF s = 1) :
    VerticallyTrivial p F :=
  hF.verticallyTrivial_iff_residualAction_trivial.mpr h1

/-- (iii) → (ii): trivial residual actions give a strict factorization `F = p ⋙ E`
    (paper `cor:invariant-calibration`, via `prop:residual` and `thm:descent`). -/
theorem factors_of_residualAction_trivial (d : OEData G p) {F : O ⥤ C}
    (hF : OEData.IsInvariant d F) (h1 : ∀ s, residualAction d F hF s = 1) :
    ∃ E : S ⥤ C, p ⋙ E = F :=
  ((d.descent F).mp (verticallyTrivial_of_residualAction_trivial d hF h1)).exists

/-- (i) → (iii), following the paper: for an invariant natural isomorphism `α : F ≅ p ⋙ L`,
    naturality along `v_{s,r}` gives `α_{b_s·r} σ_s(r) = α_{b_s}` because `Lp(v_{s,r})` is an
    identity; invariance makes `α_{b_s·r} = α_{b_s}`; cancelling the isomorphism gives
    `σ_s(r) = id` (paper `cor:invariant-calibration`, proof). -/
theorem residualAction_trivial_of_invariant_iso (d : OEData G p) {F : O ⥤ C}
    (hF : OEData.IsInvariant d F) {L : S ⥤ C} (α : F ≅ p ⋙ L)
    (hα : IsInvariantNatTrans d hF (isInvariant_comp_p d L) α.hom) (s : S) :
    residualAction d F hF s = 1 := by
  refine MonoidHom.ext fun r => Iso.ext ?_
  have hL : (residualAction d (p ⋙ L) (isInvariant_comp_p d L) s r).hom = 𝟙 _ :=
    congrArg (fun φ : G →* CategoryTheory.Aut ((p ⋙ L).obj (d.base s)) => (φ r).hom)
      (residualAction_trivial_of_factors d (isInvariant_comp_p d L) ⟨L, rfl⟩ s)
  have key := Calibration.residualAction_intertwines d hF (isInvariant_comp_p d L) α.hom hα s r
  rw [hL, Category.comp_id] at key
  have key' := congrArg (fun k : F.obj (d.base s) ⟶ (p ⋙ L).obj (d.base s) =>
    k ≫ α.inv.app (d.base s)) key
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at key'
  exact key'

/-- (ii) → (i): if `F = p ⋙ L` strictly, the identity transformation is an invariant natural
    isomorphism `F ≅ p ⋙ L` (paper `cor:invariant-calibration`, proof). -/
theorem invariant_iso_of_factors (d : OEData G p) {F : O ⥤ C} (hF : OEData.IsInvariant d F)
    (hE : ∃ E : S ⥤ C, p ⋙ E = F) :
    ∃ (L : S ⥤ C) (α : F ≅ p ⋙ L), IsInvariantNatTrans d hF (isInvariant_comp_p d L) α.hom := by
  obtain ⟨E, rfl⟩ := hE
  exact ⟨E, Iso.refl _, isInvariantNatTrans_id d hF⟩

/-- `cor:invariant-calibration`, (i) ↔ (ii): a strictly invariant `F` has an INVARIANT natural
    isomorphism `F ≅ p ⋙ L` iff it factors strictly through `p`. -/
theorem calibration_i_iff_ii (d : OEData G p) (F : O ⥤ C) (hF : OEData.IsInvariant d F) :
    (∃ (L : S ⥤ C) (α : F ≅ p ⋙ L), IsInvariantNatTrans d hF (isInvariant_comp_p d L) α.hom)
      ↔ ∃ E : S ⥤ C, p ⋙ E = F := by
  constructor
  · rintro ⟨L, α, hα⟩
    exact factors_of_residualAction_trivial d hF
      (residualAction_trivial_of_invariant_iso d hF α hα)
  · exact invariant_iso_of_factors d hF

/-- `cor:invariant-calibration`, (ii) ↔ (iii): a strictly invariant `F` factors strictly through
    `p` iff every residual action `σ_s` is trivial (this is the last assertion of paper
    `prop:residual`, `invariant_descends_iff_residual_trivial`). -/
theorem calibration_ii_iff_iii (d : OEData G p) (F : O ⥤ C) (hF : OEData.IsInvariant d F) :
    (∃ E : S ⥤ C, p ⋙ E = F) ↔ ∀ s : S, residualAction d F hF s = 1 :=
  invariant_descends_iff_residual_trivial d F hF

/-- `cor:invariant-calibration`, (i) ↔ (iii): an invariant natural isomorphism `F ≅ p ⋙ L`
    exists iff every residual action is trivial. -/
theorem calibration_i_iff_iii (d : OEData G p) (F : O ⥤ C) (hF : OEData.IsInvariant d F) :
    (∃ (L : S ⥤ C) (α : F ≅ p ⋙ L), IsInvariantNatTrans d hF (isInvariant_comp_p d L) α.hom)
      ↔ ∀ s : S, residualAction d F hF s = 1 :=
  (calibration_i_iff_ii d F hF).trans (calibration_ii_iff_iii d F hF)

/-- The invariant calibration criterion, bundled (paper `cor:invariant-calibration`): for a
    strictly `G`-invariant `F : O ⥤ C` the conditions
    (i) there are `L : S ⥤ C` and a natural isomorphism `α : F ≅ p ⋙ L` with `α R_h = α` for
    every `h`; (ii) `F` factors strictly through `p`; (iii) every residual action `σ_s` is
    trivial, are equivalent. -/
theorem invariant_calibration_tfae (d : OEData G p) (F : O ⥤ C) (hF : OEData.IsInvariant d F) :
    ((∃ (L : S ⥤ C) (α : F ≅ p ⋙ L), IsInvariantNatTrans d hF (isInvariant_comp_p d L) α.hom)
        ↔ ∃ E : S ⥤ C, p ⋙ E = F) ∧
      ((∃ E : S ⥤ C, p ⋙ E = F) ↔ ∀ s : S, residualAction d F hF s = 1) ∧
      ((∃ (L : S ⥤ C) (α : F ≅ p ⋙ L), IsInvariantNatTrans d hF (isInvariant_comp_p d L) α.hom)
        ↔ ∀ s : S, residualAction d F hF s = 1) :=
  ⟨calibration_i_iff_ii d F hF, calibration_ii_iff_iii d F hF, calibration_i_iff_iii d F hF⟩

/-- The invariant calibration criterion as a `List.TFAE` statement over the conditions
    (i), (ii), (iii) of paper `cor:invariant-calibration`. -/
theorem invariant_calibration_list_tfae (d : OEData G p) (F : O ⥤ C)
    (hF : OEData.IsInvariant d F) :
    List.TFAE
      [∃ (L : S ⥤ C) (α : F ≅ p ⋙ L), IsInvariantNatTrans d hF (isInvariant_comp_p d L) α.hom,
        ∃ E : S ⥤ C, p ⋙ E = F,
        ∀ s : S, residualAction d F hF s = 1] := by
  tfae_have 1 ↔ 2 := calibration_i_iff_ii d F hF
  tfae_have 2 ↔ 3 := calibration_ii_iff_iii d F hF
  tfae_finish

/-- A nontrivial residual action at some base object rules out any invariant natural
    isomorphism `F ≅ p ⋙ L` ("data carrying a nontrivial residual action cannot be isomorphic to
    strictly shared data through an invariant comparison", discussion after paper
    `cor:invariant-calibration`). -/
theorem no_invariant_calibration_of_residualAction_ne_one (d : OEData G p) {F : O ⥤ C}
    (hF : OEData.IsInvariant d F) {s : S} (hs : residualAction d F hF s ≠ 1) :
    ¬ ∃ (L : S ⥤ C) (α : F ≅ p ⋙ L), IsInvariantNatTrans d hF (isInvariant_comp_p d L) α.hom :=
  fun h => hs ((calibration_i_iff_iii d F hF).mp h s)

/-- Factorization up to an UNRESTRICTED natural isomorphism is automatic: every functor
    `F : O ⥤ C`, invariant or not, is isomorphic to some `p ⋙ L`, namely `L = B ⋙ F`
    (discussion after paper `cor:invariant-calibration`, from `prop:weak-descent`).  Contrast
    `calibration_i_iff_iii`, where the isomorphism is required to be invariant. -/
theorem unrestricted_calibration_exists (d : OEData G p) (F : O ⥤ C) :
    ∃ L : S ⥤ C, Nonempty (F ≅ p ⋙ L) :=
  ⟨d.sectionFunctor ⋙ F, ⟨(d.weakDescentIso F).symm⟩⟩

/-- The unrestricted calibration of any `F : O ⥤ C`: the natural isomorphism
    `F ≅ p ⋙ (B ⋙ F)`, inverse of the weak descent isomorphism `F η` (discussion after paper
    `cor:invariant-calibration`, from `prop:weak-descent`; the witness of
    `unrestricted_calibration_exists`). -/
noncomputable def unrestrictedCalibration (d : OEData G p) (F : O ⥤ C) :
    F ≅ p ⋙ (d.sectionFunctor ⋙ F) :=
  (d.weakDescentIso F).symm

/-- Dependence of the unrestricted calibration on the presentation, in general form (discussion
    after paper `cor:invariant-calibration`, contrasting `prop:weak-descent`): for strictly
    invariant `F`, the
    unrestricted calibration `F ≅ p ⋙ (B ⋙ F)` is an INVARIANT natural isomorphism iff every
    residual action of `F` is trivial.  So it fails to be invariant exactly when some `σ_s` is
    nontrivial (special case in `sec:records`: `recC_not_invariant`). -/
theorem unrestrictedCalibration_invariant_iff (d : OEData G p) (F : O ⥤ C)
    (hF : OEData.IsInvariant d F) :
    IsInvariantNatTrans d hF (isInvariant_comp_p d (d.sectionFunctor ⋙ F))
        (unrestrictedCalibration d F).hom
      ↔ ∀ s : S, residualAction d F hF s = 1 := by
  constructor
  · intro h
    exact (calibration_i_iff_iii d F hF).mp ⟨_, _, h⟩
  · intro h1
    have hvt : VerticallyTrivial p F := verticallyTrivial_of_residualAction_trivial d hF h1
    have happ : ∀ x : O, ∃ e, (unrestrictedCalibration d F).hom.app x = eqToHom e := by
      intro x
      obtain ⟨e, he⟩ := hvt _ (d.sectionEta_isVertical x)
      have hh : (d.weakDescentIso F).app x = eqToIso e := Iso.ext he
      refine ⟨e.symm, ?_⟩
      show ((d.weakDescentIso F).app x).inv = eqToHom e.symm
      rw [hh]
      rfl
    intro h x
    obtain ⟨e₁, he₁⟩ := happ (d.act x h)
    obtain ⟨e₂, he₂⟩ := happ x
    rw [he₁, he₂]
    simp
