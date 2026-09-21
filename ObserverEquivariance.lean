/-
  Symmetry Between Perspectives: Normal Forms, Descent, Calibration, and Lifts
  ===========================================================================

  A Lean 4 / mathlib formalization of the categorical and algebraic results of

      G. Ullman, *Symmetry Between Perspectives: Normal Forms, Descent, Calibration,
      and Lifts*, revised manuscript of 5 September 2026 (revision r2), source
      `doc/perspectives_invariance_calibration_2026-09-05_r2.tex`.

  Every reference below of the form `def:data`, `thm:strict`, `cor:invariant-calibration` is a
  LaTeX label of that file.  Its sections are §2 `sec:data` (normalized categorical data),
  §3 `sec:normalform` (fullness, cartesianness, normal form), §4 `sec:descent` (strict
  presentation independence), §5 `sec:symmetries` (classification of symmetry lifts, with
  `sec:normalization` and `sec:disconnected`), §6 `sec:law` (law data and a worked measurement
  model, with `sec:records`) and §7 `sec:boundaries` (with `sec:holonomy`).  This file is the
  entry point: it imports every module and runs the axiom audit.

  SCOPE
  -----
  Formalized: the categorical and algebraic content of §§2–7, including the new examples —
  `ex:twist`, the two-object example after `prop:nocleavage`, `ex:nonfaithful`, the
  `sec:holonomy` model with its `S₃` and `Q₈` special cases, and the `sec:records` measurement
  model.  `sec:records` is formalized exactly as the finite algebraic model the paper defines:
  a base of nonempty observation domains inside `{0,1,2}`, the real record spaces `L(I)` cut out
  by the free-particle relation, the sign group `G = ℤˣ`, and the sensor-polarity presentation
  `O = S × Pair(ℤˣ)`.  It is a model of a measurement convention, not physics.

  Not formalized, and claimed nowhere here: the interpretive discussion (§1 `sec:introduction`,
  §8 `sec:scope` with `sec:related`); and the cited background — smooth gauge theory and
  principal bundles, algebraic quantum field theory, Zeeman- and Wigner-type theorems,
  Noether's theorem.  Nothing here yields conservation laws, infinitesimal generators, smooth
  actions or a Lorentz group; none of those notions occurs in the source at all.  §9 `sec:lean`
  of revision r3 describes this modular development and its audit (its r2 version described
  only the earlier archived groupoid development; see AXIOM AUDIT).

  CONTEXT AND HYPOTHESES
  ----------------------
  The general development lives in the context
  `{S O G : Type*} [Category S] [Category O] [Group G] {p : O ⥤ S}` and needs nothing more.
  Neither `O` nor `S` is assumed to be a groupoid, and no connectedness, nonemptiness,
  nontriviality or commutativity is assumed unless the declaration says so.  The only
  `Groupoid` instances are those of the concrete categories `Pair X` and `Lab B Q` (Core).
  Target categories `C` are arbitrary, with universes independent of `O` and `S`.

  `OEData G p` extends `NormalizedPreDatum G p` (clauses (N1)–(N5) of `def:data`) by the single
  field `p_faithful` ((N6)); the generated projections are `NormalizedPreDatum.<field>`, while
  dot notation (`d.act`, `d.chi_comp`, …) is unchanged.  Two properties are DERIVED, not
  assumed: fullness of `p` (`OEData.isFull`, `prop:fullness`) and invertibility of the chosen
  vertical arrows (`OEData.ltrans_isIso`).

  `[IsConnected S]` is carried by the following declarations and their `@[simp]` companions, and
  by nothing else: `rigidity`, `rigidityθ`,
  `unbundled_lift_classification`, the kernel identities `ker_Φ_eq_range_Λ`,
  `ker_ΦOver_eq_range_ΛOver`, `ker_Φθ_eq_range_Λθ`, `ker_ΦθOver_eq_range_ΛθOver`, the four
  classification isomorphisms `autBoxGMulEquivProd`, `autBoxGOverMulEquivProd`,
  `autBoxGθMulEquivSemidirect`, `autBoxGθOverMulEquivSemidirect` with their specializations
  `lawPreservingAutBoxMulEquiv`, `stateStabilizerAutBoxMulEquiv` and the three `existsUnique_Λ…`
  lemmas (Core); `liftMultiplier_const`, `exists_unique_eq_liftFunctor_comp_Λ`,
  `exists_unique_eq_liftFunctorθ_comp_Λ`, `preservesCleavage_iff_exists_base_obj`,
  `preservesCleavage_iff_exists_section` (LocalLifts); `componentFunctionsMulEquiv` and
  `autBoxGOverMulEquivProdOfComponents` (Components — the componentwise classification itself
  needs NO connectedness); the parallel-family and comparison statements
  `parallel_family_eq_translate`, `parallel_family_eq_rebase_base`,
  `parallel_basepoints_eq_rebase`, `exists_unique_eq_rebase`,
  `autBoxGOverMulEquivProd_symm_eq_of_base`,
  `autBoxGθOverMulEquivSemidirect_symm_eq_of_base` and `…_conj_of_base` (BaseChange); and all of
  BaseChangeCocycle; `componentsUnique` (Components) carries it as well.  `[Nonempty S]` alone
  suffices for `ΛHom_injective`, `ΛHomOver_injective`,
  `ΛHomθ_injective`, `ΛHomθOver_injective` (injectivity is false over an empty base) and for
  `parallel_basepoints_const_unique`; `MinSpec.no_strict_retraction` assumes
  `[Nontrivial G] [Nonempty S]`.  The normal form, the section, descent, residual actions and
  calibration (§§2–4) carry none of these hypotheses.

  MODULE MAP  (module → paper labels)
  -----------------------------------
    Core                   `def:data`, `lem:coordinates`, `prop:fullness`, `prop:cartesian`,
                           `rem:groupoid`, `def:lifts`, `thm:strict`, `thm:twisted`, `def:law`
    ProductModel           `thm:normalform` (product side); the model used by `ex:twist`,
                           `sec:records` and the `prop:nocleavage` example
    MinSpec                `rem:audit` (forward), `lem:coordinates`, `prop:fullness`
    MinSpecCorrespondence  `rem:audit` (converse, round trips), `lem:coordinates`
    NormalForm             `thm:normalform`, `cor:section`, `rem:groupoid`; vertical arrows
                           of `sec:data`
    Descent                `def:vertical-trivial`, `thm:descent`, `prop:weak-descent`,
                           `ex:invariant`
    Residual               `prop:residual` and the paragraph after it
    ResidualCategory       the display after `prop:residual`
    Calibration            `cor:invariant-calibration` and its surrounding discussion
    LocalLifts             `lem:local`; the proofs of `thm:strict` and `thm:twisted`
    Components             `prop:components` (`sec:disconnected`), `prop:nocleavage`
    BaseChange             `prop:basechange`, `sec:normalization`
    Cocycles               the cocycle paragraph of `sec:normalization` (pure group theory)
    BaseChangeCocycle      normalization change ↦ its class in `H¹(H,G)`
    Examples/Twist  `ex:twist`;  Examples/TwoObject  the example after `prop:nocleavage`
    Examples/NonFaithful  `ex:nonfaithful`;  Examples/Holonomy  `sec:holonomy`, `prop:holonomy`
    Examples/Records, Examples/RecordsCalibration  `sec:records` (two halves), `def:law`
    AxiomAudit             no paper content: the executable audit commands

  DECLARATION DIRECTORY  (paper label → principal declarations)
  -------------------------------------------------------------
  `def:data`  `NormalizedPreDatum`, `OEData`, `OEData.ltrans_isIso`; `IsVertical` (NormalForm).
  `lem:coordinates`  `OEData.coord_act`, `OEData.reind_eq`, `OEData.coord_reind`,
      `OEData.coordinate_identities`.
  `rem:audit`  `MinSpec`, `OEData.toMinSpec`, `MinSpec.toOEData`, `MinSpec.liftOver`,
      `oeDataEquivMinSpec`, `OEData.ext_of_coord`.
  `prop:fullness`  `OEData.isFull`.
  `prop:cartesian`  `IsCartesianOver`, `OEData.chi_isCartesian`,
      `OEData.isCartesian_of_fullyFaithful`, `OEData.chi_split_cartesian`.
  `thm:normalform`  the STRICT inverse identities `normalFormTo_comp_normalFormFrom` and
      `normalFormFrom_comp_normalFormTo` for `normalFormTo` / `normalFormFrom` (`MinSpec` and
      `OEData` versions), lying over `S` by `normalFormTo_fst` (Core; `MinSpec.normalFormTo_comp_fst` for the
      minimal specification) / `normalFormFrom_comp_fst`;
      `normalForm_equivariant`, `normalFormTo_fst`, `normalForm_base`, `normalForm_reind`,
      `normalFormTo_map_chi`, `productData`.  `productNormalForm : O ≌ S × Pair G` and
      `projectionEquivalence` are the WEAK (equivalence) form, kept for compatibility.
  `cor:section`  `StrictSection`, `MinSpec.strictSection`, `OEData.strictSection`,
      `OEData.sectionFunctor`, `OEData.sectionFunctor_map_eq_chi`,
      `MinSpec.no_strict_retraction`.
  `rem:groupoid`  `OEData.base_hom_isIso` — not a general theorem: it takes the explicit
      hypothesis `hO : ∀ {x y : O} (f : x ⟶ y), IsIso f` — with the converse
      `OEData.hom_isIso_of_base_isIso` (hypothesis on the arrows of `S`); `MinSpec` forms
      `base_hom_isIso`, `hom_isIso_of_base_isIso`.
  `def:vertical-trivial`  `SendsToIdentity`, `VerticallyTrivial`,
      `verticallyTrivial_iff_two_clauses`.
  `thm:descent`  `strictSection_descent`, `strictSection_descent_factor`, `MinSpec.descent`,
      `OEData.descent`, `natTrans_descent`, `natTrans_descent_of_eq`,
      `StrictSection.descentEquiv`.
  `prop:weak-descent`  `weakDescentIso`, `weak_descent`.
  `ex:invariant`  `invariantPairFunctor`, `invariantPairFunctor_not_verticallyTrivial`.
  `prop:residual`  `OEData.IsInvariant` (namespaced: mathlib has a root `IsInvariant`),
      `IsInvariantNatTrans`, `residualQ`, `productInvariant_iff_factors`, `ResidualData`,
      `functorProdBGEquivResidualData`, `OEData.vertArr`, `residualAction`,
      `invariant_iff_factors`, `invariant_descends_iff_residual_trivial`; the display after it:
      `InvFun`, `invFunToProdBG`, `prodBGToInvFun`, `curry_comp_uncurry_prodBG`,
      `exists_not_isInvariantNatTrans`.
  `cor:invariant-calibration`  `calibration_i_iff_ii`, `calibration_ii_iff_iii`,
      `calibration_i_iff_iii`, `invariant_calibration_tfae`, `invariant_calibration_list_tfae`,
      `Calibration.residualAction_intertwines`, `Calibration.invariantNatTransOfResidual`,
      `unrestricted_calibration_exists`, `unrestrictedCalibration`.
  `def:lifts`  `IsGEquivariant`, `PreservesCleavage`, `IsTwistedEquivariant`, and the lift
      groups `AutBoxG`, `AutBoxGOver`, `AutBoxGθ`, `AutBoxGθOver` (the paper's `Sym_H(p)`).
  `lem:local`  `liftMultiplier`, `lift_obj_eq`, `multiplier_unique`, `lift_map_eq_liftOver`,
      `normalForm_lift_eq`, `preservesCleavage_iff_multiplier`, `liftByMultiplier`,
      `eq_autBoxGOfMultiplier`, `preservesCleavage_iff_exists_section`; twisted:
      `lift_obj_eq_twisted`, `liftByMultiplierθ`, `autBoxGθOverOfMultiplier`.
  `thm:strict`  `lift_exists`, `rigidity`, `liftAut`, `liftHom`, `Φ`, `ΛHom`, `Φ_surjective`,
      `ΛHom_injective`, `ker_Φ_eq_range_Λ`, `autBoxGMulEquivProd`; over a chosen
      `H ≤ StrictAut S`: `ΦOver`, `ΛHomOver`, `liftHomOver`, `ker_ΦOver_eq_range_ΛOver`,
      `autBoxGOverMulEquivProd`, `existsUnique_ΛHomOver_mul_of_ΦOver_eq`.
      `unbundled_lift_classification` is the elementary ∀/∃/↔ form; `idIsoΛ` and `ΛIsoId` give
      `Λ d g ≅ 𝟭 O` for every `g`.
  `thm:twisted`  `twisted_lift_exists`, `rigidityθ`, `Φθ`, `ΛHomθ`, `liftHomθ`,
      `liftHomθ_conj`, `autBoxGθMulEquivSemidirect`; over `H` with its own twist
      `θ : H →* MulAut G`: `ΦθOver`, `ΛHomθOver`, `liftHomθOver`,
      `ker_ΦθOver_eq_range_ΛθOver`, `autBoxGθOverMulEquivSemidirect`, and
      `autBoxGθOverOneMulEquiv` (trivial twist gives the untwisted theorem).
  `prop:basechange`  `OEData.rebase`, `parallel_family_eq_translate`,
      `exists_unique_eq_rebase`, `coord_eq_of_base`, `Λ_eq_conj_of_base`,
      `liftFunctorθ_eq_conj_of_base`, `autBoxGCongr`, `autBoxGOverCongr`, `autBoxGθOverCongr`.
  `sec:normalization`  `OECocycle.coboundary`, `OECocycle.IsCocycle`, `OECocycle.H1`,
      `OECocycle.cocycleSectionEquiv`, `OECocycle.H1EquivSectionClasses`,
      `OECocycle.H1EquivComplementClasses`; the bridge `baseChange_twistFactor_eq_coboundary`,
      `liftHomθOver_rebase_conj_ker`, `liftHomθOver_rebase_class`.
  `prop:components`  `componentPerm`, `componentAction`, `autBoxGOverMulEquivComponents`
      (`AutBoxGOver d H ≃* (ConnectedComponents S → G) ⋊[componentAction H G] H`),
      `componentFunctions_unique_of_isEmpty`, `autBoxGOverMulEquivProdOfComponents`.
  `prop:nocleavage`  `AutEquivOver`, `ΦEquivOver`, `objectAction`, `autEquivOverMulEquiv`,
      `kerΦEquivOverMulEquiv`, `autBoxGOverToAutEquivOver`,
      `autEquivOver_preservesCleavage_iff`; the example after it:
      `TwoObjectExample.twoObjData`, `kerEquivProd`, `transportKerMulEquiv`,
      `flipOne_not_preservesCleavage`, `diagSubgroup_ne_top`.
  `def:law`  `strictLawStabilizer`, `LawPreservingAutBox`, `lawPreservingAutBoxMulEquiv`,
      `stateStabilizer`, `stateStabilizerAutBoxMulEquiv`.
  `ex:twist`  `twistData`, `twistθ`, `twistθ_ne_one`, `twistSym`, `twistSymPerm`,
      `c3c2MulEquivS3`, `twist_conj`.  Core's older one-object witnesses are `witness`,
      `witness₂`, `labData`, `θSingleObj_zmod3_ne_one`, `zmod3SemidirectWitness`.
  `ex:nonfaithful`  `nonfaithfulProj`, `nonfaithfulPreDatum`, `nonfaithful_isEmpty_OEData`,
      `nonfaithfulLiftKernelEquiv`, `nonfaithful_kernel_not_presentationGroup`.
  `prop:holonomy`  `HolTotal`, `holReind_holBase_iff`, `holonomy_not_OEData`, `HolLift`,
      `holLift_exact`, `holLiftProjKerEquiv`, `holS3CentralizerEquiv`, `holQ8_no_section`.
  `sec:records`  `RecDom`, `RecDom.isConnected`, `recordSpace`, `L₀`, `Lℓ`, `recData`, `recA`,
      `recH`, `recSym`, `recα`, `recA_comp_L₀_ne`, `recA_comp_Lℓ_ne`; calibration half: `recD`,
      `recD_isInvariant`, `recEcal`, `recD_residualAction_hom`, `recC`, `recC_not_invariant`,
      `recD_no_invariant_iso`, `recD_no_invariant_calibration`, `recInfo_even`,
      `recInfo_no_recovery`.

  READING THE STATEMENTS
  ----------------------
  * Lean composes diagrammatically (`f ≫ g`, `F ⋙ G`), while `StrictAut`, `AutBoxG`,
    `AutBoxGOver`, `AutBoxGθOver`, `AutEquivOver` and `HolLift` multiply in operator order:
    `(e₁ * e₂).hom = e₂.hom ⋙ e₁.hom`.  The paper's `Λ_γ Ã` is the functor `Ã ⋙ Λ_γ`.
  * The lift groups and `Aut(S)` are groups of STRICT automorphisms (`StrictAut S`), as in the
    paper: a `CategoryTheory.Equivalence` has no strict inverse, and `Λ d g ≅ 𝟭 O` (`idIsoΛ`)
    would collapse the kernel.  `Λ d g` acts on arrows by transport along the chosen vertical
    arrows `ltrans`, not along the cleavage `χ`.
  * Admissibility is `IsGEquivariant` (object level) with `PreservesCleavage`; the
    morphism-level conditions are derived from (N6), and that derivation is itself formalized
    (`isGEquivariant_map_actHom`, `PreservesCleavage.map_chi`, `OEData.base_unique`,
    `AutBoxG.ext_hom`).
  * `sec:records`, the representation question: `LA ≠ L` is proved for the UNLABELED law
    functor `L₀ τ` (`recA_comp_L₀_ne`, for `τ ≠ 0`), which is the informative statement.  The
    literal reading with explicitly labeled spaces is `Lℓ τ` into `Pair RecDom × ModuleCat ℝ`
    (`recA_comp_Lℓ_ne`); there any labeled functor has trivial strict stabilizer
    (`strictLawStabilizer_Lℓ_eq_bot`), so that inequality says nothing about the law.

  AXIOM AUDIT AND BUILD STATUS
  ----------------------------
  The audit is `#assert_standard_axioms_in_modules ObserverEquivariance` at the end of this file
  (implemented in `ObserverEquivariance/AxiomAudit.lean`).  Unlike `#print axioms` it FAILS the
  build as soon as any declaration of any imported `ObserverEquivariance.*` module — auxiliary
  `_proof_n` / `match_n` constants included — depends on an axiom other than `propext`,
  `Classical.choice`, `Quot.sound`.  In the pinned environment (`lean-toolchain` =
  `leanprover/lean4:v4.31.0-rc1`; mathlib rev `8834d3761934044a64c98afb757c1673fad03521` in
  `lake-manifest.json`) the run of 2026-09-17 reported all 2599 declarations in 21 modules
  clean, with `lake build` green (8518 jobs, no errors, no warnings) and no forbidden construct
  in Lean code.  `scripts/audit.sh` reruns build, scan and audit, and exits non-zero on failure.
  `BUILD_LOG.txt` in the repository root is the log of THIS revision's run (environment, exact
  commands, per-file blob hashes, scan, build and audit line).  The archived 2026-08-20 log of
  the earlier single-file groupoid development (18 audited declarations) is preserved in git
  history at commit f3f9182; the two runs certify nothing about each other.

  SEE ALSO
  --------
  `LEAN_COVERAGE.md` — coverage matrix: one row per result of §§2–7, with the Lean
  declarations, their actual hypotheses and a status;  `CHANGES.md` — what changed against the
  pre-revision snapshot, and every intentional naming or encoding deviation;
  `scripts/audit.sh` — the reproducible build, forbidden-construct scan and axiom audit.
-/
import ObserverEquivariance.Core
import ObserverEquivariance.ProductModel
import ObserverEquivariance.MinSpec
import ObserverEquivariance.MinSpecCorrespondence
import ObserverEquivariance.NormalForm
import ObserverEquivariance.LocalLifts
import ObserverEquivariance.Descent
import ObserverEquivariance.Residual
import ObserverEquivariance.ResidualCategory
import ObserverEquivariance.Calibration
import ObserverEquivariance.Components
import ObserverEquivariance.BaseChange
import ObserverEquivariance.Cocycles
import ObserverEquivariance.BaseChangeCocycle
import ObserverEquivariance.Examples.Twist
import ObserverEquivariance.Examples.TwoObject
import ObserverEquivariance.Examples.NonFaithful
import ObserverEquivariance.Examples.Holonomy
import ObserverEquivariance.Examples.Records
import ObserverEquivariance.Examples.RecordsCalibration
import ObserverEquivariance.AxiomAudit

/-! ## Diagnostic `#print axioms` block (retained from the archived snapshot)

  These commands are RETAINED from the archived 2026-08-20 single-file groupoid development
  (whose log is preserved in git history at commit f3f9182); they are diagnostics only, and a
  build succeeds whatever they
  print.  The authoritative check for THIS revision is the executable audit below, which fails
  the build on any nonstandard axiom in any module. -/

#print axioms OEData.chi_isCartesian
#print axioms productNormalForm
#print axioms normalForm_equivariant
#print axioms normalForm_base
#print axioms normalForm_reind
#print axioms projectionEquivalence
#print axioms OEData.base_hom_isIso
#print axioms idIsoΛ
#print axioms liftAut
#print axioms autBoxGMulEquivProd
#print axioms autBoxGOverMulEquivProd
#print axioms lawPreservingAutBoxMulEquiv
#print axioms autBoxGθOverMulEquivSemidirect
#print axioms θSingleObj_zmod3_ne_one
#print axioms zmod3SemidirectWitness
-- The remaining identifiers audited for the archived snapshot (the r2 article's `tab:lean`) that are
-- not already in the dependency closure of the commands above (`lift_exists`, `rigidity`,
-- `ker_Φ_eq_range_Λ` are reached via `autBoxGMulEquivProd`; `autBoxGθMulEquivSemidirect` via
-- `zmod3SemidirectWitness`).
#print axioms twisted_lift_exists
#print axioms rigidityθ
#print axioms normalFormTo_fst

/-! ## Executable axiom audit (this revision)

  Unlike `#print axioms`, the commands below FAIL the build if a declaration depends on any axiom
  other than `propext`, `Classical.choice`, `Quot.sound` (see `ObserverEquivariance/AxiomAudit.lean`).
  The first command checks every declaration — auxiliary `_proof_n`/`match_n` constants included —
  of every `ObserverEquivariance.*` module imported above. -/

#assert_standard_axioms_in_modules ObserverEquivariance
