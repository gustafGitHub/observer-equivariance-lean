/-
  Observer Equivariance as a Condition for Shared Physical Law
  ----------------------------------------------------------------
  Lean 4 / mathlib formalization of the strict classification theorem (§4) of
  G. Ullman, *Observer Equivariance as a Condition for Shared Physical Law*:

      1 → G → Aut□_G(O/p) → Aut(S) → 1.

  STATUS: builds cleanly, no `sorry`.  `#print axioms` reports only standard mathlib axioms
  ([propext, Classical.choice, Quot.sound]) on the main theorem-level results (no `sorryAx`).
  Proven:
    • `strict_lift` (§4.1): every base autoequivalence lifts to a `G`-equivariant,
      cleavage-preserving bundle autoequivalence covering it (⇒ Φ surjective);
    • `rigidity`  (§4.2): two such lifts of one base symmetry differ by a unique `Λ d g`;
    • `exact_sequence` (§4.3, elementary `∀/∃/↔` form): Φ surjective; ker = {Λ d g}.
    • GROUP form of §4.3:  `Φ : AutBoxG d →* StrictAut S` and `Λ : G →* AutBoxG d` are
      genuine group homomorphisms (`MonoidHom`), with `Φ_surjective`, `ΛHom_injective`
      (needs `Nonempty S`) and `ker_Φ_eq_range_Λ : (Φ d).ker = (ΛHom d).range`.  This is the
      short exact sequence  1 → G → Aut□_G(O/p) → Aut(S) → 1.
    • `witness` / `witness₂`: a concrete `OEData` for any group `G` (e.g. |G| = 2), so the
      theorem is non-vacuous and `p_faithful` is consistent with nontrivial `G`.
    • TWISTED generalization (§7): the strict SES above realizes only the DIRECT product
      `G × Aut(S)`.  For a functorial twist `θ : Aut(S) →* MulAut G` (base symmetries acting on
      the structure group), `θ`-twisted equivariance `F(x·g) = F x·(θ_A g)` gives the exact
      sequence `1 → G → Aut□^θ_G(O/p) → Aut(S) → 1` whose conjugation on the kernel is `θ`
      (`Λ_comp_liftθ`) (`strict_liftθ`, `rigidityθ`, `Φθ_surjective`, `ΛHomθ_injective`,
      `ker_Φθ_eq_range_Λθ`).  This is the home of the Poincaré model `ℝ⁴ ⋊ O(1,3) = ISO(1,3)`
      (Ex. 2, corrected: `G = ℝ⁴` translations, `Aut(S) = O(1,3)` Lorentz acting by `a ↦ Λ a`).
      Setting `θ = 1` recovers §§1–6.
    • NON-VACUOUS twist witness (§8): `labData G Q : OEData G (pLab G Q)` — the `Q`-labelled
      codiscrete groupoid on `G` over `S = SingleObj Q` — together with the NONTRIVIAL twist
      `θSingleObj G : StrictAut (SingleObj G) →* MulAut G` (`θSingleObj_surjective`,
      `θSingleObj_ne_one`).  So §7 is genuinely instantiated for `θ ≠ 1` (e.g.
      `Multiplicative (ZMod 3)`).  A literal `ℝ⁴ ⋊ O(1,3)` instance is deferred — mathlib has no
      Lorentz group `O(1,3)` yet.
    • SEMIDIRECT iso (§9): the §7 sequence packaged as an explicit group isomorphism
      `Aut□^θ_G(O/p) ≃* G ⋊[θ] Aut(S)` (`autBoxGθMulEquivSemidirect`, via `SemidirectProduct.lift`
      of `Λθ`/`liftHomθ` and `MulEquiv.ofBijective`); so `G ⋊_θ Aut(S)` is now a literal
      formalized identification, not only the exact-sequence data.

  GROUP PACKAGING NOTE.  `Aut(S)` and `Aut□_G(O/p)` are the groups of STRICT (on-the-nose)
  automorphisms (`StrictAut S` / `AutBoxG d`), not `CategoryTheory.Equivalence` (`≌`): an
  equivalence has no strict inverse (`F ⋙ F⁻¹ ≅ 𝟭`, not `= 𝟭`), and `Λ_g ≅ 𝟭` would collapse
  the kernel.  This matches the paper's `Aut(S)` = "chosen strict representatives".  The
  elementary `exact_sequence` (quantified over `A : S ≌ S`) is retained as a bridge.

  MODEL (chosen with the author — the *non-discrete* model):
    • The v0 scaffold built `Λ`/`Ã` on morphisms purely from the cleavage `χ`; that is only
      type-correct for DISCRETE fibers, and discrete fibers + the flat basepoints
      (`u*(b_t)=b_s`) + connected `O` force `G` trivial (vacuous).  Instead `Λ_g` is
      TRANSPORT along the chosen vertical translation isos `ltrans`, so it acts on in-fiber
      morphisms via the `G`-action.
    • The fibration is principal in the strong (torsor-groupoid) sense, encoded as the
      SINGLE extra assumption `p_faithful : p.Faithful` (thin fibers); `p.Full` is DERIVED
      (`OEData.isFull`).  Holds for the paper's qubit/Lorentz/action examples (see `witness`).
    • `Aut□_G` = `IsGEquivariant` (object `G`-equivariance) ∧ `PreservesCleavage` (covers
      `A`, and sends chosen cartesian sources to chosen cartesian sources).  Morphism-level
      `G`-equivariance is NOT assumed — it is a free consequence of `p` faithful.
    • `rigidity` / `exact_sequence` assume `[IsConnected S]` (the paper's "connected"):
      connectedness gives constancy of the local element `g_s`, nonemptiness its uniqueness.
-/

import Mathlib

open CategoryTheory

universe v u w

variable {S O G : Type*} [Category S] [Groupoid O] [Group G]
variable {p : O ⥤ S}

/-! ## 1. The bundle structure (Definition 3.x + normalization of §4) -/

/-- All data and axioms of a split principal `G`-fibration in groupoids
    `p : O ⥤ S`, together with a normalized transport-compatible basepoint
    section. The `□` of the paper (cleavage preservation) lives downstream in
    the predicates on automorphisms, not here. -/
structure OEData (G : Type*) [Group G] (p : O ⥤ S) where
  -- Right `G`-action on objects of `O`. (Def. 3.x (i)–(ii), object part.)
  act       : O → G → O
  act_one   : ∀ x, act x 1 = x
  act_mul   : ∀ x g h, act (act x g) h = act x (g * h)
  -- Action preserves the projection on objects. (Def. 3.x (iii).)
  p_act     : ∀ x g, p.obj (act x g) = p.obj x
  -- Freeness of the action on objects within a fiber.
  act_free  : ∀ x g h, act x g = act x h → g = h
  -- Right `G`-action on morphisms, with functoriality in the morphism slot.
  actHom    : ∀ {x y : O}, (x ⟶ y) → (g : G) → (act x g ⟶ act y g)
  actHom_id : ∀ (x : O) (g : G), actHom (𝟙 x) g = 𝟙 (act x g)
  actHom_comp : ∀ {x y z : O} (f : x ⟶ y) (h : y ⟶ z) (g : G),
      actHom (f ≫ h) g = actHom f g ≫ actHom h g
  -- Compatibility of `actHom` with `p`. (Def. 3.x (iii), morphism part.)
  p_actHom  : ∀ {x y : O} (f : x ⟶ y) (g : G),
      p.map (actHom f g)
        = eqToHom (p_act x g) ≫ p.map f ≫ eqToHom (p_act y g).symm
  -- (`actHom` records the morphism part of the right `G`-action from Def. 3.x(ii); it is part
  --  of the bundle datum.  The §4 results below act on in-fiber morphisms via `ltrans` and
  --  `p`-faithfulness, so they do not consume the cross-`g` coherence of `actHom` directly.)

  -- Normalized, transport-compatible basepoint section `b : Ob S → Ob O`.
  base       : S → O
  p_base     : ∀ s, p.obj (base s) = s
  -- Coordinate of an object relative to its basepoint:  x = base (p.obj x) · coord x.
  coord      : O → G
  base_coord : ∀ x, act (base (p.obj x)) (coord x) = x
  coord_base : ∀ s g, coord (act (base s) g) = g

  -- Chosen split cleavage: reindexed object `u*y` and the chosen cartesian lift
  -- `χ_{u,y} : u*y → y`, defined for `y` in the fiber over `t`.
  reind   : ∀ {s t : S}, (s ⟶ t) → (y : O) → p.obj y = t → O
  p_reind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      p.obj (reind u y hy) = s
  chi     : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      reind u y hy ⟶ y
  -- The chosen lift sits over `u`.
  p_chi   : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      p.map (chi u y hy) = eqToHom (p_reind u y hy) ≫ u ≫ eqToHom hy.symm
  -- Normalization: the section is flat for the cleavage  (u*(b_t) = b_s).
  reind_base : ∀ {s t : S} (u : s ⟶ t),
      reind u (base t) (p_base t) = base s
  -- `G`-stability of reindexing on objects  (transport compatibility).
  reind_act  : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) (g : G),
      reind u (act y g) ((p_act y g).trans hy) = act (reind u y hy) g
  -- `G`-stability of the chosen cartesian lifts  (Def. 3.x (iv):  χ_{u,y·g} = χ_{u,y}·g).
  chi_act    : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) (g : G),
      chi u (act y g) ((p_act y g).trans hy)
        = eqToHom (reind_act u y hy g) ≫ actHom (chi u y hy) g

  -- Normalized fiber translation, morphism level (the principal/normalized datum
  -- the author chose: "icke-diskret" model).  `ltrans g x : x ⟶ b_{p x}·(g·coord x)`
  -- is the chosen vertical iso realizing left-translation by `g` in the fiber.  It
  -- is what lets `Λ_g` act on in-fiber (vertical) morphisms via the `G`-action,
  -- not only on cartesian arrows — repairing the discrete-fiber degeneracy.
  ltrans   : ∀ (g : G) (x : O), x ⟶ act (base (p.obj x)) (g * coord x)
  -- `ltrans` is vertical (projects to an identity, up to `eqToHom`).
  p_ltrans : ∀ (g : G) (x : O),
      p.map (ltrans g x)
        = eqToHom (((p_act (base (p.obj x)) (g * coord x)).trans (p_base (p.obj x))).symm)

  -- Splitness of the cleavage (Def. 3.x: chosen lifts compatible with id and ∘).
  reind_id : ∀ {s : S} (y : O) (hy : p.obj y = s), reind (𝟙 s) y hy = y
  chi_id   : ∀ {s : S} (y : O) (hy : p.obj y = s),
      chi (𝟙 s) y hy = eqToHom (reind_id y hy)
  reind_comp : ∀ {s t r : S} (u : s ⟶ t) (v : t ⟶ r) (z : O) (hz : p.obj z = r),
      reind (u ≫ v) z hz = reind u (reind v z hz) (p_reind v z hz)
  chi_comp : ∀ {s t r : S} (u : s ⟶ t) (v : t ⟶ r) (z : O) (hz : p.obj z = r),
      chi (u ≫ v) z hz
        = eqToHom (reind_comp u v z hz) ≫ chi u (reind v z hz) (p_reind v z hz) ≫ chi v z hz

  -- Faithfulness of `p`:  fibers are "thin" — at most one morphism between two objects
  -- over each base morphism (the torsor-groupoid content of the "non-discrete" model).
  -- This is a GENUINE extra assumption, NOT derivable from the fields above: nothing here
  -- forbids extra morphisms with the same projection (`chi` is data with a projection law
  -- `p_chi`, not a cartesian *universal* property).  It holds in the paper's qubit /
  -- Lorentz / action-groupoid examples and is implicitly required by the paper's own
  -- constructions (`Ã` well defined on morphisms; the morphism step of `rigidity`).
  -- NOTE: `p.Full` is NOT assumed — it is DERIVED in `OEData.isFull` (from `chi`+`ltrans`).
  p_faithful : p.Faithful

/-! ## 2. The fiber-translation functor Λ_g  (§4.2) -/

/-- `Λ d g : O ⥤ O` is the normalized fiber translation by `g`.
    On objects: `x ↦ base (p.obj x) · (g · coord x)`.
    On morphisms it transports along the chosen translation isos `ltrans`:
    `f ↦ (ltrans g x)⁻¹ ≫ f ≫ ltrans g y`.  This is a functor for any iso family
    (no naturality needed) and acts on in-fiber morphisms via the `G`-action. -/
noncomputable def Λ (d : OEData G p) (g : G) : O ⥤ O where
  obj x := d.act (d.base (p.obj x)) (g * d.coord x)
  -- `Λ_g(f)` transports `f` along the translation isos.  This is a functor for ANY
  -- family of isos `ltrans` (no naturality needed); on a vertical `f` it gives the
  -- `g`-translate of `f`, which is the fix the non-discrete model requires.
  map {x y} f := Groupoid.inv (d.ltrans g x) ≫ f ≫ d.ltrans g y
  map_id x := by simp
  map_comp {x y z} f h := by simp

/-- `Λ d g` covers the identity on `S`:  `Λ d g ⋙ p = p`.  (So `Λ d g ∈ ker Φ`.) -/
theorem Λ_comp_p (d : OEData G p) (g : G) : Λ d g ⋙ p = p := by
  have hobj : ∀ x, (Λ d g ⋙ p).obj x = p.obj x := fun x =>
    (d.p_act (d.base (p.obj x)) (g * d.coord x)).trans (d.p_base (p.obj x))
  refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
  show p.map (Groupoid.inv (d.ltrans g x) ≫ f ≫ d.ltrans g y) = _
  simp only [p.map_comp, Groupoid.inv_eq_inv, p.map_inv, d.p_ltrans, inv_eqToHom]
  rfl

namespace OEData

/-- `coord` shifts on the right under the action:  `coord (x · g) = coord x * g`. -/
theorem coord_act (d : OEData G p) (x : O) (g : G) :
    d.coord (d.act x g) = d.coord x * g := by
  conv_lhs => rw [← d.base_coord x, d.act_mul, d.coord_base]

/-- Projection of the lift on objects:  `p (b_{A s} · coord x) = A s`. -/
theorem p_liftObj (d : OEData G p) (A : S ⥤ S) (x : O) :
    p.obj (d.act (d.base (A.obj (p.obj x))) (d.coord x)) = A.obj (p.obj x) :=
  (d.p_act _ _).trans (d.p_base _)

/-- The reindexed object in coordinates:  `u*y = b_s · coord y`. -/
theorem reind_eq (d : OEData G p) {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) :
    d.reind u y hy = d.act (d.base s) (d.coord y) := by
  have hy2 : d.act (d.base t) (d.coord y) = y := by rw [← hy]; exact d.base_coord y
  have key := d.reind_act u (d.base t) (d.p_base t) (d.coord y)
  rw [d.reind_base] at key
  simp only [hy2] at key
  exact key

/-- The coordinate of a reindexed object is unchanged:  `coord (u*y) = coord y`. -/
theorem coord_reind (d : OEData G p) {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) :
    d.coord (d.reind u y hy) = d.coord y := by
  rw [d.reind_eq, d.coord_base]

/-- `p` is FULL — this is a DERIVED consequence, not a new assumption.  A lift of a base
    morphism `w : p x ⟶ p y` is the vertical translation `ltrans` of `x` into `w*y`,
    followed by the chosen cartesian arrow `chi w y`. -/
theorem isFull (d : OEData G p) : p.Full where
  map_surjective {x y} w := by
    refine ⟨d.ltrans (d.coord (d.reind w y rfl) * (d.coord x)⁻¹) x
              ≫ eqToHom ?_ ≫ d.chi w y rfl, ?_⟩
    · conv_rhs => rw [← d.base_coord (d.reind w y rfl), d.p_reind]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    · simp [d.p_ltrans, d.p_chi, eqToHom_map]

end OEData

/-! ## 3. Predicates on bundle automorphisms -/

/-- Object-level `G`-equivariance, `F (x · g) = F x · g`.  The paper's `Aut□_G` additionally
    requires morphism-level equivariance and cleavage preservation: the latter is the
    separate predicate `PreservesCleavage`, while the former is DERIVED — given `p` faithful,
    any object-equivariant `F` covering a base map is automatically morphism-equivariant
    (its two sides have equal source/target and projection; cf. `funct_ext`).  So
    `Aut□_G` is faithfully captured by `IsGEquivariant ∧ PreservesCleavage` (see `AutBoxG`). -/
def IsGEquivariant (d : OEData G p) (F : O ⥤ O) : Prop :=
  ∀ (x : O) (g : G), F.obj (d.act x g) = d.act (F.obj x) g

/-- `F` covers the base autoequivalence `A`, i.e. `p ∘ F = A ∘ p` strictly. -/
def CoversBase (p : O ⥤ S) (F : O ⥤ O) (A : S ≌ S) : Prop :=
  F ⋙ p = p ⋙ A.functor

/-- Cleavage preservation — the `□` of `Aut□_G` (§2).  `F` covers `A` and sends each
    chosen cartesian source `u*y` to the chosen cartesian source `(A u)*(F y)`.  This is
    the object-level shadow of "F maps chosen cartesian arrows to chosen cartesian arrows";
    given `p` faithful it is equivalent to the full morphism statement `F(χ_{u,y}) = χ_{A u, F y}`.
    It is exactly what forces the local constant `g_s` in `rigidity`. -/
structure PreservesCleavage (d : OEData G p) (F : O ⥤ O) (A : S ⥤ S) : Prop where
  covers : F ⋙ p = p ⋙ A
  src : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
    F.obj (d.reind u y hy)
      = d.reind (A.map u) (F.obj y)
          ((Functor.congr_obj covers y).trans (congrArg A.obj hy))

/-! ## 4. The two key lemmas and the main theorem  (§4) -/

/-- The strict lift `Ã : O ⥤ O` of a base functor `A : S ⥤ S` (§4.1).  On objects
    `x ↦ b_{A(p x)} · coord x`; on morphisms the unique lift (`p` is fully faithful) of
    `A (p f)`.  Functoriality is automatic from faithfulness. -/
noncomputable def liftFunctor (d : OEData G p) (A : S ⥤ S) : O ⥤ O :=
  haveI := d.isFull
  haveI := d.p_faithful
  { obj := fun x => d.act (d.base (A.obj (p.obj x))) (d.coord x)
    map := fun {x y} f =>
      p.preimage (eqToHom (d.p_liftObj A x) ≫ A.map (p.map f) ≫ eqToHom (d.p_liftObj A y).symm)
    map_id := fun x => by
      refine p.map_injective ?_
      simp [eqToHom_trans]
    map_comp := fun {x y z} f g => by
      refine p.map_injective ?_
      simp [p.map_preimage, p.map_comp, Category.assoc] }

/-- The lift is `G`-equivariant. -/
theorem lift_isGEquivariant (d : OEData G p) (A : S ⥤ S) :
    IsGEquivariant d (liftFunctor d A) := by
  intro x g
  show d.act (d.base (A.obj (p.obj (d.act x g)))) (d.coord (d.act x g))
     = d.act (d.act (d.base (A.obj (p.obj x))) (d.coord x)) g
  rw [d.p_act, d.coord_act, d.act_mul]

/-- The lift covers `A` and preserves the chosen cleavage. -/
theorem lift_preservesCleavage (d : OEData G p) (A : S ⥤ S) :
    PreservesCleavage d (liftFunctor d A) A where
  covers := by
    have hobj : ∀ x, (liftFunctor d A ⋙ p).obj x = (p ⋙ A).obj x := fun x => d.p_liftObj A x
    refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
    haveI := d.isFull
    haveI := d.p_faithful
    show p.map (p.preimage (eqToHom (d.p_liftObj A x) ≫ A.map (p.map f)
        ≫ eqToHom (d.p_liftObj A y).symm)) = _
    rw [p.map_preimage]
    rfl
  src u y hy := by
    simp only [liftFunctor, d.reind_eq, d.coord_base, d.p_act, d.p_base]

/-- Lemma (Strict existence of lifts, §4.1).  Every base autoequivalence lifts to a
    `G`-equivariant, cleavage-preserving bundle autoequivalence covering it (`∈ Aut□_G`). -/
theorem strict_lift (d : OEData G p) (A : S ≌ S) :
    ∃ F : O ⥤ O, IsGEquivariant d F ∧ PreservesCleavage d F A.functor :=
  ⟨liftFunctor d A.functor, lift_isGEquivariant d A.functor, lift_preservesCleavage d A.functor⟩

/-- Lemma (Rigidity, §4.2).  Two cleavage-preserving equivariant lifts of the same base
    autoequivalence differ by a unique normalized fiber translation.  (Uses `S` connected
    for the constancy of the local element `g_s`, and `p` faithful for the morphism step.) -/
theorem rigidity (d : OEData G p) (A : S ≌ S) [IsConnected S] (F₁ F₂ : O ⥤ O)
    (h₁ : IsGEquivariant d F₁) (h₂ : IsGEquivariant d F₂)
    (pc₁ : PreservesCleavage d F₁ A.functor) (pc₂ : PreservesCleavage d F₂ A.functor) :
    ∃! g : G, F₂ = F₁ ⋙ Λ d g := by
  haveI := d.p_faithful
  -- Two equivariant functors covering the same `A`, agreeing on objects, are equal
  -- (`p` faithful: the morphism values have equal source/target and projection).
  have funct_ext : ∀ (G₁ G₂ : O ⥤ O), (∀ x, G₁.obj x = G₂.obj x) → G₁ ⋙ p = G₂ ⋙ p →
      G₁ = G₂ := by
    intro G₁ G₂ hobj hcomp
    refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
    apply p.map_injective
    rw [p.map_comp, p.map_comp, eqToHom_map, eqToHom_map]
    exact Functor.congr_hom hcomp f
  -- Object form of an equivariant lift covering `A`:  F x = b_{A(p x)} · (k(p x) · coord x).
  have Fobj : ∀ (F : O ⥤ O), IsGEquivariant d F → F ⋙ p = p ⋙ A.functor → ∀ x,
      F.obj x = d.act (d.base (A.functor.obj (p.obj x)))
                  (d.coord (F.obj (d.base (p.obj x))) * d.coord x) := by
    intro F hF hc x
    have e1 : F.obj x = d.act (F.obj (d.base (p.obj x))) (d.coord x) := by
      conv_lhs => rw [← d.base_coord x]
      exact hF _ _
    have e2 : F.obj (d.base (p.obj x))
        = d.act (d.base (A.functor.obj (p.obj x))) (d.coord (F.obj (d.base (p.obj x)))) := by
      conv_lhs => rw [← d.base_coord (F.obj (d.base (p.obj x)))]
      congr 1
      exact congrArg d.base ((Functor.congr_obj hc (d.base (p.obj x))).trans
        (congrArg A.functor.obj (d.p_base (p.obj x))))
    rw [e1, ← d.act_mul, ← e2]
  -- Local constancy of `k` from cleavage preservation:  u : s ⟶ t ⇒ k s = k t.
  have kconst : ∀ (F : O ⥤ O), F ⋙ p = p ⋙ A.functor → PreservesCleavage d F A.functor →
      ∀ {s t : S}, (s ⟶ t) → d.coord (F.obj (d.base s)) = d.coord (F.obj (d.base t)) := by
    intro F hc pc s t u
    have key := pc.src u (d.base t) (d.p_base t)
    rw [d.reind_base, d.reind_eq] at key
    have hFs : F.obj (d.base s)
        = d.act (d.base (A.functor.obj s)) (d.coord (F.obj (d.base s))) := by
      conv_lhs => rw [← d.base_coord (F.obj (d.base s))]
      congr 1
      exact congrArg d.base ((Functor.congr_obj hc (d.base s)).trans
        (congrArg A.functor.obj (d.p_base s)))
    rw [hFs] at key
    exact d.act_free _ _ _ key
  -- `k₁`, `k₂` are globally constant since `S` is connected.
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  have k₁c : ∀ s, d.coord (F₁.obj (d.base s)) = d.coord (F₁.obj (d.base s₀)) := fun s =>
    constant_of_preserves_morphisms (fun s => d.coord (F₁.obj (d.base s)))
      (fun _ _ u => kconst F₁ pc₁.covers pc₁ u) s s₀
  have k₂c : ∀ s, d.coord (F₂.obj (d.base s)) = d.coord (F₂.obj (d.base s₀)) := fun s =>
    constant_of_preserves_morphisms (fun s => d.coord (F₂.obj (d.base s)))
      (fun _ _ u => kconst F₂ pc₂.covers pc₂ u) s s₀
  have hcovΛ : ∀ g, (F₁ ⋙ Λ d g) ⋙ p = p ⋙ A.functor := by
    intro g
    rw [Functor.assoc, Λ_comp_p]; exact pc₁.covers
  refine ⟨d.coord (F₂.obj (d.base s₀)) * (d.coord (F₁.obj (d.base s₀)))⁻¹, ?_, ?_⟩
  · -- F₂ = F₁ ⋙ Λ d g
    refine funct_ext _ _ (fun x => ?_) ?_
    · -- objects
      rw [Fobj F₂ h₂ pc₂.covers x]
      show _ = (Λ d _).obj (F₁.obj x)
      rw [Fobj F₁ h₁ pc₁.covers x]
      simp only [Λ, d.p_act, d.p_base, d.coord_base]
      rw [k₂c (p.obj x), k₁c (p.obj x)]
      congr 1
      group
    · rw [pc₂.covers]; exact (hcovΛ _).symm
  · -- uniqueness:  any `g'` with `F₂ = F₁ ⋙ Λ d g'` equals `g` (evaluate at `b_{s₀}`)
    intro g' hg'
    have hev := congrArg (fun (F : O ⥤ O) => d.coord (F.obj (d.base s₀))) hg'
    simp only [Functor.comp_obj, Λ, d.coord_base] at hev
    -- hev : coord (F₂ b_{s₀}) = g' * coord (F₁ b_{s₀})
    rw [hev]; group

/-- `𝟭 O` is `G`-equivariant. -/
theorem id_isGEquivariant (d : OEData G p) : IsGEquivariant d (𝟭 O) := fun _ _ => rfl

/-- `𝟭 O` preserves the chosen cleavage (over `id_S`). -/
theorem id_preservesCleavage (d : OEData G p) :
    PreservesCleavage d (𝟭 O) (𝟭 S) where
  covers := by rw [Functor.id_comp, Functor.comp_id]
  src _ _ _ := rfl

/-- `Λ d g` is `G`-equivariant. -/
theorem Λ_isGEquivariant (d : OEData G p) (g : G) : IsGEquivariant d (Λ d g) := by
  intro x h
  show d.act (d.base (p.obj (d.act x h))) (g * d.coord (d.act x h))
     = d.act (d.act (d.base (p.obj x)) (g * d.coord x)) h
  rw [d.p_act, d.coord_act, d.act_mul, mul_assoc]

/-- `Λ d g` preserves the chosen cleavage (over `id_S`), hence lies in `ker Φ`. -/
theorem Λ_preservesCleavage (d : OEData G p) (g : G) :
    PreservesCleavage d (Λ d g) (𝟭 S) where
  covers := by rw [Λ_comp_p, Functor.comp_id]
  src u y hy := by
    simp only [Λ, d.reind_eq, d.coord_base, d.p_act, d.p_base, Functor.id_obj]

/-- Theorem (Strict classification of lifted symmetries, §4.3) — exactness form.

    `Φ : Aut□_G(O/p) → Aut(S)` is surjective (first conjunct), and a cleavage-preserving
    `G`-equivariant automorphism lies in `ker Φ` (covers `id_S`) iff it is a normalized
    fiber translation `Λ d g` (second conjunct).  Together with `rigidity` this is the
    short exact sequence  1 → G → Aut□_G(O/p) → Aut(S) → 1. -/
theorem exact_sequence (d : OEData G p) [IsConnected S] :
    (∀ A : S ≌ S, ∃ F : O ⥤ O, IsGEquivariant d F ∧ PreservesCleavage d F A.functor) ∧
    (∀ F : O ⥤ O, IsGEquivariant d F →
        (PreservesCleavage d F (𝟭 S) ↔ ∃ g : G, F = Λ d g)) := by
  refine ⟨fun A => strict_lift d A, ?_⟩
  intro F hF
  constructor
  · -- F ∈ ker Φ ⇒ F = Λ d g, via `rigidity` with F₁ = 𝟭 O, A = refl.
    intro hpc
    obtain ⟨g, hg, _⟩ := rigidity d (CategoryTheory.Equivalence.refl) (𝟭 O) F
      (id_isGEquivariant d) hF (id_preservesCleavage d) hpc
    exact ⟨g, by simpa only [Functor.id_comp] using hg⟩
  · -- Λ d g is cleavage-preserving over `id_S`, hence ∈ ker Φ.
    rintro ⟨g, rfl⟩
    exact Λ_preservesCleavage d g

/-! ## 5. Non-degeneracy witness

  A concrete `OEData G (pWit G)` for an ARBITRARY group `G`.  It shows the structure is
  instantiable and — crucially — that `p_faithful` (thin fibers) coexists with `|G| > 1`,
  so it does NOT silently reintroduce the discrete-fiber collapse.  `indiscrete ≠ discrete`:

  The fiber is the CODISCRETE groupoid on `G` — objects are the `|G|` group elements, with
  exactly ONE morphism between any two.  It is thin (⇒ `p` faithful) and connected, and it
  is NON-discrete: between distinct objects the hom-set is `PUnit`, not `∅`.  That non-empty
  hom is exactly what dodges the collapse (discrete fibers + flat section + connected `O`
  ⇒ `G` trivial).  Taking `G = Multiplicative (ZMod 2)` gives `|G| = 2` (see `witness₂`). -/

/-- The codiscrete groupoid on a type `X`: exactly one morphism between any two objects. -/
structure Codisc (X : Type*) where pt : X

instance (X : Type*) : Groupoid (Codisc X) where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  inv _ := ⟨⟩
  inv_comp _ := rfl
  comp_inv _ := rfl

/-- Witness projection: forget everything down to the one-object base `Codisc PUnit`. -/
def pWit (G : Type*) : Codisc G ⥤ Codisc PUnit where
  obj _ := ⟨PUnit.unit⟩
  map _ := ⟨⟩

/-- `OEData` is instantiable for EVERY group `G`, with thin fibers of size `|G|`.  Hence
    `p_faithful` is consistent with nontrivial `G`: no discrete-fiber degeneracy. -/
def witness (G : Type*) [Group G] : OEData G (pWit G) where
  act x g := ⟨x.pt * g⟩
  act_one x := by simp
  act_mul x g h := by simp [mul_assoc]
  p_act _ _ := rfl
  act_free x g h e := mul_left_cancel (congrArg Codisc.pt e)
  actHom _ _ := ⟨⟩
  actHom_id _ _ := rfl
  actHom_comp _ _ _ := rfl
  p_actHom _ _ := rfl
  base _ := ⟨1⟩
  p_base _ := rfl
  coord x := x.pt
  base_coord x := by simp
  coord_base _ g := by simp
  reind _ y _ := y
  p_reind _ _ _ := rfl
  chi _ _ _ := ⟨⟩
  p_chi _ _ _ := rfl
  reind_base _ := rfl
  reind_act _ _ _ _ := rfl
  chi_act _ _ _ _ := rfl
  ltrans _ _ := ⟨⟩
  p_ltrans _ _ := rfl
  reind_id _ _ := rfl
  chi_id _ _ := rfl
  reind_comp _ _ _ _ := rfl
  chi_comp _ _ _ _ := rfl
  p_faithful := ⟨fun _ => rfl⟩

/-- A concrete instantiation with a NONTRIVIAL structure group (`|G| = 2`): the witness
    is genuinely non-degenerate, with a 2-object connected (codiscrete) fiber. -/
def witness₂ : OEData (Multiplicative (ZMod 2)) (pWit (Multiplicative (ZMod 2))) :=
  witness _

example : Nontrivial (Multiplicative (ZMod 2)) := inferInstance

/-- Non-discreteness, made explicit: whenever `G` is nontrivial the (codiscrete) fiber
    has two DISTINCT objects joined by a morphism.  So the fiber is genuinely non-discrete
    (`Hom` between distinct objects is inhabited), even though it is thin (`p` faithful). -/
example (G : Type*) [Group G] [Nontrivial G] :
    ∃ x y : Codisc G, x ≠ y ∧ Nonempty (x ⟶ y) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  exact ⟨⟨a⟩, ⟨b⟩, fun h => hab (congrArg Codisc.pt h), ⟨⟨⟩⟩⟩

/-! ## 6. The exact sequence as a group statement (§4.3)

  We package the result as genuine group theory.  The base symmetries `Aut(S)` and the
  bundle automorphisms `Aut□_G(O/p)` must be STRICT (on-the-nose) automorphisms: with
  `CategoryTheory.Equivalence` (`≌`, up-to-iso) there is no strict inverse, and `Λ_g ≅ 𝟭`
  would collapse the kernel.  This matches the paper's `Aut(S)` = "chosen strict
  representatives of autoequivalences".  No new `OEData` assumption is used. -/

/-- A strict automorphism of a category `C`: a functor with a strict two-sided inverse
    (an isomorphism in `Cat`).  These form the group `Aut(C)` of strict autoequivalences. -/
@[ext]
structure StrictAut (C : Type*) [Category C] where
  hom : C ⥤ C
  inv : C ⥤ C
  hom_inv_id : hom ⋙ inv = 𝟭 C
  inv_hom_id : inv ⋙ hom = 𝟭 C

namespace StrictAut
variable {C : Type*} [Category C]

/-- Group of strict automorphisms.  Multiplication is composition `e₁ * e₂ = e₁ ∘ e₂`
    (apply `e₂` then `e₁`), so `(·).hom` / `(·).inv` are (anti)homomorphisms. -/
instance : Group (StrictAut C) where
  mul e₁ e₂ := ⟨e₂.hom ⋙ e₁.hom, e₁.inv ⋙ e₂.inv, by
      show e₂.hom ⋙ (e₁.hom ⋙ e₁.inv) ⋙ e₂.inv = 𝟭 C
      rw [e₁.hom_inv_id, Functor.id_comp, e₂.hom_inv_id], by
      show e₁.inv ⋙ (e₂.inv ⋙ e₂.hom) ⋙ e₁.hom = 𝟭 C
      rw [e₂.inv_hom_id, Functor.id_comp, e₁.inv_hom_id]⟩
  one := ⟨𝟭 C, 𝟭 C, rfl, rfl⟩
  inv e := ⟨e.inv, e.hom, e.inv_hom_id, e.hom_inv_id⟩
  mul_assoc a b c := by ext <;> rfl
  one_mul a := by ext <;> rfl
  mul_one a := by ext <;> rfl
  inv_mul_cancel a := by ext <;> exact a.hom_inv_id

@[simp] lemma one_hom : (1 : StrictAut C).hom = 𝟭 C := rfl
@[simp] lemma one_inv : (1 : StrictAut C).inv = 𝟭 C := rfl
@[simp] lemma mul_hom (e₁ e₂ : StrictAut C) : (e₁ * e₂).hom = e₂.hom ⋙ e₁.hom := rfl

end StrictAut

/-! ### Closure of the bundle-automorphism conditions under `⋙` and inverse -/

variable (d : OEData G p)

/-- `G`-equivariance is closed under composition. -/
theorem isGEquivariant_comp {F F' : O ⥤ O}
    (h : IsGEquivariant d F) (h' : IsGEquivariant d F') : IsGEquivariant d (F ⋙ F') :=
  fun x g => by
    show F'.obj (F.obj (d.act x g)) = d.act (F'.obj (F.obj x)) g
    rw [h x g, h' (F.obj x) g]

/-- `G`-equivariance transfers to a strict inverse. -/
theorem isGEquivariant_inv {F Finv : O ⥤ O} (hi : F ⋙ Finv = 𝟭 O) (ih : Finv ⋙ F = 𝟭 O)
    (h : IsGEquivariant d F) : IsGEquivariant d Finv := by
  have hFcancel : ∀ z, F.obj (Finv.obj z) = z := fun z => by
    have := Functor.congr_obj ih z; simpa using this
  have hinj : Function.Injective F.obj := fun a b hab => by
    have := congrArg Finv.obj hab
    have e : ∀ z, Finv.obj (F.obj z) = z := fun z => by
      have := Functor.congr_obj hi z; simpa using this
    rw [e, e] at this; exact this
  intro x g
  apply hinj
  rw [h (Finv.obj x) g, hFcancel, hFcancel]

/-- Cleavage preservation is closed under composition. -/
theorem preservesCleavage_comp {F F' : O ⥤ O} {A A' : S ⥤ S}
    (pc : PreservesCleavage d F A) (pc' : PreservesCleavage d F' A') :
    PreservesCleavage d (F ⋙ F') (A ⋙ A') where
  covers := by rw [Functor.assoc, pc'.covers, ← Functor.assoc, pc.covers, Functor.assoc]
  src u y hy := by
    simp only [Functor.comp_obj, Functor.comp_map]
    rw [pc.src u y hy, pc'.src]
    rfl

/-- Cleavage preservation transfers to a strict inverse (with the inverse base). -/
theorem preservesCleavage_inv {F Finv : O ⥤ O} {B : StrictAut S}
    (hi : F ⋙ Finv = 𝟭 O) (ih : Finv ⋙ F = 𝟭 O)
    (pc : PreservesCleavage d F B.hom) : PreservesCleavage d Finv B.inv where
  covers := by
    have h1 : (Finv ⋙ p) ⋙ B.hom = p := by
      rw [Functor.assoc, ← pc.covers, ← Functor.assoc, ih, Functor.id_comp]
    calc Finv ⋙ p
        = (Finv ⋙ p) ⋙ B.hom ⋙ B.inv := by rw [B.hom_inv_id, Functor.comp_id]
      _ = ((Finv ⋙ p) ⋙ B.hom) ⋙ B.inv := rfl
      _ = p ⋙ B.inv := by rw [h1]
  src u y hy := by
    have hFcancel : ∀ z, F.obj (Finv.obj z) = z := fun z => by
      have := Functor.congr_obj ih z; simpa using this
    have hinj : Function.Injective F.obj := fun a b hab => by
      have e : ∀ z, Finv.obj (F.obj z) = z := fun z => by
        have := Functor.congr_obj hi z; simpa using this
      have := congrArg Finv.obj hab; rw [e, e] at this; exact this
    apply hinj
    rw [hFcancel, pc.src (B.inv.map u) (Finv.obj y)]
    simp only [d.reind_eq, hFcancel]
    congr 1
    exact congrArg d.base (Functor.congr_obj B.inv_hom_id _).symm

/-- Two equivariant functors covering the same base (i.e. equal after `⋙ p`) that agree on
    objects are equal (`p` faithful). -/
theorem funct_ext (d : OEData G p) {F₁ F₂ : O ⥤ O} (hobj : ∀ x, F₁.obj x = F₂.obj x)
    (hcomp : F₁ ⋙ p = F₂ ⋙ p) : F₁ = F₂ := by
  haveI := d.p_faithful
  refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
  apply p.map_injective
  rw [p.map_comp, p.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hcomp f

/-- `Λ` is trivial at the identity:  `Λ d 1 = 𝟭 O`. -/
theorem Λ_one : Λ d (1 : G) = 𝟭 O :=
  funct_ext d (fun x => by
    show d.act (d.base (p.obj x)) (1 * d.coord x) = x
    rw [one_mul, d.base_coord]) (by rw [Λ_comp_p, Functor.id_comp])

/-- `Λ` is an (anti)homomorphism:  `Λ d g ⋙ Λ d h = Λ d (h * g)`. -/
theorem Λ_comp (g h : G) : Λ d g ⋙ Λ d h = Λ d (h * g) :=
  funct_ext d (fun x => by
    simp only [Functor.comp_obj, Λ, d.p_act, d.p_base, d.coord_base, mul_assoc])
    (by rw [Functor.assoc, Λ_comp_p, Λ_comp_p, Λ_comp_p])

/-- A bundle automorphism: a strict autoequivalence `hom` of `O` that is `G`-equivariant and
    preserves the cleavage over the strict base automorphism `base`.  Forms `Aut□_G(O/p)`. -/
@[ext]
structure AutBoxG (d : OEData G p) where
  hom : O ⥤ O
  inv : O ⥤ O
  hom_inv_id : hom ⋙ inv = 𝟭 O
  inv_hom_id : inv ⋙ hom = 𝟭 O
  base : StrictAut S
  equiv : IsGEquivariant d hom
  pres : PreservesCleavage d hom base.hom

namespace AutBoxG

instance : Group (AutBoxG d) where
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
      pres := preservesCleavage_comp d e₂.pres e₁.pres }
  one := ⟨𝟭 O, 𝟭 O, rfl, rfl, 1, id_isGEquivariant d, id_preservesCleavage d⟩
  inv e :=
    { hom := e.inv
      inv := e.hom
      hom_inv_id := e.inv_hom_id
      inv_hom_id := e.hom_inv_id
      base := e.base⁻¹
      equiv := isGEquivariant_inv d e.hom_inv_id e.inv_hom_id e.equiv
      pres := preservesCleavage_inv d e.hom_inv_id e.inv_hom_id e.pres }
  mul_assoc a b c := by refine AutBoxG.ext ?_ ?_ ?_ <;> rfl
  one_mul a := by refine AutBoxG.ext ?_ ?_ ?_ <;> rfl
  mul_one a := by refine AutBoxG.ext ?_ ?_ ?_ <;> rfl
  inv_mul_cancel a := by
    refine AutBoxG.ext ?_ ?_ ?_ <;> first | exact a.hom_inv_id | exact inv_mul_cancel _

@[simp] lemma mul_hom (e₁ e₂ : AutBoxG d) : (e₁ * e₂).hom = e₂.hom ⋙ e₁.hom := rfl
@[simp] lemma mul_base (e₁ e₂ : AutBoxG d) : (e₁ * e₂).base = e₁.base * e₂.base := rfl
@[simp] lemma one_hom : (1 : AutBoxG d).hom = 𝟭 O := rfl
@[simp] lemma one_base : (1 : AutBoxG d).base = 1 := rfl

end AutBoxG

/-- The lift is a strict homomorphism:  `liftFunctor A ⋙ liftFunctor B = liftFunctor (A ⋙ B)`. -/
theorem lift_comp (d : OEData G p) (A B : S ⥤ S) :
    liftFunctor d A ⋙ liftFunctor d B = liftFunctor d (A ⋙ B) :=
  funct_ext d
    (fun x => by simp only [Functor.comp_obj, liftFunctor, d.p_act, d.p_base, d.coord_base])
    (by rw [Functor.assoc, (lift_preservesCleavage d B).covers, ← Functor.assoc,
        (lift_preservesCleavage d A).covers, Functor.assoc, (lift_preservesCleavage d (A ⋙ B)).covers])

/-- The lift of the identity is the identity. -/
theorem lift_id (d : OEData G p) : liftFunctor d (𝟭 S) = 𝟭 O :=
  funct_ext d
    (fun x => by
      show d.act (d.base ((𝟭 S).obj (p.obj x))) (d.coord x) = x
      rw [Functor.id_obj, d.base_coord])
    (by rw [(lift_preservesCleavage d (𝟭 S)).covers, Functor.comp_id, Functor.id_comp])

/-- `Φ : Aut□_G(O/p) →* Aut(S)`:  the projection sending a bundle automorphism to the base
    symmetry it covers.  (This is the `Φ` of the short exact sequence.) -/
def Φ (d : OEData G p) : AutBoxG d →* StrictAut S where
  toFun e := e.base
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `Λ : G →* Aut□_G(O/p)`:  the normalized fiber-translation embedding. -/
noncomputable def ΛHom (d : OEData G p) : G →* AutBoxG d where
  toFun g :=
    { hom := Λ d g
      inv := Λ d g⁻¹
      hom_inv_id := by rw [Λ_comp, inv_mul_cancel, Λ_one]
      inv_hom_id := by rw [Λ_comp, mul_inv_cancel, Λ_one]
      base := 1
      equiv := Λ_isGEquivariant d g
      pres := Λ_preservesCleavage d g }
  map_one' := by
    refine AutBoxG.ext ?_ ?_ ?_
    · exact Λ_one d
    · show Λ d (1 : G)⁻¹ = 𝟭 O; rw [inv_one, Λ_one]
    · rfl
  map_mul' g h := by
    refine AutBoxG.ext ?_ ?_ ?_
    · show Λ d (g * h) = Λ d h ⋙ Λ d g; rw [Λ_comp]
    · show Λ d (g * h)⁻¹ = Λ d g⁻¹ ⋙ Λ d h⁻¹; rw [Λ_comp, mul_inv_rev]
    · rfl

/-- `Φ` is surjective:  every strict base automorphism is covered by a bundle automorphism
    (the strict lift).  (`⇒` surjectivity of the exact sequence.) -/
theorem Φ_surjective (d : OEData G p) : Function.Surjective (Φ d) := fun A =>
  ⟨{ hom := liftFunctor d A.hom
     inv := liftFunctor d A.inv
     hom_inv_id := by rw [lift_comp, A.hom_inv_id, lift_id]
     inv_hom_id := by rw [lift_comp, A.inv_hom_id, lift_id]
     base := A
     equiv := lift_isGEquivariant d A.hom
     pres := lift_preservesCleavage d A.hom }, rfl⟩

/-- `Λ` is injective (needs a basepoint; freeness of the action does the rest). -/
theorem ΛHom_injective (d : OEData G p) [Nonempty S] : Function.Injective (ΛHom d) := by
  intro g h hgh
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hev : (Λ d g).obj (d.base s₀) = (Λ d h).obj (d.base s₀) :=
    congrArg (·.obj (d.base s₀)) (congrArg AutBoxG.hom hgh)
  have hc : d.coord (d.base s₀) = 1 := by
    have h1 := d.coord_base s₀ 1; rwa [d.act_one] at h1
  simp only [Λ, d.p_base, hc, mul_one] at hev
  exact d.act_free _ _ _ hev

/-- The kernel of `Φ` is exactly the image of `Λ`:  `ker Φ = range Λ`.  This is exactness of
    `1 → G →[Λ] Aut□_G(O/p) →[Φ] Aut(S) → 1` at the middle term. -/
theorem ker_Φ_eq_range_Λ (d : OEData G p) [IsConnected S] : (Φ d).ker = (ΛHom d).range := by
  ext e
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro he
    have hb : e.base = 1 := he
    have hpc : PreservesCleavage d e.hom (𝟭 S) := by
      have hp := e.pres; rw [hb] at hp; exact hp
    obtain ⟨g, hg⟩ := ((exact_sequence d).2 e.hom e.equiv).1 hpc
    refine ⟨g, AutBoxG.ext hg.symm ?_ hb.symm⟩
    show Λ d g⁻¹ = e.inv
    have key : e.hom ⋙ Λ d g⁻¹ = 𝟭 O := by rw [hg, Λ_comp, inv_mul_cancel, Λ_one]
    calc Λ d g⁻¹ = (e.inv ⋙ e.hom) ⋙ Λ d g⁻¹ := by rw [e.inv_hom_id, Functor.id_comp]
      _ = e.inv ⋙ e.hom ⋙ Λ d g⁻¹ := rfl
      _ = e.inv := by rw [key, Functor.comp_id]
  · rintro ⟨g, rfl⟩
    rfl

/-! ## 7. Twisted (semidirect) generalization — toward the Poincaré model (§5, Ex. 2)

  The strict theorem of §§1–6 realizes only DIRECT products `G × Aut(S)`: the conjugation
  `liftFunctor A ⋙ Λ d g ⋙ (liftFunctor A)⁻¹ = Λ d g` is trivial, because strict
  `G`-equivariance commutes on the nose with the right action.  Genuine semidirect symmetry
  groups — notably the Poincaré group `ISO(1,3) = ℝ⁴ ⋊ O(1,3)` with structure group
  `G = ℝ⁴` (translations) and base symmetries `Aut(S) = O(1,3)` acting by `a ↦ Λ a` — require
  *twisted* equivariance: the lift `F` of a base symmetry `A` acts on the fiber through a
  group automorphism `θ ∈ MulAut G`,

        `F (x · g) = F x · (θ g)`,

  so that `liftFunctorθ A θ ⋙ Λ d g ⋙ (…)⁻¹ = Λ d (θ g)` (`Λ_comp_liftθ`) and the kernel `G`
  carries the nontrivial action — the semidirect structure on `Aut□^θ_G`, packaged in §9 as an
  explicit isomorphism `Aut□^θ_G ≃* G ⋊_θ Aut(S)` (`autBoxGθMulEquivSemidirect`).
  Setting `θ = 1` recovers §§1–6.

  This section proves the twisted analogues of `strict_lift` and `rigidity`, the conjugation
  relation `Λ_comp_liftθ`, and the group-level exact sequence `1 → G → Aut□^θ_G(O/p) → Aut(S) → 1`
  (`Φθ_surjective`, `ΛHomθ_injective`, `ker_Φθ_eq_range_Λθ`).  The twist threads through because
  the lift's fiber coordinate transforms by `coord_act`, on which `θ` (a homomorphism) distributes,
  and it cancels in `rigidityθ` since both lifts carry the same `θ`. -/

/-- `θ`-twisted `G`-equivariance: `F (x · g) = F x · (θ g)` for a fiber-twist `θ ∈ MulAut G`.
    `θ = 1` is ordinary (strict) `G`-equivariance. -/
def IsTwistedEquivariant (d : OEData G p) (θ : MulAut G) (F : O ⥤ O) : Prop :=
  ∀ (x : O) (g : G), F.obj (d.act x g) = d.act (F.obj x) (θ g)

/-- At `θ = 1`, twisted equivariance is exactly `IsGEquivariant`. -/
theorem isTwistedEquivariant_one (d : OEData G p) (F : O ⥤ O) :
    IsTwistedEquivariant d (1 : MulAut G) F ↔ IsGEquivariant d F := Iff.rfl

namespace OEData
/-- Projection of a twisted lift on objects (for ANY fiber element):  `p(b_{A s} · g') = A s`. -/
theorem p_liftObjθ (d : OEData G p) (A : S ⥤ S) (x : O) (g' : G) :
    p.obj (d.act (d.base (A.obj (p.obj x))) g') = A.obj (p.obj x) :=
  (d.p_act _ _).trans (d.p_base _)
end OEData

/-- The `θ`-twisted lift of a base functor `A`.  On objects `x ↦ b_{A(p x)} · θ(coord x)`;
    on morphisms the unique lift of `A(p f)` (faithfulness), exactly as `liftFunctor`. -/
noncomputable def liftFunctorθ (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) : O ⥤ O :=
  haveI := d.isFull
  haveI := d.p_faithful
  { obj := fun x => d.act (d.base (A.obj (p.obj x))) (θ (d.coord x))
    map := fun {x y} f =>
      p.preimage (eqToHom (d.p_liftObjθ A x (θ (d.coord x)))
        ≫ A.map (p.map f) ≫ eqToHom (d.p_liftObjθ A y (θ (d.coord y))).symm)
    map_id := fun x => by
      refine p.map_injective ?_
      simp [eqToHom_trans]
    map_comp := fun {x y z} f g => by
      refine p.map_injective ?_
      simp [p.map_preimage, p.map_comp, Category.assoc] }

/-- The twisted lift is `θ`-twisted `G`-equivariant (analogue of `lift_isGEquivariant`). -/
theorem liftθ_isTwistedEquivariant (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) :
    IsTwistedEquivariant d θ (liftFunctorθ d A θ) := by
  intro x g
  show d.act (d.base (A.obj (p.obj (d.act x g)))) (θ (d.coord (d.act x g)))
     = d.act (d.act (d.base (A.obj (p.obj x))) (θ (d.coord x))) (θ g)
  rw [d.p_act, d.coord_act, map_mul, d.act_mul]

/-- The twisted lift covers `A`:  `liftFunctorθ d A θ ⋙ p = p ⋙ A`. -/
theorem liftθ_covers (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) :
    liftFunctorθ d A θ ⋙ p = p ⋙ A := by
  have hobj : ∀ x, (liftFunctorθ d A θ ⋙ p).obj x = (p ⋙ A).obj x :=
    fun x => d.p_liftObjθ A x (θ (d.coord x))
  refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
  haveI := d.isFull
  haveI := d.p_faithful
  show p.map (p.preimage (eqToHom (d.p_liftObjθ A x (θ (d.coord x))) ≫ A.map (p.map f)
      ≫ eqToHom (d.p_liftObjθ A y (θ (d.coord y))).symm)) = _
  rw [p.map_preimage]
  rfl

/-- Twisted lift at `θ = 1` is the strict lift. -/
theorem liftFunctorθ_one (d : OEData G p) (A : S ⥤ S) :
    liftFunctorθ d A (1 : MulAut G) = liftFunctor d A := rfl

/-- The twisted lift preserves the chosen cleavage (same `PreservesCleavage` predicate —
    the twist does not affect the source-identity, since `coord (Ã y) = θ (coord y)`). -/
theorem liftθ_preservesCleavage (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) :
    PreservesCleavage d (liftFunctorθ d A θ) A where
  covers := liftθ_covers d A θ
  src u y hy := by
    simp only [liftFunctorθ, d.reind_eq, d.coord_base, d.p_act, d.p_base]

/-- Twisted strict lift (analogue of `strict_lift`):  every base autoequivalence admits a
    `θ`-twisted equivariant cleavage-preserving lift covering it. -/
theorem strict_liftθ (d : OEData G p) (A : S ≌ S) (θ : MulAut G) :
    ∃ F : O ⥤ O, IsTwistedEquivariant d θ F ∧ PreservesCleavage d F A.functor :=
  ⟨liftFunctorθ d A.functor θ, liftθ_isTwistedEquivariant d A.functor θ,
    liftθ_preservesCleavage d A.functor θ⟩

/-- Twisted rigidity (analogue of `rigidity`).  Two `θ`-twisted equivariant cleavage-preserving
    lifts of the same base autoequivalence (the SAME twist `θ`) differ by a unique normalized
    fiber translation `Λ d g`.  The twist cancels — both carry it — so the difference is the
    untwisted `Λ d g`.  (`[IsConnected S]`; `p` faithful for the morphism step.) -/
theorem rigidityθ (d : OEData G p) (A : S ≌ S) (θ : MulAut G) [IsConnected S] (F₁ F₂ : O ⥤ O)
    (h₁ : IsTwistedEquivariant d θ F₁) (h₂ : IsTwistedEquivariant d θ F₂)
    (pc₁ : PreservesCleavage d F₁ A.functor) (pc₂ : PreservesCleavage d F₂ A.functor) :
    ∃! g : G, F₂ = F₁ ⋙ Λ d g := by
  haveI := d.p_faithful
  have funct_ext : ∀ (G₁ G₂ : O ⥤ O), (∀ x, G₁.obj x = G₂.obj x) → G₁ ⋙ p = G₂ ⋙ p →
      G₁ = G₂ := by
    intro G₁ G₂ hobj hcomp
    refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
    apply p.map_injective
    rw [p.map_comp, p.map_comp, eqToHom_map, eqToHom_map]
    exact Functor.congr_hom hcomp f
  -- Object form of a `θ`-twisted lift:  F x = b_{A(p x)} · (k(p x) · θ(coord x)).
  have Fobj : ∀ (F : O ⥤ O), IsTwistedEquivariant d θ F → F ⋙ p = p ⋙ A.functor → ∀ x,
      F.obj x = d.act (d.base (A.functor.obj (p.obj x)))
                  (d.coord (F.obj (d.base (p.obj x))) * θ (d.coord x)) := by
    intro F hF hc x
    have e1 : F.obj x = d.act (F.obj (d.base (p.obj x))) (θ (d.coord x)) := by
      conv_lhs => rw [← d.base_coord x]
      exact hF _ _
    have e2 : F.obj (d.base (p.obj x))
        = d.act (d.base (A.functor.obj (p.obj x))) (d.coord (F.obj (d.base (p.obj x)))) := by
      conv_lhs => rw [← d.base_coord (F.obj (d.base (p.obj x)))]
      congr 1
      exact congrArg d.base ((Functor.congr_obj hc (d.base (p.obj x))).trans
        (congrArg A.functor.obj (d.p_base (p.obj x))))
    rw [e1, ← d.act_mul, ← e2]
  -- Local constancy of `k` from cleavage preservation (twist-free: evaluated at basepoints).
  have kconst : ∀ (F : O ⥤ O), F ⋙ p = p ⋙ A.functor → PreservesCleavage d F A.functor →
      ∀ {s t : S}, (s ⟶ t) → d.coord (F.obj (d.base s)) = d.coord (F.obj (d.base t)) := by
    intro F hc pc s t u
    have key := pc.src u (d.base t) (d.p_base t)
    rw [d.reind_base, d.reind_eq] at key
    have hFs : F.obj (d.base s)
        = d.act (d.base (A.functor.obj s)) (d.coord (F.obj (d.base s))) := by
      conv_lhs => rw [← d.base_coord (F.obj (d.base s))]
      congr 1
      exact congrArg d.base ((Functor.congr_obj hc (d.base s)).trans
        (congrArg A.functor.obj (d.p_base s)))
    rw [hFs] at key
    exact d.act_free _ _ _ key
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  have k₁c : ∀ s, d.coord (F₁.obj (d.base s)) = d.coord (F₁.obj (d.base s₀)) := fun s =>
    constant_of_preserves_morphisms (fun s => d.coord (F₁.obj (d.base s)))
      (fun _ _ u => kconst F₁ pc₁.covers pc₁ u) s s₀
  have k₂c : ∀ s, d.coord (F₂.obj (d.base s)) = d.coord (F₂.obj (d.base s₀)) := fun s =>
    constant_of_preserves_morphisms (fun s => d.coord (F₂.obj (d.base s)))
      (fun _ _ u => kconst F₂ pc₂.covers pc₂ u) s s₀
  have hcovΛ : ∀ g, (F₁ ⋙ Λ d g) ⋙ p = p ⋙ A.functor := by
    intro g
    rw [Functor.assoc, Λ_comp_p]; exact pc₁.covers
  refine ⟨d.coord (F₂.obj (d.base s₀)) * (d.coord (F₁.obj (d.base s₀)))⁻¹, ?_, ?_⟩
  · refine funct_ext _ _ (fun x => ?_) ?_
    · rw [Fobj F₂ h₂ pc₂.covers x]
      show _ = (Λ d _).obj (F₁.obj x)
      rw [Fobj F₁ h₁ pc₁.covers x]
      simp only [Λ, d.p_act, d.p_base, d.coord_base]
      rw [k₂c (p.obj x), k₁c (p.obj x)]
      congr 1
      group
    · rw [pc₂.covers]; exact (hcovΛ _).symm
  · intro g' hg'
    have hev := congrArg (fun (F : O ⥤ O) => d.coord (F.obj (d.base s₀))) hg'
    simp only [Functor.comp_obj, Λ, d.coord_base] at hev
    rw [hev]; group

/-- The SEMIDIRECT relation.  The fiber translation `Λ d g` commutes past the twisted lift
    `Ã = liftFunctorθ d A θ` up to twisting `g` by `θ`:
        `Λ d g ⋙ Ã = Ã ⋙ Λ d (θ g)`,   i.e.   `Ã ∘ Λ d g ∘ Ã⁻¹ = Λ d (θ g)`.
    This is trivial (`Ã Λ_g Ã⁻¹ = Λ_g`) exactly when `θ = 1` — recovering the direct product
    `G × Aut(S)` of the strict theorem — and nontrivial otherwise, making the extension semidirect
    rather than direct (the kernel `G` is acted on by `θ`, as in `ℝ⁴ ⋊ O(1,3) = ISO(1,3)`). -/
theorem Λ_comp_liftθ (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) (g : G) :
    Λ d g ⋙ liftFunctorθ d A θ = liftFunctorθ d A θ ⋙ Λ d (θ g) := by
  have hL : (Λ d g ⋙ liftFunctorθ d A θ) ⋙ p = p ⋙ A := by
    rw [Functor.assoc, liftθ_covers, ← Functor.assoc, Λ_comp_p]
  have hR : (liftFunctorθ d A θ ⋙ Λ d (θ g)) ⋙ p = p ⋙ A := by
    rw [Functor.assoc, Λ_comp_p, liftθ_covers]
  refine funct_ext d (fun x => ?_) (hL.trans hR.symm)
  simp only [Functor.comp_obj, Λ, liftFunctorθ, d.p_act, d.p_base, d.coord_base, map_mul]

/-- At `θ = 1` the semidirect relation degenerates to commutation `Λ d g ⋙ Ã = Ã ⋙ Λ d g`
    (the direct-product case): conjugation by a strict lift fixes every `Λ d g`. -/
theorem Λ_comp_lift_one (d : OEData G p) (A : S ⥤ S) (g : G) :
    Λ d g ⋙ liftFunctor d A = liftFunctor d A ⋙ Λ d g := by
  have := Λ_comp_liftθ d A (1 : MulAut G) g
  rwa [liftFunctorθ_one] at this

/-- Composition of twisted lifts:  `liftθ A θ ⋙ liftθ B φ = liftθ (A ⋙ B) (φ * θ)`.  The
    twists multiply in `MulAut G` (contravariantly, matching the lift's action on coordinates). -/
theorem liftθ_comp (d : OEData G p) (A B : S ⥤ S) (θ φ : MulAut G) :
    liftFunctorθ d A θ ⋙ liftFunctorθ d B φ = liftFunctorθ d (A ⋙ B) (φ * θ) := by
  have hcov : (liftFunctorθ d A θ ⋙ liftFunctorθ d B φ) ⋙ p = p ⋙ (A ⋙ B) := by
    rw [Functor.assoc, liftθ_covers, ← Functor.assoc, liftθ_covers, Functor.assoc]
  refine funct_ext d (fun x => ?_) (hcov.trans (liftθ_covers d (A ⋙ B) (φ * θ)).symm)
  simp only [Functor.comp_obj, liftFunctorθ, d.p_act, d.p_base, d.coord_base, MulAut.mul_apply]

/-- The twisted lift of the identity at the trivial twist is the identity. -/
theorem liftθ_id (d : OEData G p) : liftFunctorθ d (𝟭 S) (1 : MulAut G) = 𝟭 O := by
  rw [liftFunctorθ_one]; exact lift_id d

/-- Twisted equivariance is closed under composition; the twists multiply in `MulAut G`. -/
theorem isTwistedEquivariant_comp {F F' : O ⥤ O} {θ θ' : MulAut G}
    (h : IsTwistedEquivariant d θ F) (h' : IsTwistedEquivariant d θ' F') :
    IsTwistedEquivariant d (θ' * θ) (F ⋙ F') := fun x g => by
  show F'.obj (F.obj (d.act x g)) = d.act (F'.obj (F.obj x)) ((θ' * θ) g)
  rw [h x g, h' (F.obj x) (θ g), MulAut.mul_apply]

/-- Twisted equivariance transfers to a strict inverse, inverting the twist. -/
theorem isTwistedEquivariant_inv {F Finv : O ⥤ O} {θ : MulAut G}
    (hi : F ⋙ Finv = 𝟭 O) (ih : Finv ⋙ F = 𝟭 O) (h : IsTwistedEquivariant d θ F) :
    IsTwistedEquivariant d θ⁻¹ Finv := by
  have hθ : ∀ g, θ (θ⁻¹ g) = g := fun g => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hFcancel : ∀ z, F.obj (Finv.obj z) = z := fun z => by
    have := Functor.congr_obj ih z; simpa using this
  have hinj : Function.Injective F.obj := fun a b hab => by
    have e : ∀ z, Finv.obj (F.obj z) = z := fun z => by
      have := Functor.congr_obj hi z; simpa using this
    have := congrArg Finv.obj hab; rw [e, e] at this; exact this
  intro x g
  apply hinj
  rw [h (Finv.obj x) (θ⁻¹ g), hFcancel, hFcancel, hθ]

/-! ### The semidirect bundle-automorphism group  `Aut□^θ_G(O/p)`  and its exact sequence

  Fix a *functorial twist* `θ : StrictAut S →* MulAut G` — the physical action of base symmetries
  on the structure group (for Poincaré, `O(1,3) → MulAut ℝ⁴`, the defining representation).  A
  `θ`-twisted bundle automorphism covers a base symmetry `A` and is `θ A`-twisted equivariant.
  These assemble into a group `AutBoxGθ d θ`, and `Φθ`/`ΛHomθ` give the short exact sequence

        `1 → G → Aut□^θ_G(O/p) → Aut(S) → 1`.

  By `Λ_comp_liftθ` the conjugation action of this group on the kernel `G` is `θ`, so the extension
  is semidirect rather than direct — `G ⋊_θ Aut(S)` (e.g. `ℝ⁴ ⋊ O(1,3) = ISO(1,3)`), realized as an
  explicit `≃*` in §9 (`autBoxGθMulEquivSemidirect`); at `θ = 1` it is the direct product of §6.
  No new `OEData` assumption is used beyond §§1–6. -/

variable (θ : StrictAut S →* MulAut G)

/-- A `θ`-twisted bundle automorphism:  a strict autoequivalence `hom` of `O` that is
    `θ(base)`-twisted `G`-equivariant and cleavage-preserving over the strict base
    automorphism `base`.  Forms `Aut□^θ_G(O/p)`. -/
@[ext]
structure AutBoxGθ (d : OEData G p) (θ : StrictAut S →* MulAut G) where
  hom : O ⥤ O
  inv : O ⥤ O
  hom_inv_id : hom ⋙ inv = 𝟭 O
  inv_hom_id : inv ⋙ hom = 𝟭 O
  base : StrictAut S
  equiv : IsTwistedEquivariant d (θ base) hom
  pres : PreservesCleavage d hom base.hom

namespace AutBoxGθ

instance : Group (AutBoxGθ d θ) where
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
      equiv := by
        rw [map_mul]; exact isTwistedEquivariant_comp d e₂.equiv e₁.equiv
      pres := preservesCleavage_comp d e₂.pres e₁.pres }
  one := ⟨𝟭 O, 𝟭 O, rfl, rfl, 1, by rw [map_one]; exact id_isGEquivariant d,
    id_preservesCleavage d⟩
  inv e :=
    { hom := e.inv
      inv := e.hom
      hom_inv_id := e.inv_hom_id
      inv_hom_id := e.hom_inv_id
      base := e.base⁻¹
      equiv := by
        rw [map_inv]; exact isTwistedEquivariant_inv d e.hom_inv_id e.inv_hom_id e.equiv
      pres := preservesCleavage_inv d e.hom_inv_id e.inv_hom_id e.pres }
  mul_assoc a b c := by refine AutBoxGθ.ext ?_ ?_ ?_ <;> rfl
  one_mul a := by refine AutBoxGθ.ext ?_ ?_ ?_ <;> rfl
  mul_one a := by refine AutBoxGθ.ext ?_ ?_ ?_ <;> rfl
  inv_mul_cancel a := by
    refine AutBoxGθ.ext ?_ ?_ ?_ <;> first | exact a.hom_inv_id | exact inv_mul_cancel _

@[simp] lemma mul_hom (e₁ e₂ : AutBoxGθ d θ) : (e₁ * e₂).hom = e₂.hom ⋙ e₁.hom := rfl
@[simp] lemma mul_base (e₁ e₂ : AutBoxGθ d θ) : (e₁ * e₂).base = e₁.base * e₂.base := rfl
@[simp] lemma one_hom : (1 : AutBoxGθ d θ).hom = 𝟭 O := rfl
@[simp] lemma one_base : (1 : AutBoxGθ d θ).base = 1 := rfl

end AutBoxGθ

/-- `Φθ : Aut□^θ_G(O/p) →* Aut(S)`:  the base symmetry covered by a twisted bundle automorphism. -/
def Φθ (d : OEData G p) (θ : StrictAut S →* MulAut G) : AutBoxGθ d θ →* StrictAut S where
  toFun e := e.base
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `Λθ : G →* Aut□^θ_G(O/p)`:  the normalized fiber-translation embedding (base `1`, twist `1`). -/
noncomputable def ΛHomθ (d : OEData G p) (θ : StrictAut S →* MulAut G) : G →* AutBoxGθ d θ where
  toFun g :=
    { hom := Λ d g
      inv := Λ d g⁻¹
      hom_inv_id := by rw [Λ_comp, inv_mul_cancel, Λ_one]
      inv_hom_id := by rw [Λ_comp, mul_inv_cancel, Λ_one]
      base := 1
      equiv := by rw [map_one]; exact Λ_isGEquivariant d g
      pres := Λ_preservesCleavage d g }
  map_one' := by
    refine AutBoxGθ.ext ?_ ?_ ?_
    · exact Λ_one d
    · show Λ d (1 : G)⁻¹ = 𝟭 O; rw [inv_one, Λ_one]
    · rfl
  map_mul' g h := by
    refine AutBoxGθ.ext ?_ ?_ ?_
    · show Λ d (g * h) = Λ d h ⋙ Λ d g; rw [Λ_comp]
    · show Λ d (g * h)⁻¹ = Λ d g⁻¹ ⋙ Λ d h⁻¹; rw [Λ_comp, mul_inv_rev]
    · rfl

/-- `Φθ` is surjective:  every base symmetry is covered by its `θ`-twisted strict lift. -/
theorem Φθ_surjective (d : OEData G p) (θ : StrictAut S →* MulAut G) :
    Function.Surjective (Φθ d θ) := fun A =>
  ⟨{ hom := liftFunctorθ d A.hom (θ A)
     inv := liftFunctorθ d A.inv (θ A)⁻¹
     hom_inv_id := by rw [liftθ_comp, inv_mul_cancel, A.hom_inv_id, liftθ_id]
     inv_hom_id := by rw [liftθ_comp, mul_inv_cancel, A.inv_hom_id, liftθ_id]
     base := A
     equiv := liftθ_isTwistedEquivariant d A.hom (θ A)
     pres := liftθ_preservesCleavage d A.hom (θ A) }, rfl⟩

/-- `Λθ` is injective (needs a basepoint; freeness of the action does the rest). -/
theorem ΛHomθ_injective (d : OEData G p) (θ : StrictAut S →* MulAut G) [Nonempty S] :
    Function.Injective (ΛHomθ d θ) := by
  intro g h hgh
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hev : (Λ d g).obj (d.base s₀) = (Λ d h).obj (d.base s₀) :=
    congrArg (·.obj (d.base s₀)) (congrArg AutBoxGθ.hom hgh)
  have hc : d.coord (d.base s₀) = 1 := by
    have h1 := d.coord_base s₀ 1; rwa [d.act_one] at h1
  simp only [Λ, d.p_base, hc, mul_one] at hev
  exact d.act_free _ _ _ hev

/-- Exactness at the middle:  `ker Φθ = range Λθ`.  A twisted bundle automorphism covers `id_S`
    (twist `θ 1 = 1`, so it is strictly equivariant) iff it is a normalized fiber translation.
    With `Φθ_surjective` and `ΛHomθ_injective` this is the SEMIDIRECT exact sequence
    `1 → G →[Λθ] Aut□^θ_G(O/p) →[Φθ] Aut(S) → 1`. -/
theorem ker_Φθ_eq_range_Λθ (d : OEData G p) (θ : StrictAut S →* MulAut G) [IsConnected S] :
    (Φθ d θ).ker = (ΛHomθ d θ).range := by
  ext e
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro he
    have hb : e.base = 1 := he
    have hgeq : IsGEquivariant d e.hom := by
      have h := e.equiv; rw [hb, map_one] at h; exact h
    have hpc : PreservesCleavage d e.hom (𝟭 S) := by
      have hp := e.pres; rw [hb] at hp; exact hp
    obtain ⟨g, hg⟩ := ((exact_sequence d).2 e.hom hgeq).1 hpc
    refine ⟨g, AutBoxGθ.ext hg.symm ?_ hb.symm⟩
    show Λ d g⁻¹ = e.inv
    have key : e.hom ⋙ Λ d g⁻¹ = 𝟭 O := by rw [hg, Λ_comp, inv_mul_cancel, Λ_one]
    calc Λ d g⁻¹ = (e.inv ⋙ e.hom) ⋙ Λ d g⁻¹ := by rw [e.inv_hom_id, Functor.id_comp]
      _ = e.inv ⋙ e.hom ⋙ Λ d g⁻¹ := rfl
      _ = e.inv := by rw [key, Functor.comp_id]
  · rintro ⟨g, rfl⟩
    rfl


/-! ## 8. A non-vacuous NONTRIVIAL-twist witness  (§7 is not vacuous for `θ ≠ 1`)

  We exhibit a concrete `OEData G p` together with a NONTRIVIAL functorial twist
  `θ : StrictAut S →* MulAut G`, so the semidirect theory of §7 is non-vacuous beyond `θ = 1`.

  The base is `S = SingleObj Q`, whose strict autoequivalences are `MulAut Q` (so taking
  `Q = G` gives the twist `θ : StrictAut S ≅ MulAut G`, the identity — nontrivial whenever `G`
  has a nontrivial automorphism, e.g. `Multiplicative (ZMod 3)`).

  The total groupoid is the `Q`-LABELLED codiscrete groupoid on `G` (`Lab G Q`): objects are
  `G`, every hom-set is `Q`, and `p` reads off the label.  Crucially the label is INDEPENDENT of
  the endpoints, so the structure-group action can leave it fixed (`actHom f g = f`) and the
  chosen vertical translation `ltrans` can be labelled `1` — genuinely vertical, as the current
  `OEData` requires.  (The naive `Codisc G` with `p(a⟶b) = b·a⁻¹` would force `ltrans` to project
  to a nonidentity, violating `p_ltrans`.) -/

/-- The `Q`-labelled codiscrete groupoid on objects `B`: `Hom x y := Q`, composing by flipped
    multiplication (matching `SingleObj Q`), so `pLab` below is a functor. -/
@[ext] structure Lab (B Q : Type*) where pt : B

instance (B Q : Type*) [Group Q] : Groupoid (Lab B Q) where
  Hom _ _ := Q
  id _ := 1
  comp f g := g * f
  id_comp _ := mul_one _
  comp_id _ := one_mul _
  assoc f g h := (mul_assoc h g f).symm
  inv f := f⁻¹
  inv_comp _ := mul_inv_cancel _
  comp_inv _ := inv_mul_cancel _

/-- The projection `Lab B Q ⥤ SingleObj Q` reading off the `Q`-label (faithful and full). -/
def pLab (B Q : Type*) [Group Q] : Lab B Q ⥤ SingleObj Q where
  obj _ := SingleObj.star Q
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The non-vacuous twist witness as an `OEData`: structure group `G` acts on objects by right
    multiplication, leaving the `Q`-label fixed; basepoint `⟨1⟩`, `coord = pt`; the chosen
    cleavage is the identity reindexing with `chi` the label `u`, and `ltrans` the label `1`
    (vertical). -/
def labData (G Q : Type*) [Group G] [Group Q] : OEData G (pLab G Q) where
  act x g := ⟨x.pt * g⟩
  act_one x := by simp
  act_mul x g h := by simp [mul_assoc]
  p_act _ _ := rfl
  act_free x g h e := mul_left_cancel (congrArg Lab.pt e)
  actHom f _ := f
  actHom_id _ _ := rfl
  actHom_comp _ _ _ := rfl
  p_actHom _ _ := by simp [pLab]
  base _ := ⟨1⟩
  p_base _ := rfl
  coord x := x.pt
  base_coord x := by simp
  coord_base _ g := by simp
  reind _ y _ := y
  p_reind _ _ _ := rfl
  chi u _ _ := u
  p_chi := fun {s t} u y hy => by
    obtain rfl : s = SingleObj.star Q := rfl
    obtain rfl : t = SingleObj.star Q := rfl
    simp [pLab]
  reind_base _ := rfl
  reind_act _ _ _ _ := rfl
  chi_act _ _ _ _ := by simp
  ltrans _ _ := 1
  p_ltrans _ _ := by aesop_cat
  reind_id _ _ := rfl
  chi_id _ _ := by aesop_cat
  reind_comp _ _ _ _ := rfl
  chi_comp _ _ _ _ := by aesop_cat
  p_faithful := ⟨fun h => h⟩

/-- Reading a strict autoequivalence of `SingleObj G` as a group automorphism of `G` (its
    underlying monoid hom, via `SingleObj.mapHom`).  This realizes `StrictAut (SingleObj G) ≅
    MulAut G`. -/
def toMulAutSingleObj (G : Type*) [Group G] (e : StrictAut (SingleObj G)) : MulAut G where
  toFun := (SingleObj.mapHom G G).symm e.hom
  invFun := (SingleObj.mapHom G G).symm e.inv
  left_inv g := by
    have h : ((SingleObj.mapHom G G).symm e.inv).comp ((SingleObj.mapHom G G).symm e.hom)
        = MonoidHom.id G := by
      apply (SingleObj.mapHom G G).injective
      rw [SingleObj.mapHom_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, e.hom_inv_id,
          SingleObj.mapHom_id]
    exact DFunLike.congr_fun h g
  right_inv g := by
    have h : ((SingleObj.mapHom G G).symm e.hom).comp ((SingleObj.mapHom G G).symm e.inv)
        = MonoidHom.id G := by
      apply (SingleObj.mapHom G G).injective
      rw [SingleObj.mapHom_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, e.inv_hom_id,
          SingleObj.mapHom_id]
    exact DFunLike.congr_fun h g
  map_mul' := ((SingleObj.mapHom G G).symm e.hom).map_mul

/-- The functorial twist `θ : StrictAut (SingleObj G) →* MulAut G`, the identity under the
    equivalence `StrictAut (SingleObj G) ≅ MulAut G`. -/
def θSingleObj (G : Type*) [Group G] : StrictAut (SingleObj G) →* MulAut G where
  toFun := toMulAutSingleObj G
  map_one' := by
    ext g
    show ((SingleObj.mapHom G G).symm (𝟭 (SingleObj G))) g = g
    rw [← SingleObj.mapHom_id, Equiv.symm_apply_apply]; rfl
  map_mul' e₁ e₂ := by
    have key : (SingleObj.mapHom G G).symm (e₂.hom ⋙ e₁.hom)
        = ((SingleObj.mapHom G G).symm e₁.hom).comp ((SingleObj.mapHom G G).symm e₂.hom) := by
      apply (SingleObj.mapHom G G).injective
      rw [SingleObj.mapHom_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
          Equiv.apply_symm_apply]
    ext g
    show ((SingleObj.mapHom G G).symm (e₂.hom ⋙ e₁.hom)) g = _
    rw [key]; rfl

/-- `θSingleObj` is surjective:  every group automorphism of `G` is realized by a strict
    autoequivalence of `SingleObj G` (so `θSingleObj` is the iso `StrictAut (SingleObj G) ≅
    MulAut G`). -/
theorem θSingleObj_surjective (G : Type*) [Group G] : Function.Surjective (θSingleObj G) := by
  intro φ
  have hi : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by
    ext g; exact φ.symm_apply_apply g
  have hi' : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G := by
    ext g; exact φ.apply_symm_apply g
  refine ⟨{ hom := SingleObj.mapHom G G φ.toMonoidHom
            inv := SingleObj.mapHom G G φ.symm.toMonoidHom
            hom_inv_id := by rw [← SingleObj.mapHom_comp, hi, SingleObj.mapHom_id]
            inv_hom_id := by rw [← SingleObj.mapHom_comp, hi', SingleObj.mapHom_id] }, ?_⟩
  ext g
  show ((SingleObj.mapHom G G).symm (SingleObj.mapHom G G φ.toMonoidHom)) g = φ g
  rw [Equiv.symm_apply_apply]; rfl

/-- Hence the twist is NONTRIVIAL whenever `G` has a nontrivial automorphism (e.g.
    `Multiplicative (ZMod 3)`), so §7 is genuinely used beyond `θ = 1`. -/
theorem θSingleObj_ne_one (G : Type*) [Group G] [Nontrivial (MulAut G)] :
    θSingleObj G ≠ 1 := by
  obtain ⟨φ, hφ⟩ := exists_ne (1 : MulAut G)
  obtain ⟨e, he⟩ := θSingleObj_surjective G φ
  intro h
  exact hφ (by rw [← he, h, MonoidHom.one_apply])

/-- The semidirect exact sequence of §7, applied to the labelled witness with the nontrivial
    twist `θSingleObj`:  `ker Φθ = range Λθ` for `OEData G (pLab G G)`.  Together with
    `θSingleObj_ne_one` this shows the twisted (semidirect) theory is non-vacuous for `θ ≠ 1`. -/
example (G : Type*) [Group G] :
    (Φθ (labData G G) (θSingleObj G)).ker = (ΛHomθ (labData G G) (θSingleObj G)).range :=
  ker_Φθ_eq_range_Λθ (labData G G) (θSingleObj G)


/-! ## 9. The bundle-automorphism group as an explicit semidirect product

  Upgrades the §7 exact sequence to a literal group isomorphism

      `Aut□^θ_G(O/p)  ≃*  G ⋊[θ] Aut(S)`   (mathlib's `SemidirectProduct`).

  The map `G ⋊[θ] Aut(S) → Aut□^θ_G` is `SemidirectProduct.lift` of the fiber-translation
  embedding `Λθ` and the twisted-lift section `liftHomθ`, whose compatibility is exactly the
  conjugation law `Λ_comp_liftθ`.  Bijectivity is the exactness `ker_Φθ_eq_range_Λθ` together with
  `ΛHomθ_injective`.  Needs `[IsConnected S]`. -/

/-- The twisted-lift section as a group homomorphism `Aut(S) →* Aut□^θ_G(O/p)`:
    `A ↦ liftFunctorθ d A.hom (θ A)`, the canonical `θ_A`-twisted cleavage-preserving lift. -/
noncomputable def liftHomθ (d : OEData G p) (θ : StrictAut S →* MulAut G) :
    StrictAut S →* AutBoxGθ d θ where
  toFun A :=
    { hom := liftFunctorθ d A.hom (θ A)
      inv := liftFunctorθ d A.inv (θ A)⁻¹
      hom_inv_id := by rw [liftθ_comp, inv_mul_cancel, A.hom_inv_id, liftθ_id]
      inv_hom_id := by rw [liftθ_comp, mul_inv_cancel, A.inv_hom_id, liftθ_id]
      base := A
      equiv := liftθ_isTwistedEquivariant d A.hom (θ A)
      pres := liftθ_preservesCleavage d A.hom (θ A) }
  map_one' := by
    refine AutBoxGθ.ext ?_ ?_ ?_
    · show liftFunctorθ d (𝟭 S) (θ 1) = 𝟭 O
      rw [map_one]; exact liftθ_id d
    · show liftFunctorθ d (𝟭 S) (θ 1)⁻¹ = 𝟭 O
      rw [map_one, inv_one]; exact liftθ_id d
    · rfl
  map_mul' A B := by
    refine AutBoxGθ.ext ?_ ?_ ?_
    · show liftFunctorθ d (B.hom ⋙ A.hom) (θ (A * B))
          = liftFunctorθ d B.hom (θ B) ⋙ liftFunctorθ d A.hom (θ A)
      rw [liftθ_comp, map_mul]
    · show liftFunctorθ d (A.inv ⋙ B.inv) (θ (A * B))⁻¹
          = liftFunctorθ d A.inv (θ A)⁻¹ ⋙ liftFunctorθ d B.inv (θ B)⁻¹
      rw [liftθ_comp, map_mul, mul_inv_rev]
    · rfl

@[simp] theorem liftHomθ_base (d : OEData G p) (θ : StrictAut S →* MulAut G) (A : StrictAut S) :
    (liftHomθ d θ A).base = A := rfl

@[simp] theorem Φθ_apply (d : OEData G p) (θ : StrictAut S →* MulAut G) (e : AutBoxGθ d θ) :
    Φθ d θ e = e.base := rfl

@[simp] theorem ΛHomθ_base (d : OEData G p) (θ : StrictAut S →* MulAut G) (g : G) :
    (ΛHomθ d θ g).base = 1 := rfl

@[simp] theorem AutBoxGθ_inv_base (d : OEData G p) (θ : StrictAut S →* MulAut G)
    (e : AutBoxGθ d θ) : (e⁻¹).base = e.base⁻¹ := rfl

/-- The compatibility condition for `SemidirectProduct.lift`:  conjugating `Λθ g` by the lift of
    `A` twists `g` by `θ A` (this is `Λ_comp_liftθ` at the group level). -/
theorem liftHomθ_conj (d : OEData G p) (θ : StrictAut S →* MulAut G) (A : StrictAut S) :
    (ΛHomθ d θ).comp (θ A).toMonoidHom
      = (MulAut.conj (liftHomθ d θ A)).toMonoidHom.comp (ΛHomθ d θ) := by
  refine MonoidHom.ext fun g => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine AutBoxGθ.ext ?_ ?_ ?_
  · show Λ d ((θ A) g)
        = liftFunctorθ d A.inv (θ A)⁻¹ ⋙ Λ d g ⋙ liftFunctorθ d A.hom (θ A)
    rw [Λ_comp_liftθ, ← Functor.assoc, liftθ_comp, A.inv_hom_id, mul_inv_cancel, liftθ_id,
      Functor.id_comp]
  · show Λ d ((θ A) g)⁻¹
        = liftFunctorθ d A.inv (θ A)⁻¹ ⋙ Λ d g⁻¹ ⋙ liftFunctorθ d A.hom (θ A)
    rw [Λ_comp_liftθ, ← Functor.assoc, liftθ_comp, A.inv_hom_id, mul_inv_cancel, liftθ_id,
      Functor.id_comp, map_inv]
  · simp

/-- `G ⋊[θ] Aut(S) →* Aut□^θ_G(O/p)`:  `inl g ↦ Λθ g`, `inr A ↦ liftHomθ A`. -/
noncomputable def semidirectToAutBoxGθ (d : OEData G p) (θ : StrictAut S →* MulAut G) :
    SemidirectProduct G (StrictAut S) θ →* AutBoxGθ d θ :=
  SemidirectProduct.lift (ΛHomθ d θ) (liftHomθ d θ) (liftHomθ_conj d θ)

@[simp] theorem semidirectToAutBoxGθ_inl (d : OEData G p) (θ : StrictAut S →* MulAut G) (g : G) :
    semidirectToAutBoxGθ d θ (SemidirectProduct.inl g) = ΛHomθ d θ g :=
  SemidirectProduct.lift_inl _ _ _ g

@[simp] theorem semidirectToAutBoxGθ_inr (d : OEData G p) (θ : StrictAut S →* MulAut G)
    (A : StrictAut S) :
    semidirectToAutBoxGθ d θ (SemidirectProduct.inr A) = liftHomθ d θ A :=
  SemidirectProduct.lift_inr _ _ _ A

/-- The §7 semidirect exact sequence, packaged as an explicit group isomorphism
    `Aut□^θ_G(O/p) ≃* G ⋊[θ] Aut(S)`. -/
noncomputable def autBoxGθMulEquivSemidirect (d : OEData G p) (θ : StrictAut S →* MulAut G)
    [IsConnected S] : AutBoxGθ d θ ≃* SemidirectProduct G (StrictAut S) θ := by
  have hinj : Function.Injective (semidirectToAutBoxGθ d θ) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul,
      semidirectToAutBoxGθ_inl, semidirectToAutBoxGθ_inr] at hx
    have hright : x.right = 1 := by
      have h2 := congrArg (Φθ d θ) hx
      rw [map_mul, map_one] at h2
      simpa using h2
    rw [hright, map_one, mul_one] at hx
    have hleft : x.left = 1 := ΛHomθ_injective d θ (by rw [hx, map_one])
    exact SemidirectProduct.ext hleft hright
  have hsurj : Function.Surjective (semidirectToAutBoxGθ d θ) := by
    intro e
    have hker : e * (liftHomθ d θ e.base)⁻¹ ∈ (Φθ d θ).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      simp
    rw [ker_Φθ_eq_range_Λθ, MonoidHom.mem_range] at hker
    obtain ⟨g, hg⟩ := hker
    refine ⟨SemidirectProduct.inl g * SemidirectProduct.inr e.base, ?_⟩
    rw [map_mul, semidirectToAutBoxGθ_inl, semidirectToAutBoxGθ_inr, hg, inv_mul_cancel_right]
  exact (MulEquiv.ofBijective (semidirectToAutBoxGθ d θ) ⟨hinj, hsurj⟩).symm

/-- Non-vacuity of the semidirect packaging:  applied to the §8 nontrivial-twist witness it gives
    `Aut□^θ_G(O/pLab) ≃* G ⋊[θSingleObj] Aut(SingleObj G)` — a genuine (nontrivial-`θ`) semidirect
    product, the abstract shape of `ℝ⁴ ⋊ O(1,3)`. -/
noncomputable example (G : Type*) [Group G] :
    AutBoxGθ (labData G G) (θSingleObj G)
      ≃* SemidirectProduct G (StrictAut (SingleObj G)) (θSingleObj G) :=
  autBoxGθMulEquivSemidirect (labData G G) (θSingleObj G)

