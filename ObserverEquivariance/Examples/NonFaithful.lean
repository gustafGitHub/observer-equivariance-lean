import ObserverEquivariance.Core

/-!
# Dropping faithfulness: additional vertical isotropy (paper `ex:nonfaithful`)

Paper labels covered: `ex:nonfaithful` (and, for the conditions checked, `def:data` (N1)–(N6)
and `def:lifts`; the conclusion is about the kernel statement of `thm:strict`).

The example: the presentation group is trivial, `G = PUnit`; the base is terminal,
`S = Discrete PUnit`; the total category is `O = SingleObj K = BK` for a group `K`
(the *isotropy* group, kept distinct from `G` throughout); `p` is the unique functor.

* `nonfaithfulPreDatum K : NormalizedPreDatum PUnit (nonfaithfulProj K)` — the unique
  basepoint and coordinate, identity chosen transport, identity `ℓ`-arrows.  A bare
  `NormalizedPreDatum` does NOT contain the invertibility part of (N5), so this is proven
  separately (`nonfaithfulPreDatum_ltrans_isIso`); together these are the paper's (N1)–(N5).
* `nonfaithfulProj_not_faithful` — for nontrivial `K`, (N6) fails; hence
  `nonfaithful_isEmpty_OEData`: the example is NOT an `OEData` (that structure contains (N6)),
  for any presentation group whatsoever.
* `IsNonfaithfulLift K F` — the lift conditions over the identity of the base, for the chosen
  data of this example: covering (`eq:cover`), equivariance on objects (`eq:equiv`) and on arrows,
  preservation of the chosen transport on objects (`eq:preserve`) AND on the chosen `χ`-arrows,
  and preservation of the chosen `ℓ`-arrows.  Because `p` is not faithful, the arrow-level
  conditions are not implied by the object-level ones in general, so they are imposed explicitly.
* `nonfaithfulLiftKernel K` — the subgroup of `StrictAut (SingleObj K)` cut out by these
  conditions; `nonfaithfulLiftKernel_eq_top` (every strict automorphism qualifies) and
  `nonfaithfulLiftKernelEquiv K : nonfaithfulLiftKernel K ≃* MulAut K` (via `θSingleObjEquiv`).
  Since `StrictAut (Discrete PUnit)` is trivial (`strictAut_discretePUnit_eq_one`), this is the
  whole kernel of the projection to base automorphisms.
* `IsNonfaithfulObjLift K F` / `nonfaithfulObjLiftKernel K` — only the object-level conditions of
  `def:lifts`; `nonfaithfulObjLiftKernel_eq_nonfaithfulLiftKernel` shows this kernel is the same
  (`⊤`, `≃* MulAut K`), so the arrow-level conditions are not essential here.
* For `K = G3 = Multiplicative (ZMod 3)`: `nonfaithfulLiftKernelZMod3Equiv : … ≃* Multiplicative
  (ZMod 2)`, and `nonfaithful_kernel_not_presentationGroup`: the kernel is nontrivial and not
  isomorphic to the (trivial) presentation group, so the kernel conclusion of `thm:strict`
  genuinely needs (N6).
-/

open CategoryTheory

universe u

/-! ## 1. The projection and the pre-datum -/

section Datum

variable (K : Type u) [Group K]

/-- The unique functor `p : BK ⥤ *` from `SingleObj K` to the terminal category
    `Discrete PUnit` (paper `ex:nonfaithful`). -/
def nonfaithfulProj : SingleObj K ⥤ Discrete PUnit.{1} where
  obj _ := ⟨PUnit.unit⟩
  map _ := 𝟙 _

namespace NonFaithful

omit [Group K] in
/-- `SingleObj K` has exactly one object (helper for paper `ex:nonfaithful`). -/
theorem obj_eq (x y : SingleObj K) : x = y := rfl

/-- Every `eqToHom` in `SingleObj K` is the identity element `1 : K`
    (helper for paper `ex:nonfaithful`). -/
theorem eqToHom_eq_one {x y : SingleObj K} (h : x = y) : (eqToHom h : x ⟶ y) = (1 : K) := by
  subst h
  rw [eqToHom_refl, SingleObj.id_as_one]

end NonFaithful

/-- The normalized pre-datum of paper `ex:nonfaithful`: trivial presentation group `G = PUnit`,
    unique basepoint `b_* = ⋆` and coordinate `g_⋆ = 1`, trivial action, identity chosen
    transport (`u^* y = y`, `χ_{u,y} = 𝟙 y`) and identity `ℓ`-arrows.  These are the data and
    laws of (N1)–(N4) and the vertical-arrow part of (N5); the invertibility part of (N5) is
    `nonfaithfulPreDatum_ltrans_isIso`. -/
def nonfaithfulPreDatum : NormalizedPreDatum PUnit.{1} (nonfaithfulProj K) where
  act x _ := x
  act_one _ := rfl
  act_mul _ _ _ := rfl
  p_act _ _ := rfl
  act_free _ _ _ _ := rfl
  actHom f _ := f
  actHom_id _ _ := rfl
  actHom_comp _ _ _ := rfl
  actHom_one f := by
    simp only [NonFaithful.eqToHom_eq_one, SingleObj.comp_as_mul, mul_one, one_mul]
  actHom_mul f _ _ := by
    simp only [NonFaithful.eqToHom_eq_one, SingleObj.comp_as_mul, mul_one, one_mul]
  p_actHom _ _ := Subsingleton.elim _ _
  base _ := SingleObj.star K
  p_base _ := Subsingleton.elim _ _
  coord _ := 1
  base_coord _ := rfl
  coord_base _ _ := rfl
  reind _ y _ := y
  p_reind _ _ _ := Subsingleton.elim _ _
  chi _ y _ := 𝟙 y
  p_chi _ _ _ := Subsingleton.elim _ _
  reind_base _ := rfl
  reind_act _ _ _ _ := rfl
  chi_act _ _ _ _ := by
    simp only [NonFaithful.eqToHom_eq_one, SingleObj.comp_as_mul, mul_one]
  ltrans _ x := 𝟙 x
  p_ltrans _ _ := Subsingleton.elim _ _
  reind_id _ _ := rfl
  chi_id _ _ := by
    simp only [NonFaithful.eqToHom_eq_one, SingleObj.id_as_one]
  reind_comp _ _ _ _ := rfl
  chi_comp _ _ _ _ := by
    simp only [NonFaithful.eqToHom_eq_one, SingleObj.comp_as_mul, SingleObj.id_as_one, mul_one]

/-- The chosen `ℓ`-arrows of the pre-datum of paper `ex:nonfaithful` are isomorphisms: the
    invertibility part of (N5), which is not a field of `NormalizedPreDatum` and so is
    proven separately.  With `nonfaithfulPreDatum` this gives all of (N1)–(N5). -/
instance nonfaithfulPreDatum_ltrans_isIso (g : PUnit.{1}) (x : SingleObj K) :
    IsIso ((nonfaithfulPreDatum K).ltrans g x) :=
  show IsIso (𝟙 x) from inferInstance

/-- Failure of (N6) in paper `ex:nonfaithful`: for nontrivial `K` the projection `BK ⥤ *` is
    not faithful (every `k : ⋆ ⟶ ⋆` has the same image). -/
theorem nonfaithfulProj_not_faithful [Nontrivial K] : ¬ (nonfaithfulProj K).Faithful := by
  intro hF
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  apply hk
  have h : (nonfaithfulProj K).map (k : SingleObj.star K ⟶ SingleObj.star K)
      = (nonfaithfulProj K).map (1 : SingleObj.star K ⟶ SingleObj.star K) :=
    Subsingleton.elim _ _
  exact (nonfaithfulProj K).map_injective h

/-- Paper `ex:nonfaithful`, bundled: this theorem records the invertibility part of (N5) (every
    chosen `ℓ`-arrow is an isomorphism) and, for nontrivial `K`, the failure of (N6).  The data
    and laws of (N1)–(N4) and the verticality of the `ℓ`-arrows are NOT part of this statement:
    they are witnessed by the fields of the definition `nonfaithfulPreDatum K`. -/
theorem nonfaithful_N1_N5_and_not_N6 [Nontrivial K] :
    (∀ (g : PUnit.{1}) (x : SingleObj K), IsIso ((nonfaithfulPreDatum K).ltrans g x)) ∧
      ¬ (nonfaithfulProj K).Faithful :=
  ⟨fun g x => nonfaithfulPreDatum_ltrans_isIso K g x, nonfaithfulProj_not_faithful K⟩

/-- Paper `ex:nonfaithful`: for nontrivial `K` the example cannot be an `OEData` — that
    structure contains faithfulness (N6) as the field `p_faithful` — for ANY presentation
    group `G`, in particular not for `G = PUnit`. -/
theorem nonfaithful_isEmpty_OEData [Nontrivial K] (G : Type*) [Group G] :
    IsEmpty (OEData G (nonfaithfulProj K)) :=
  ⟨fun d => nonfaithfulProj_not_faithful K d.p_faithful⟩

/-! ### Field lemmas (all `rfl`) -/

/-- The action of the trivial presentation group is trivial (paper `ex:nonfaithful`). -/
@[simp] theorem nonfaithfulPreDatum_act (x : SingleObj K) (g : PUnit.{1}) :
    (nonfaithfulPreDatum K).act x g = x := rfl

/-- The arrow action is trivial (paper `ex:nonfaithful`). -/
@[simp] theorem nonfaithfulPreDatum_actHom {x y : SingleObj K} (f : x ⟶ y) (g : PUnit.{1}) :
    (nonfaithfulPreDatum K).actHom f g = f := rfl

/-- The unique basepoint (paper `ex:nonfaithful`). -/
@[simp] theorem nonfaithfulPreDatum_base (s : Discrete PUnit.{1}) :
    (nonfaithfulPreDatum K).base s = SingleObj.star K := rfl

/-- The unique coordinate (paper `ex:nonfaithful`). -/
@[simp] theorem nonfaithfulPreDatum_coord (x : SingleObj K) :
    (nonfaithfulPreDatum K).coord x = 1 := rfl

/-- Identity chosen transport on objects (paper `ex:nonfaithful`). -/
@[simp] theorem nonfaithfulPreDatum_reind {s t : Discrete PUnit.{1}} (u : s ⟶ t)
    (y : SingleObj K) (hy : (nonfaithfulProj K).obj y = t) :
    (nonfaithfulPreDatum K).reind u y hy = y := rfl

/-- Identity chosen `χ`-arrows (paper `ex:nonfaithful`). -/
@[simp] theorem nonfaithfulPreDatum_chi {s t : Discrete PUnit.{1}} (u : s ⟶ t)
    (y : SingleObj K) (hy : (nonfaithfulProj K).obj y = t) :
    (nonfaithfulPreDatum K).chi u y hy = 𝟙 y := rfl

/-- Identity chosen `ℓ`-arrows (paper `ex:nonfaithful`). -/
@[simp] theorem nonfaithfulPreDatum_ltrans (g : PUnit.{1}) (x : SingleObj K) :
    (nonfaithfulPreDatum K).ltrans g x = 𝟙 x := rfl

end Datum

/-! ## 2. The lift kernel is `Aut(K)` -/

section Kernel

variable (K : Type u) [Group K]

/-- The lift conditions of paper `def:lifts` over the identity base automorphism, for the
    chosen data of paper `ex:nonfaithful`, stated at object AND arrow level (since `p` is not
    faithful, the arrow equations do not follow from the object equations in general):
    * `covers`: `pF = 𝟭 ∘ p` (`eq:cover` with `A = 𝟭`);
    * `equiv`: `F(x·g) = F(x)·g` (`eq:equiv`), and `equiv_map`: `F(f·g) = F(f)·g` with the casts;
    * `src`: `F(u^* y) = (𝟭 u)^* F(y)` (`eq:preserve`), with the same cast proof as Core's
      `PreservesCleavage.src`;
    * `map_chi`: `F(χ_{u,y}) = χ_{𝟭 u, F y}` after the `src` cast (chosen `χ`-arrows to chosen
      `χ`-arrows);
    * `map_ltrans`: `F(ℓ_{g,x}) = ℓ_{g,F x}` up to the (here trivial) object cast (chosen
      `ℓ`-arrows to chosen `ℓ`-arrows). -/
structure IsNonfaithfulLift (F : SingleObj K ⥤ SingleObj K) : Prop where
  covers : F ⋙ nonfaithfulProj K = nonfaithfulProj K ⋙ 𝟭 (Discrete PUnit.{1})
  equiv : ∀ (x : SingleObj K) (g : PUnit.{1}),
    F.obj ((nonfaithfulPreDatum K).act x g) = (nonfaithfulPreDatum K).act (F.obj x) g
  equiv_map : ∀ {x y : SingleObj K} (f : x ⟶ y) (g : PUnit.{1}),
    F.map ((nonfaithfulPreDatum K).actHom f g)
      = eqToHom (equiv x g) ≫ (nonfaithfulPreDatum K).actHom (F.map f) g ≫
          eqToHom (equiv y g).symm
  src : ∀ {s t : Discrete PUnit.{1}} (u : s ⟶ t) (y : SingleObj K)
      (hy : (nonfaithfulProj K).obj y = t),
    F.obj ((nonfaithfulPreDatum K).reind u y hy)
      = (nonfaithfulPreDatum K).reind ((𝟭 (Discrete PUnit.{1})).map u) (F.obj y)
          ((Functor.congr_obj covers y).trans (congrArg (𝟭 (Discrete PUnit.{1})).obj hy))
  map_chi : ∀ {s t : Discrete PUnit.{1}} (u : s ⟶ t) (y : SingleObj K)
      (hy : (nonfaithfulProj K).obj y = t),
    F.map ((nonfaithfulPreDatum K).chi u y hy)
      = eqToHom (src u y hy) ≫
          (nonfaithfulPreDatum K).chi ((𝟭 (Discrete PUnit.{1})).map u) (F.obj y)
            ((Functor.congr_obj covers y).trans (congrArg (𝟭 (Discrete PUnit.{1})).obj hy))
  map_ltrans : ∀ (g : PUnit.{1}) (x : SingleObj K),
    F.map ((nonfaithfulPreDatum K).ltrans g x)
      = (nonfaithfulPreDatum K).ltrans g (F.obj x) ≫ eqToHom (NonFaithful.obj_eq K _ _)

/-- Paper `ex:nonfaithful`: EVERY endofunctor of `BK` covers the identity and preserves all
    the chosen data (on objects and on arrows). -/
theorem isNonfaithfulLift_of_functor (F : SingleObj K ⥤ SingleObj K) : IsNonfaithfulLift K F where
  covers := CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)
  equiv _ _ := rfl
  equiv_map f _ := by
    show F.map f = eqToHom _ ≫ F.map f ≫ eqToHom _
    simp only [NonFaithful.eqToHom_eq_one, SingleObj.comp_as_mul, mul_one, one_mul]
  src _ _ _ := rfl
  map_chi _ y _ := by
    rw [NonFaithful.eqToHom_eq_one]
    exact (F.map_id y).trans (mul_one (1 : K)).symm
  map_ltrans _ x := by
    rw [NonFaithful.eqToHom_eq_one]
    exact (F.map_id x).trans (mul_one (1 : K)).symm

/-- Paper `ex:nonfaithful`: every endofunctor of `BK` also preserves the unique basepoint and
    the unique coordinate. -/
theorem nonfaithful_preserves_base_coord (F : SingleObj K ⥤ SingleObj K) :
    (∀ s : Discrete PUnit.{1},
        F.obj ((nonfaithfulPreDatum K).base s) = (nonfaithfulPreDatum K).base s) ∧
      ∀ x : SingleObj K, (nonfaithfulPreDatum K).coord (F.obj x) = (nonfaithfulPreDatum K).coord x :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- Paper `ex:nonfaithful`: the terminal base `S = * = Discrete PUnit` has only the trivial
    strict automorphism, so `Aut(S)` (and every `H ≤ Aut(S)`) is trivial. -/
instance subsingleton_strictAut_discretePUnit : Subsingleton (StrictAut (Discrete PUnit.{1})) :=
  ⟨fun _ _ => StrictAut.ext_hom (CategoryTheory.Functor.ext (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ => Subsingleton.elim _ _))⟩

/-- Paper `ex:nonfaithful`: every strict automorphism of the terminal base is the identity, so
    every admissible pair `(F, A)` of `def:lifts` has `A = 1` and lies in the kernel of `Φ`. -/
theorem strictAut_discretePUnit_eq_one (A : StrictAut (Discrete PUnit.{1})) : A = 1 :=
  Subsingleton.elim _ _

/-- The lift kernel of paper `ex:nonfaithful`: the strict automorphisms of `BK` satisfying the
    lift conditions `IsNonfaithfulLift` over the identity of the terminal base.  The base
    `Discrete PUnit` has only the trivial strict automorphism (`strictAut_discretePUnit_eq_one`),
    so this is the whole kernel of the projection to base automorphisms.  `IsNonfaithfulLift` is
    stronger than the object-level conditions of `def:lifts`; the kernel cut out by the latter
    alone is `nonfaithfulObjLiftKernel K`, and the two coincide
    (`nonfaithfulObjLiftKernel_eq_nonfaithfulLiftKernel`).  Closure holds because the conditions
    hold for every endofunctor (`isNonfaithfulLift_of_functor`). -/
def nonfaithfulLiftKernel : Subgroup (StrictAut (SingleObj K)) where
  carrier := {F | IsNonfaithfulLift K F.hom}
  mul_mem' _ _ := isNonfaithfulLift_of_functor K _
  one_mem' := isNonfaithfulLift_of_functor K _
  inv_mem' _ := isNonfaithfulLift_of_functor K _

/-- Membership in the lift kernel of paper `ex:nonfaithful`. -/
theorem mem_nonfaithfulLiftKernel_iff (F : StrictAut (SingleObj K)) :
    F ∈ nonfaithfulLiftKernel K ↔ IsNonfaithfulLift K F.hom := Iff.rfl

/-- Paper `ex:nonfaithful`: all strict automorphisms of `BK` lie in the lift kernel. -/
theorem nonfaithfulLiftKernel_eq_top : nonfaithfulLiftKernel K = ⊤ :=
  eq_top_iff.2 fun F _ => isNonfaithfulLift_of_functor K F.hom

/-- Paper `ex:nonfaithful`: the lift kernel is `Aut(K)`, via `θSingleObjEquiv`
    (every strict automorphism of `BK` comes from a unique automorphism of `K`). -/
noncomputable def nonfaithfulLiftKernelEquiv : nonfaithfulLiftKernel K ≃* MulAut K :=
  ((MulEquiv.subgroupCongr (nonfaithfulLiftKernel_eq_top K)).trans Subgroup.topEquiv).trans
    (θSingleObjEquiv K)

/-- The identification of paper `ex:nonfaithful` sends a kernel element to its induced
    automorphism of `K`. -/
@[simp] theorem nonfaithfulLiftKernelEquiv_apply (F : nonfaithfulLiftKernel K) :
    nonfaithfulLiftKernelEquiv K F = θSingleObj K F.1 := rfl

/-! ### The kernel for the object-level conditions of `def:lifts` only -/

/-- Exactly the object-level conditions of paper `def:lifts` over the identity base
    automorphism (the only one, `strictAut_discretePUnit_eq_one`), for the chosen data of paper
    `ex:nonfaithful`: `covers` is `eq:cover` with `A = 𝟭`, `equiv` is `eq:equiv` on objects, and
    `src` is `eq:preserve` on objects (same cast proof as `IsNonfaithfulLift.src`).  No arrow-level
    condition is imposed. -/
structure IsNonfaithfulObjLift (F : SingleObj K ⥤ SingleObj K) : Prop where
  covers : F ⋙ nonfaithfulProj K = nonfaithfulProj K ⋙ 𝟭 (Discrete PUnit.{1})
  equiv : ∀ (x : SingleObj K) (g : PUnit.{1}),
    F.obj ((nonfaithfulPreDatum K).act x g) = (nonfaithfulPreDatum K).act (F.obj x) g
  src : ∀ {s t : Discrete PUnit.{1}} (u : s ⟶ t) (y : SingleObj K)
      (hy : (nonfaithfulProj K).obj y = t),
    F.obj ((nonfaithfulPreDatum K).reind u y hy)
      = (nonfaithfulPreDatum K).reind ((𝟭 (Discrete PUnit.{1})).map u) (F.obj y)
          ((Functor.congr_obj covers y).trans (congrArg (𝟭 (Discrete PUnit.{1})).obj hy))

/-- The object-and-arrow lift conditions imply the object-level conditions of paper
    `def:lifts` (paper `ex:nonfaithful`). -/
theorem IsNonfaithfulLift.toObjLift {F : SingleObj K ⥤ SingleObj K}
    (h : IsNonfaithfulLift K F) : IsNonfaithfulObjLift K F :=
  ⟨h.covers, h.equiv, h.src⟩

/-- Paper `ex:nonfaithful`: in this example the object-level conditions of `def:lifts` and the
    stronger `IsNonfaithfulLift` are equivalent (both hold for every endofunctor of `BK`), so the
    arrow-level conditions are not essential for the kernel conclusion. -/
theorem isNonfaithfulObjLift_iff (F : SingleObj K ⥤ SingleObj K) :
    IsNonfaithfulObjLift K F ↔ IsNonfaithfulLift K F :=
  ⟨fun _ => isNonfaithfulLift_of_functor K F, IsNonfaithfulLift.toObjLift K⟩

/-- The kernel of paper `ex:nonfaithful` for the object-level conditions of `def:lifts` only:
    the strict automorphisms of `BK` satisfying `IsNonfaithfulObjLift`. -/
def nonfaithfulObjLiftKernel : Subgroup (StrictAut (SingleObj K)) where
  carrier := {F | IsNonfaithfulObjLift K F.hom}
  mul_mem' _ _ := (isNonfaithfulLift_of_functor K _).toObjLift K
  one_mem' := (isNonfaithfulLift_of_functor K _).toObjLift K
  inv_mem' _ := (isNonfaithfulLift_of_functor K _).toObjLift K

/-- Paper `ex:nonfaithful`: every strict automorphism of `BK` lies in the object-level kernel. -/
theorem nonfaithfulObjLiftKernel_eq_top : nonfaithfulObjLiftKernel K = ⊤ :=
  eq_top_iff.2 fun F _ => (isNonfaithfulLift_of_functor K F.hom).toObjLift K

/-- Paper `ex:nonfaithful`: the object-level kernel of `def:lifts` equals the kernel cut out by
    the stronger `IsNonfaithfulLift` (both are `⊤`). -/
theorem nonfaithfulObjLiftKernel_eq_nonfaithfulLiftKernel :
    nonfaithfulObjLiftKernel K = nonfaithfulLiftKernel K :=
  (nonfaithfulObjLiftKernel_eq_top K).trans (nonfaithfulLiftKernel_eq_top K).symm

/-- Paper `ex:nonfaithful`: the object-level kernel of `def:lifts` is also `Aut(K)`. -/
noncomputable def nonfaithfulObjLiftKernelEquiv : nonfaithfulObjLiftKernel K ≃* MulAut K :=
  (MulEquiv.subgroupCongr (nonfaithfulObjLiftKernel_eq_nonfaithfulLiftKernel K)).trans
    (nonfaithfulLiftKernelEquiv K)

end Kernel

/-! ## 3. `K = C₃`: the kernel is `C₂` although `G` is trivial -/

section ZMod3

namespace NonFaithful

/-- `|Aut(C₃)| = 2` (helper for paper `ex:nonfaithful`). -/
theorem nat_card_mulAut_G3 : Nat.card (MulAut G3) = 2 := by
  have h3 : Nat.card G3 = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [IsCyclic.card_mulAut, h3, Nat.totient_prime Nat.prime_three]

/-- `|C₂| = 2` (helper for paper `ex:nonfaithful`). -/
theorem nat_card_multiplicative_zmod2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

end NonFaithful

/-- `Aut(C₃) ≃* C₂` (paper `ex:nonfaithful`), as groups of prime order `2`. -/
noncomputable def mulAutG3MulEquivZMod2 : MulAut G3 ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq NonFaithful.nat_card_mulAut_G3 NonFaithful.nat_card_multiplicative_zmod2

/-- Paper `ex:nonfaithful` for `K = C₃`: the lift kernel is `C₂`. -/
noncomputable def nonfaithfulLiftKernelZMod3Equiv :
    nonfaithfulLiftKernel G3 ≃* Multiplicative (ZMod 2) :=
  (nonfaithfulLiftKernelEquiv G3).trans mulAutG3MulEquivZMod2

/-- Paper `ex:nonfaithful` for `K = C₃`: the lift kernel has exactly two elements. -/
theorem nat_card_nonfaithfulLiftKernel_G3 : Nat.card (nonfaithfulLiftKernel G3) = 2 :=
  (Nat.card_congr (nonfaithfulLiftKernelEquiv G3).toEquiv).trans NonFaithful.nat_card_mulAut_G3

/-- Paper `ex:nonfaithful`, conclusion: with `K = C₃` the presentation group `G = PUnit` is
    trivial and (N6) fails, while the lift kernel is nontrivial and hence NOT isomorphic to `G`.
    So the kernel conclusion of `thm:strict` (kernel `≅ G`) genuinely requires (N6). -/
theorem nonfaithful_kernel_not_presentationGroup :
    Subsingleton PUnit.{1} ∧ ¬ (nonfaithfulProj G3).Faithful ∧
      Nontrivial (nonfaithfulLiftKernel G3) ∧
      IsEmpty (nonfaithfulLiftKernel G3 ≃* PUnit.{1}) := by
  have hnt : Nontrivial (nonfaithfulLiftKernel G3) :=
    (nonfaithfulLiftKernelEquiv G3).toEquiv.nontrivial
  refine ⟨inferInstance, nonfaithfulProj_not_faithful G3, hnt, ⟨fun e => ?_⟩⟩
  exact not_subsingleton (nonfaithfulLiftKernel G3) e.toEquiv.subsingleton

end ZMod3
