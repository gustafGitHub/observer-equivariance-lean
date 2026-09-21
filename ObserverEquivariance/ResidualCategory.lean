import ObserverEquivariance.Residual

/-!
# The category of invariant functors (display after paper `prop:residual`)

Paper display after `prop:residual`:
`Fun_{G-inv}(O, C) ≅ Fun(S × BG, C) ≅ Fun(S, C^{BG})`.

* `Fun_{G-inv}(O, C)`: `InvFun d C`, whose objects are strictly invariant functors
  (`OEData.IsInvariant`) and whose arrows are INVARIANT natural transformations
  (`IsInvariantNatTrans`, "`α R_h = α`"). On arrows this is NOT the full subcategory of
  `O ⥤ C`: `ResidualCategory.exists_not_isInvariantNatTrans` exhibits, for NONABELIAN `G`, a
  non-invariant natural automorphism of the single invariant functor of `ex:invariant`.  This is
  a different witness from the paper's.  The paper's sentence "This restriction on arrows is
  essential. An unrestricted natural isomorphism can identify functors with different residual
  actions" refers to the `sec:records` calibration (with abelian `G = ℤˣ`), formalized in
  `ObserverEquivariance.Examples.RecordsCalibration` (`recC`, `recC_not_invariant`,
  `recD_no_invariant_iso`).
* Not formalized: the remark after `cor:invariant-calibration` that the diagonal orbit category
  is `O/G ≅ S × BG` in the chosen coordinates (no orbit-category construction is made; the
  closest statement is the unique factorization `invariant_iff_factors` through `N ⋙ Q`).
* `Fun_{G-inv}(O, C) ≅ Fun(S × BG, C)`: strict isomorphism of categories
  `invFunToProdBG d C` / `prodBGToInvFun d C`, with both composites EQUAL to `𝟭`
  (`invFunToProdBG_comp_prodBGToInvFun`, `prodBGToInvFun_comp_invFunToProdBG`).
* `Fun(S × BG, C) ≅ Fun(S, C^{BG})`: mathlib's `Functor.curry` / `Functor.uncurry`, with both
  composites equal to `𝟭` (`curry_comp_uncurry_prodBG`, `uncurry_comp_curry_prodBG`).

Explicit object and transformation recovery lemmas accompany each functor.
-/

open CategoryTheory Residual

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}

/-! ## The category `Fun_{G-inv}(O, C)` -/

/-- Objects of `Fun_{G-inv}(O, C)`: strictly invariant functors `F : O ⥤ C`, `F R_h = F`
    (display after paper `prop:residual`). -/
structure InvFun (d : OEData G p) (C : Type*) [Category C] where
  /-- The underlying functor `F : O ⥤ C`. -/
  functor : O ⥤ C
  /-- Strict invariance `F R_h = F` for all `h : G`. -/
  invariant : d.IsInvariant functor

namespace InvFun

variable {d : OEData G p} {C : Type*} [Category C]

/-- Objects of `Fun_{G-inv}(O, C)` are determined by their underlying functors
    (display after paper `prop:residual`). -/
@[ext] theorem ext {F F' : InvFun d C} (h : F.functor = F'.functor) : F = F' := by
  cases F; cases F'; cases h; rfl

/-- Arrows of `Fun_{G-inv}(O, C)`: invariant natural transformations `α R_h = α`, NOT all
    natural transformations (display after paper `prop:residual`). -/
@[ext] structure Hom (F F' : InvFun d C) where
  /-- The underlying natural transformation `α : F ⟶ F'`. -/
  nat : F.functor ⟶ F'.functor
  /-- Invariance `α R_h = α` (component equalities with the invariance transports). -/
  invariant : IsInvariantNatTrans d F.invariant F'.invariant nat

/-- The category structure of `Fun_{G-inv}(O, C)`: identities and composition are those of
    `O ⥤ C` (display after paper `prop:residual`). -/
instance category : Category (InvFun d C) where
  Hom F F' := Hom F F'
  id F := ⟨𝟙 F.functor, isInvariantNatTrans_id d F.invariant⟩
  comp α β := ⟨α.nat ≫ β.nat, isInvariantNatTrans_comp d α.invariant β.invariant⟩

/-- Arrows of `Fun_{G-inv}(O, C)` are determined by their underlying transformations
    (display after paper `prop:residual`). -/
@[ext] theorem hom_ext {F F' : InvFun d C} {α β : F ⟶ F'} (h : α.nat = β.nat) : α = β :=
  Hom.ext h

/-- Identities of `Fun_{G-inv}(O, C)` (display after paper `prop:residual`). -/
@[simp] theorem id_nat (F : InvFun d C) : Hom.nat (𝟙 F) = 𝟙 F.functor := rfl

/-- Composition of `Fun_{G-inv}(O, C)` (display after paper `prop:residual`). -/
@[simp] theorem comp_nat {F F' F'' : InvFun d C} (α : F ⟶ F') (β : F' ⟶ F'') :
    Hom.nat (α ≫ β) = α.nat ≫ β.nat := rfl

/-- Object casts in `Fun_{G-inv}(O, C)` have underlying transformation the cast of the
    underlying functors (helper for the display after paper `prop:residual`). -/
@[simp] theorem eqToHom_nat {F F' : InvFun d C} (h : F = F') :
    Hom.nat (eqToHom h) = eqToHom (congrArg InvFun.functor h) := by
  subst h; rfl

end InvFun

namespace ResidualCategory

variable {d : OEData G p} {C : Type*} [Category C]

/-- Components of any natural transformation along an object equality, with arbitrary cast
    proofs (helper for the display after paper `prop:residual`). -/
theorem natTrans_app_cast {D : Type*} [Category D] {F F' : D ⥤ C} (α : F ⟶ F') {X Y : D}
    (e : X = Y) (h₁ : F.obj X = F.obj Y) (h₂ : F'.obj Y = F'.obj X) :
    α.app X = eqToHom h₁ ≫ α.app Y ≫ eqToHom h₂ := by
  subst e; simp

/-- An invariant transformation has fiberwise constant components in product coordinates:
    `α_{b_s · a} = α_{b_s · b}` up to the casts (display after paper `prop:residual`:
    "`α_(s,a) = α_(s,1)`"). -/
theorem IsInvariantNatTrans.app_act_base {F F' : O ⥤ C} {hF : d.IsInvariant F}
    {hF' : d.IsInvariant F'} {α : F ⟶ F'} (hα : IsInvariantNatTrans d hF hF' α) (s : S)
    (a b : G) (h₁ : F.obj (d.act (d.base s) a) = F.obj (d.act (d.base s) b))
    (h₂ : F'.obj (d.act (d.base s) b) = F'.obj (d.act (d.base s) a)) :
    α.app (d.act (d.base s) a) = eqToHom h₁ ≫ α.app (d.act (d.base s) b) ≫ eqToHom h₂ := by
  rw [hα a (d.base s), hα b (d.base s)]
  simp

/-- A naturality square with a cast on the target, over clean objects (helper for the display
    after paper `prop:residual`). -/
theorem natTrans_naturality_cast {D : Type*} [Category D] {F F' : D ⥤ C} (α : F ⟶ F')
    {x y z : D} (φ : x ⟶ y) (e₁ : F.obj y = F.obj z) (e₂ : F'.obj y = F'.obj z)
    (h : α.app z = eqToHom e₁.symm ≫ α.app y ≫ eqToHom e₂) :
    (F.map φ ≫ eqToHom e₁) ≫ α.app z = α.app x ≫ F'.map φ ≫ eqToHom e₂ := by
  rw [h]; simp

/-! ## `Fun_{G-inv}(O, C) ⥤ Fun(S × BG, C)` -/

variable (d C) in
/-- The functor `Fun_{G-inv}(O, C) ⥤ Fun(S × BG, C)`: an invariant `F` goes to the unique
    `Ecal` with `Q ⋙ Ecal = M ⋙ F` (paper `prop:residual`), and an invariant `α` goes to
    `Ecal(α)_(s,*) = α_{b_s · 1}` (display after paper `prop:residual`: "`α_(s,a) = α_(s,1)`";
    naturality along `(𝟙 s, r)` is the intertwining condition). -/
noncomputable def invFunToProdBG : InvFun d C ⥤ (S × SingleObj G ⥤ C) where
  obj F := (OEData.IsInvariant.isProductInvariant.{_, _, _, _, _, _, _, 0} F.invariant).factor
  map α :=
    { app := fun X => α.nat.app (d.act (d.base X.1) 1)
      naturality := fun _ Y f =>
        natTrans_naturality_cast α.nat ((normalFormFrom d).map (pairArr f.1 1 (f.2 : G))) _ _
          (IsInvariantNatTrans.app_act_base α.invariant Y.1 1 (f.2 : G) _ _) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Object recovery: `Ecal_F` is the factorization of `M ⋙ F` through `Q`
    (display after paper `prop:residual`). -/
theorem invFunToProdBG_obj (F : InvFun d C) :
    (invFunToProdBG d C).obj F
      = (OEData.IsInvariant.isProductInvariant.{_, _, _, _, _, _, _, 0} F.invariant).factor := rfl

/-- Object recovery on objects: `Ecal_F(s, *) = F(b_s · 1)` (display after paper
    `prop:residual`; paper proof "`Ecal(s,*) = F(s,1)`"). -/
@[simp] theorem invFunToProdBG_obj_obj (F : InvFun d C) (X : S × SingleObj G) :
    ((invFunToProdBG d C).obj F).obj X = F.functor.obj (d.act (d.base X.1) 1) := rfl

/-- Object recovery on arrows: `Ecal_F(u, r) = F(M(u : 1 → r))` up to the invariance cast
    (display after paper `prop:residual`; paper proof "`Ecal(u,r) = F(u : 1 → r)`"). -/
theorem invFunToProdBG_obj_map (F : InvFun d C) {X Y : S × SingleObj G} (f : X ⟶ Y) :
    ((invFunToProdBG d C).obj F).map f
      = F.functor.map ((normalFormFrom d).map (pairArr f.1 1 (f.2 : G)))
        ≫ eqToHom (F.invariant.isProductInvariant.obj_eq Y.1 (f.2 : G) 1) := rfl

/-- Transformation recovery: `Ecal(α)_(s,*) = α_{b_s · 1}` (display after paper
    `prop:residual`). -/
@[simp] theorem invFunToProdBG_map_app {F F' : InvFun d C} (α : F ⟶ F') (X : S × SingleObj G) :
    ((invFunToProdBG d C).map α).app X = α.nat.app (d.act (d.base X.1) 1) := rfl

/-! ## `Fun(S × BG, C) ⥤ Fun_{G-inv}(O, C)` -/

variable (d) in
/-- For any `Ecal : S × BG ⥤ C`, the functor `(N ⋙ Q) ⋙ Ecal` on `O` is strictly invariant,
    since `R_h ⋙ N = N ⋙ P_h` and `P_h ⋙ Q = Q` (paper `prop:residual`). -/
theorem isInvariant_normalFormTo_comp (E : S × SingleObj G ⥤ C) :
    d.IsInvariant ((normalFormTo d ⋙ residualQ S G) ⋙ E) := fun h => by
  simp only [← Functor.assoc]
  rw [normalForm_equivariant, Functor.assoc (normalFormTo d), residualQ_invariant]

variable (d C) in
/-- The functor `Fun(S × BG, C) ⥤ Fun_{G-inv}(O, C)`: `Ecal ↦ (N ⋙ Q) ⋙ Ecal`, and
    `β ↦ β` whiskered by `N ⋙ Q`, which is an invariant transformation
    (display after paper `prop:residual`). The auxiliary hom-universe of `Pair G` is pinned to
    `0`; the composite `N ⋙ Q : O ⥤ S × BG` does not depend on it. -/
noncomputable def prodBGToInvFun : (S × SingleObj G ⥤ C) ⥤ InvFun d C where
  obj E := ⟨(normalFormTo.{_, _, _, _, _, 0} d ⋙ residualQ.{_, _, _, 0} S G) ⋙ E,
    isInvariant_normalFormTo_comp d E⟩
  map {E E'} β :=
    ⟨Functor.whiskerLeft (normalFormTo.{_, _, _, _, _, 0} d ⋙ residualQ.{_, _, _, 0} S G) β,
      fun h x =>
        have e : ((p.obj (d.act x h), SingleObj.star G) : S × SingleObj G)
            = (p.obj x, SingleObj.star G) := Prod.ext (d.p_act x h) rfl
        natTrans_app_cast β e (congrArg E.obj e) (congrArg E'.obj e).symm⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Object recovery: the invariant functor of `Ecal` is `(N ⋙ Q) ⋙ Ecal`, i.e. `F = Ecal Q`
    (display after paper `prop:residual`). -/
@[simp] theorem prodBGToInvFun_obj_functor (E : S × SingleObj G ⥤ C) :
    ((prodBGToInvFun d C).obj E).functor
      = (normalFormTo.{_, _, _, _, _, 0} d ⋙ residualQ.{_, _, _, 0} S G) ⋙ E := rfl

/-- Object recovery on objects: `F(x) = Ecal(p x, *)`, i.e. `F(s, a) = E(s)`
    (paper `prop:residual`). -/
theorem prodBGToInvFun_obj_obj (E : S × SingleObj G ⥤ C) (x : O) :
    ((prodBGToInvFun d C).obj E).functor.obj x = E.obj (p.obj x, SingleObj.star G) := rfl

/-- Object recovery on arrows: `F(f) = Ecal(p f, g_y g_x⁻¹)`, i.e. `F(u : a → b) = Ecal(u, b a⁻¹)`
    (paper `prop:residual`). -/
theorem prodBGToInvFun_obj_map (E : S × SingleObj G ⥤ C) {x y : O} (f : x ⟶ y) :
    ((prodBGToInvFun d C).obj E).functor.map f
      = E.map (((p.map f, (d.coord y * (d.coord x)⁻¹ : G)) :
          ((p.obj x, SingleObj.star G) : S × SingleObj G) ⟶ (p.obj y, SingleObj.star G))) := rfl

/-- Transformation recovery: `α_x = β_(p x, *)` (display after paper `prop:residual`). -/
@[simp] theorem prodBGToInvFun_map_nat_app {E E' : S × SingleObj G ⥤ C} (β : E ⟶ E') (x : O) :
    ((prodBGToInvFun d C).map β).nat.app x = β.app (p.obj x, SingleObj.star G) := rfl

/-! ## The strict isomorphism `Fun_{G-inv}(O, C) ≅ Fun(S × BG, C)` -/

/-- An invariant transformation is determined by its components on the basepoints:
    `α_{b_{p x} · 1} = α_x` up to the casts, since `x = b_{p x} · g_x` (display after paper
    `prop:residual`: "`α_(s,a) = α_(s,1)`"). -/
theorem IsInvariantNatTrans.app_eq_base {F F' : O ⥤ C} {hF : d.IsInvariant F}
    {hF' : d.IsInvariant F'} {α : F ⟶ F'} (hα : IsInvariantNatTrans d hF hF' α) (x : O)
    (h₁ : F.obj (d.act (d.base (p.obj x)) 1) = F.obj x)
    (h₂ : F'.obj x = F'.obj (d.act (d.base (p.obj x)) 1)) :
    α.app (d.act (d.base (p.obj x)) 1) = eqToHom h₁ ≫ α.app x ≫ eqToHom h₂ := by
  have e : d.act (d.base (p.obj x)) (d.coord x) = x := d.base_coord x
  rw [IsInvariantNatTrans.app_act_base hα (p.obj x) 1 (d.coord x)
      (h₁.trans (congrArg F.obj e.symm)) ((congrArg F'.obj e).trans h₂),
    natTrans_app_cast α e (congrArg F.obj e) (congrArg F'.obj e.symm)]
  simp

/-- Object round trip on `Fun_{G-inv}(O, C)`: `(N ⋙ Q) ⋙ Ecal_F = F`
    (display after paper `prop:residual`). -/
theorem prodBGToInvFun_obj_invFunToProdBG_obj (F : InvFun d C) :
    (prodBGToInvFun d C).obj ((invFunToProdBG d C).obj F) = F := by
  ext
  rw [prodBGToInvFun_obj_functor, invFunToProdBG_obj, Functor.assoc,
    IsProductInvariant.residualQ_comp_factor, ← Functor.assoc, normalFormTo_comp_normalFormFrom,
    Functor.id_comp]

variable (d C) in
/-- Strict isomorphism of categories, first half: `Fun_{G-inv}(O, C) ⥤ Fun(S × BG, C) ⥤
    Fun_{G-inv}(O, C)` is EQUAL to the identity functor, on objects and on invariant
    transformations (display after paper `prop:residual`). -/
theorem invFunToProdBG_comp_prodBGToInvFun :
    invFunToProdBG d C ⋙ prodBGToInvFun d C = 𝟭 (InvFun d C) := by
  fapply CategoryTheory.Functor.ext
  · exact prodBGToInvFun_obj_invFunToProdBG_obj
  · intro F F' α
    ext x
    simp only [Functor.id_map, InvFun.comp_nat, NatTrans.comp_app, InvFun.eqToHom_nat,
      eqToHom_app]
    exact IsInvariantNatTrans.app_eq_base α.invariant x _ _

/-- Object round trip on `Fun(S × BG, C)`: `Ecal_{(N ⋙ Q) ⋙ Ecal} = Ecal`, by uniqueness of the
    factorization through `Q` and `M ⋙ N = 𝟭` (display after paper `prop:residual`). -/
theorem invFunToProdBG_obj_prodBGToInvFun_obj (E : S × SingleObj G ⥤ C) :
    (invFunToProdBG d C).obj ((prodBGToInvFun d C).obj E) = E := by
  apply residualQ_cancel.{_, _, _, _, _, 0}
  rw [invFunToProdBG_obj, IsProductInvariant.residualQ_comp_factor, prodBGToInvFun_obj_functor,
    ← Functor.assoc, ← Functor.assoc, normalFormFrom_comp_normalFormTo, Functor.id_comp]

variable (d C) in
/-- Strict isomorphism of categories, second half: `Fun(S × BG, C) ⥤ Fun_{G-inv}(O, C) ⥤
    Fun(S × BG, C)` is EQUAL to the identity functor, on objects and on natural
    transformations (display after paper `prop:residual`). -/
theorem prodBGToInvFun_comp_invFunToProdBG :
    prodBGToInvFun d C ⋙ invFunToProdBG d C = 𝟭 (S × SingleObj G ⥤ C) := by
  fapply CategoryTheory.Functor.ext
  · exact invFunToProdBG_obj_prodBGToInvFun_obj
  · intro E E' β
    ext X
    simp only [Functor.id_map, NatTrans.comp_app, eqToHom_app]
    have e : ((p.obj (d.act (d.base X.1) 1), SingleObj.star G) : S × SingleObj G) = X :=
      Prod.ext ((d.p_act _ 1).trans (d.p_base X.1)) rfl
    exact natTrans_app_cast β e _ _

/-! ## The strict isomorphism `Fun(S × BG, C) ≅ Fun(S, C^{BG})` (mathlib currying) -/

variable (S G C)

/-- Strict isomorphism of categories, first half: currying then uncurrying
    `Fun(S × BG, C) ⥤ Fun(S, Fun(BG, C)) ⥤ Fun(S × BG, C)` is EQUAL to the identity functor
    (display after paper `prop:residual`, `Fun(S × BG, C) ≅ Fun(S, C^{BG})`). -/
theorem curry_comp_uncurry_prodBG :
    (Functor.curry : (S × SingleObj G ⥤ C) ⥤ S ⥤ SingleObj G ⥤ C) ⋙ Functor.uncurry
      = 𝟭 (S × SingleObj G ⥤ C) := by
  fapply CategoryTheory.Functor.ext
  · exact Functor.uncurry_obj_curry_obj
  · intro E E' β
    ext X
    simp only [Functor.id_map, NatTrans.comp_app, eqToHom_app]
    exact natTrans_app_cast β (X := ((X.1, X.2) : S × SingleObj G)) (Y := X) rfl _ _

/-- Strict isomorphism of categories, second half: uncurrying then currying
    `Fun(S, Fun(BG, C)) ⥤ Fun(S × BG, C) ⥤ Fun(S, Fun(BG, C))` is EQUAL to the identity
    functor (display after paper `prop:residual`). -/
theorem uncurry_comp_curry_prodBG :
    (Functor.uncurry : (S ⥤ SingleObj G ⥤ C) ⥤ S × SingleObj G ⥤ C) ⋙ Functor.curry
      = 𝟭 (S ⥤ SingleObj G ⥤ C) := by
  fapply CategoryTheory.Functor.ext
  · exact Functor.curry_obj_uncurry_obj
  · intro E E' β
    ext s r
    simp only [Functor.id_map, NatTrans.comp_app, eqToHom_app]
    exact natTrans_app_cast (β.app s) (X := r) (Y := r) rfl _ _

variable {S G C}

/-- Object recovery for currying: `(curry Ecal)(s)(r) = Ecal(𝟙 s, r)`, the residual action
    `σ_s(r)` (paper `prop:residual`, proof: "`σ_s(r) = Ecal(id_s, r)`"). -/
theorem curry_prodBG_obj_obj_map (E : S × SingleObj G ⥤ C) (s : S) (r : G) :
    ((Functor.curry.obj E).obj s).map (r : SingleObj.star G ⟶ SingleObj.star G)
      = E.map ((𝟙 s, r) : ((s, SingleObj.star G) : S × SingleObj G) ⟶ (s, SingleObj.star G)) :=
  rfl

/-- Object recovery for currying on base arrows: `(curry Ecal)(u)_* = Ecal(u, 1)`, the functor
    `E` (paper `prop:residual`, proof: "`E(u) = Ecal(u, 1)`"). -/
theorem curry_prodBG_obj_map_app (E : S × SingleObj G ⥤ C) {s t : S} (u : s ⟶ t) :
    ((Functor.curry.obj E).map u).app (SingleObj.star G)
      = E.map ((u, 𝟙 (SingleObj.star G)) :
          ((s, SingleObj.star G) : S × SingleObj G) ⟶ (t, SingleObj.star G)) :=
  rfl

/-- Transformation recovery for currying: `((curry β)_s)_* = β_(s, *)`
    (display after paper `prop:residual`). -/
theorem curry_prodBG_map_app_app {E E' : S × SingleObj G ⥤ C} (β : E ⟶ E') (s : S) :
    ((Functor.curry.map β).app s).app (SingleObj.star G) = β.app (s, SingleObj.star G) := rfl

/-- Transformation recovery for uncurrying: `(uncurry β)_(s, *) = (β_s)_*`
    (display after paper `prop:residual`). -/
theorem uncurry_prodBG_map_app {E E' : S ⥤ SingleObj G ⥤ C} (β : E ⟶ E') (X : S × SingleObj G) :
    (Functor.uncurry.map β).app X = (β.app X.1).app X.2 := rfl

/-! ## Residual actions through the isomorphism -/

/-- A cast-cancellation identity over clean objects (helper for the display after paper
    `prop:residual`). -/
theorem eqToHom_conj_conj {A B : C} (h : A = B) (h' : B = A) (f : A ⟶ A) :
    eqToHom h ≫ (eqToHom h' ≫ f ≫ eqToHom h'.symm) ≫ eqToHom h.symm = f := by
  subst h; simp

/-- Residual-action recovery: the image of the vertical arrow `(𝟙 s, r)` under `Ecal_F` is the
    residual action `σ_s(r)` of the invariant functor `F`, up to the cast `F(b_s · 1) = F(b_s)`
    (paper `prop:residual`: "the images of the vertical arrows `(id_s : 1 → r)` are precisely
    `σ_s(r)`"; display after it: naturality along vertical arrows is the intertwining). -/
theorem invFunToProdBG_obj_map_vert (F : InvFun d C) (s : S) (r : G)
    (h : F.functor.obj (d.act (d.base s) 1) = F.functor.obj (d.base s)) :
    ((invFunToProdBG d C).obj F).map
        ((𝟙 s, r) : ((s, SingleObj.star G) : S × SingleObj G) ⟶ (s, SingleObj.star G))
      = eqToHom h ≫ (residualAction d F.functor F.invariant s r).hom ≫ eqToHom h.symm := by
  have hE : (normalFormTo.{_, _, _, _, _, 0} d ⋙ residualQ.{_, _, _, 0} S G)
      ⋙ (invFunToProdBG d C).obj F = F.functor :=
    congrArg InvFun.functor (prodBGToInvFun_obj_invFunToProdBG_obj F)
  rw [residualAction_agrees d F.functor F.invariant hE s r h.symm]
  exact (eqToHom_conj_conj h h.symm _).symm

/-! ## `Fun_{G-inv}(O, C)` is not full on arrows -/

/-- For `k : G`, the natural transformation `α_a = a k a⁻¹` of the invariant functor
    `Pair G ⥤ BG`, `a → b ↦ b a⁻¹` of paper `ex:invariant` (helper for the display after paper
    `prop:residual`: "This restriction on arrows is essential"). -/
def conjNatTrans (G : Type*) [Group G] (k : G) :
    invariantPairFunctor G ⟶ invariantPairFunctor G where
  app a := (a.pt * k * a.pt⁻¹ : G)
  naturality a b _ := by
    show (b.pt * k * b.pt⁻¹) * (b.pt * a.pt⁻¹) = (b.pt * a.pt⁻¹) * (a.pt * k * a.pt⁻¹)
    group

/-- The transformation `α_a = a k a⁻¹` is invariant only if `k` commutes with every `h`
    (display after paper `prop:residual`: "This restriction on arrows is essential"). -/
theorem conjNatTrans_not_isInvariant {G : Type*} [Group G] {h k : G} (hk : h * k ≠ k * h) :
    ¬ IsInvariantNatTrans (witness G) (invariantPairFunctor_isInvariant G)
      (invariantPairFunctor_isInvariant G) (conjNatTrans G k) := by
  intro hα
  have e := hα h ⟨1⟩
  change ((1 : G) * h) * k * (1 * h)⁻¹ = ((1 : G) * ((1 : G) * k * (1 : G)⁻¹)) * 1 at e
  simp only [one_mul, mul_one, inv_one] at e
  exact hk ((mul_inv_eq_iff_eq_mul).1 e)

/-- `Fun_{G-inv}(O, C)` is NOT the full subcategory of `O ⥤ C`: for a NONABELIAN `G` there are
    invariant functors (here both equal to the functor of `ex:invariant`) and a natural
    transformation between them that underlies no arrow of `InvFun` (display after paper
    `prop:residual`, the arrows of `Fun_{G-inv}` are only the invariant transformations).
    This is NOT the witness the paper uses for "This restriction on arrows is essential": the
    paper's point is that an unrestricted natural isomorphism can identify functors with
    DIFFERENT residual actions, as in the `sec:records` calibration (abelian `G = ℤˣ`), which is
    formalized in `ObserverEquivariance.Examples.RecordsCalibration` (`recC`,
    `recC_not_invariant`, `recD_no_invariant_iso`). -/
theorem exists_not_isInvariantNatTrans {G : Type*} [Group G] (hG : ∃ h k : G, h * k ≠ k * h) :
    ∃ (F F' : InvFun (witness G) (SingleObj G)) (α : F.functor ⟶ F'.functor),
      ∀ β : F ⟶ F', β.nat ≠ α := by
  obtain ⟨h, k, hk⟩ := hG
  refine ⟨⟨invariantPairFunctor G, invariantPairFunctor_isInvariant G⟩,
    ⟨invariantPairFunctor G, invariantPairFunctor_isInvariant G⟩, conjNatTrans G k, ?_⟩
  intro β hβ
  apply conjNatTrans_not_isInvariant hk
  rw [← hβ]
  exact β.invariant

end ResidualCategory
