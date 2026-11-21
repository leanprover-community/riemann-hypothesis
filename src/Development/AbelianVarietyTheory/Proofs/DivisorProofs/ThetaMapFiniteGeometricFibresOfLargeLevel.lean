import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensioStatement
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialScaledFini
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelThetaPointOfThetaConstantsLevelSquare

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.FinAct

theorem finite_oActs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)), letI := H.starRing;
    Set.Finite {act : 𝓞 E → (P.A ⟶ P.A) | ∃ ρ : P.OAct (𝓞 E), ∀ a, ρ.act a = act a} := by
  intro E _ _ _ H K _ _ _ P
  letI := H.starRing
  have h₂ := GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion.2
  choose cn hcn using GlobalTheory.exists_starNormLE_of_isCMField E (fun a => H.bar_eq a)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  set g := P.g
  set M := 4 ^ g * g.factorial * (2 * s.sup cn) + 1 with hM
  have hM1 : 1 ≤ M := Nat.le_add_left _ _
  have key : ∀ c, c ≤ s.sup cn → 4 ^ g * g.factorial * (2 * c) < M ^ 2 := fun c hc =>
    calc 4 ^ g * g.factorial * (2 * c) ≤ 4 ^ g * g.factorial * (2 * s.sup cn) := by gcongr
      _ < M := Nat.lt_succ_self _
      _ ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  have hK : (M : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let T := {x : baseOver (Sp K) ⟶ P.A // x ^ M = 1}
  haveI : Finite T := GlobalTheory.AbTorsionFinite.finite_torsion K P.A P.isAb M hM1
  classical
  let F : (𝓞 E → (P.A ⟶ P.A)) → (s → T → Option T) := fun act a x =>
    if h : (x.1 ≫ act a) ^ M = 1 then some ⟨_, h⟩ else none
  refine Set.Finite.of_finite_image (f := F) (Set.toFinite _) ?_
  rintro act₁ ⟨ρ₁, h₁⟩ act₂ ⟨ρ₂, h₂'⟩ hF
  have tor : ∀ (ρ : P.OAct (𝓞 E)) (a : 𝓞 E) (x : T), (x.1 ≫ ρ.act a) ^ M = 1 := fun ρ a x => by
    have := ρ.hom a
    have e := map_pow (IsMonHom.monoidHom (ρ.act a) (baseOver (Sp K))) x.1 M
    rw [x.2, map_one] at e
    exact e.symm
  have onS : ∀ a ∈ s, ρ₁.act a = ρ₂.act a := fun a ha => by
    have := h₂ g (cn a) M (key _ (Finset.le_sup ha)) K hK P P rfl rfl (Iso.refl _)
      (ThetaPtDet.isPolIso_refl P) (𝓞 E) ρ₁ ρ₂ a (hcn a) fun y hy => by
        have e := congrFun (congrFun hF ⟨a, ha⟩) ⟨y, hy⟩
        simp only [F, h₁, h₂'] at e
        rw [dif_pos (h₁ a ▸ tor ρ₁ a ⟨y, hy⟩), dif_pos (h₂' a ▸ tor ρ₂ a ⟨y, hy⟩)] at e
        have e' := congrArg Subtype.val (Option.some_injective _ e)
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, h₁, h₂']
        exact e'
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using this
  have add₁ : ∀ a b, ρ₁.act (a + b) = ρ₁.act a * ρ₁.act b := ρ₁.map_add
  have add₂ : ∀ a b, ρ₂.act (a + b) = ρ₂.act a * ρ₂.act b := ρ₂.map_add
  let f₁ : 𝓞 E →+ Additive (P.A ⟶ P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (ρ₁.act a))
    fun a b => by rw [add₁]; rfl
  let f₂ : 𝓞 E →+ Additive (P.A ⟶ P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (ρ₂.act a))
    fun a b => by rw [add₂]; rfl
  have hf : f₁ = f₂ := AddMonoidHom.eq_of_eqOn_dense (s := (s : Set (𝓞 E)))
    (by rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl) fun a ha =>
      congrArg Additive.ofMul (onS a ha)
  funext a
  rw [← h₁, ← h₂']
  exact Additive.ofMul.injective (DFunLike.congr_fun hf a)

end GlobalTheory.UMin.FinAct
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integerRing_actions_principallyPolarised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)), letI := H.starRing; Set.Finite {act : 𝓞 E → (P.A ⟶ P.A) | ∃ ρ : P.OAct (𝓞 E), ∀ a, ρ.act a = act a} := by
  atlas_forward_decl GlobalTheory.UMin.FinAct.finite_oActs
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem moduli_point_eq_of_same_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (x x' : Sp K ⟶ Xo.X) (α α' : P.A.left ⟶ Xo.univ.t.G.left), x ≫ Xo.s = x' ≫ Xo.s → IsGrpPullback P.A Xo.univ.t.G x α → IsGrpPullback P.A Xo.univ.t.G x' α' → LBIso P.L (Xo.univ.t.PP.L.pull α) → LBIso P.L (Xo.univ.t.PP.L.pull α') → (∀ a, ∃ h : P.A ⟶ P.A, h.left ≫ α = α ≫ (Xo.univ.t.act.act a).left ∧ h.left ≫ α' = α' ≫ (Xo.univ.t.act.act a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.eta a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.eta a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.etaA a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.etaA a).left) → x = x' := by
  intro E _ _ _ H D l Xo K _ _ P x x' α α' hs hα hα' hL hL' hact hM hA
  choose act h₁ h₂ using hact
  have h : GlobalTheory.ArcUnique.IsFibre P.A act P.L Xo.univ.t x α := ⟨hα, h₁, hL⟩
  have h' : GlobalTheory.ArcUnique.IsFibre P.A act P.L Xo.univ.t x' α' := ⟨hα', h₂, hL'⟩
  obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ (Sp K) Xo.s
    (x ≫ Xo.s) x rfl rfl ((Category.comp_id _).symm.trans (congrArg ((x ≫ Xo.s) ≫ ·) (Spec.map_id _).symm)) Xo.univ
  obtain ⟨ρ, e₁, g, ha, hi⟩ := h.cancel P.isLB o'.t.PP.isLB (GlobalTheory.ArcUnique.isFibre_of_sabMap m.toSABMap)
    (Category.id_comp x)
  obtain ⟨f₁, f₂, f₃⟩ := h'.precomp P.isLB o'.t.PP.isLB g ha hi
  rw [Category.id_comp] at f₁
  have := o'.proper
  obtain ⟨m', hm'⟩ := exists_sabMap_of_lbIso E H _ _ Xo.univ.t o'.t x' (ρ ≫ α')
    ⟨inferInstance, fun s _ K _ _ t _ => inferInstance⟩ f₁ f₂ f₃
  have key : ∀ (y : 𝟙_ (Over (Sp K)) ⟶ o'.t.G) (w : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
      y.left ≫ m.toSABMap.φ = x ≫ w.left →
      (∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ w.left ∧ z.left ≫ α' = x' ≫ w.left) →
      y.left ≫ m'.φ = x' ≫ w.left := by
    rintro y w hy ⟨z, z₁, z₂⟩
    have e : y.left ≫ ρ = z.left := hα.1.hom_ext (by rw [Category.assoc, e₁, hy, z₁]) (by
      rw [Category.assoc, g.1.w, ← Category.assoc, Over.w, Over.w]
      exact Category.comp_id _)
    rw [hm', ← Category.assoc, e, z₂]
  exact (Xo.rep _ _ inferInstance o').unique ⟨rfl, ⟨m⟩⟩
    ⟨hs.symm, ⟨⟨m', fun a => key _ _ (m.eta a) (hM a), fun a => key _ _ (m.etaA a) (hA a)⟩⟩⟩

end GlobalTheory.UMin
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduli_geometric_point_eq_of_same_fibre_action_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (x x' : Sp K ⟶ Xo.X) (α α' : P.A.left ⟶ Xo.univ.t.G.left), x ≫ Xo.s = x' ≫ Xo.s → IsGrpPullback P.A Xo.univ.t.G x α → IsGrpPullback P.A Xo.univ.t.G x' α' → LBIso P.L (Xo.univ.t.PP.L.pull α) → LBIso P.L (Xo.univ.t.PP.L.pull α') → (∀ a, ∃ h : P.A ⟶ P.A, h.left ≫ α = α ≫ (Xo.univ.t.act.act a).left ∧ h.left ≫ α' = α' ≫ (Xo.univ.t.act.act a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.eta a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.eta a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.etaA a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.etaA a).left) → x = x' := by
  atlas_forward_decl GlobalTheory.UMin.moduli_point_eq_of_same_fibre
end

section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PolPartPull

def torusExtPull {k Ω : Type} [Field k] [Field Ω] (f : Sp Ω ⟶ Sp k) (G : Over (Sp k)) [GrpObj G]
    (T : TorusExtension G) : TorusExtension ((Over.pullback f).obj G) :=
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  haveI : IsMonHom (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose.hom :=
    (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose_spec.1
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := (Over.pullback f).obj T.B
    grpB := inferInstance
    isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
    q := (Over.pullback f).map T.q
    q_hom := inferInstance
    q_flat := MorphismProperty.of_isPullback (P := @Flat) (GlobalTheory.SS.isPullback_overPullback_map_left f T.q) T.q_flat
    q_surjective :=
      MorphismProperty.of_isPullback (P := @Surjective) (GlobalTheory.SS.isPullback_overPullback_map_left f T.q) T.q_surjective
    q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact)
      (GlobalTheory.SS.isPullback_overPullback_map_left f T.q) T.q_quasiCompact
    i := (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose.hom ≫ (Over.pullback f).map T.i
    i_hom := inferInstance
    isKernel := by
      refine IsPullback.of_iso (T.isKernel.map (Over.pullback f))
        (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose.symm (Iso.refl _)
        (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · exact toUnit_unique _ _
      · simp
      · simp }

def oActIso {O : Type} [CommRing O] {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom]
    (a : OAct O A) : OAct O B where
  act x := e.inv ≫ a.act x ≫ e.hom
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one]; simp
  mul x y := by rw [a.mul]; simp
  add x y := by rw [a.add, MonObj.mul_comp, MonObj.comp_mul]

theorem pbMap_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

theorem rosatiAdj_pull {K K' : Type} [Field K] [Field K'] (f : K →+* K') {P : Out.PolAV (Sp K)}
    {P' : Out.PolAV (Sp K')} {ψ : P'.A.left ⟶ P.A.left} (hψ : IsGrpPullback P'.A P.A (spMap f) ψ)
    (hL : LBIso (P.L.pull ψ) P'.L) {a b : P.A ⟶ P.A} {a' b' : P'.A ⟶ P'.A} (ha : a'.left ≫ ψ = ψ ≫ a.left)
    (hb : b'.left ≫ ψ = ψ ≫ b.left) (hr : Out.RosatiAdj P.A P.L a b) : Out.RosatiAdj P'.A P'.L a' b' := by
  haveI := P.isAb.comm
  haveI := P'.isAb.comm
  let U₂ := lift (pushPt hψ.1.w (fst P'.A P'.A)) (pushPt hψ.1.w (snd P'.A P'.A))
  have u₁ : U₂.left ≫ (fst P.A P.A).left = (fst P'.A P'.A).left ≫ ψ := TripleDescent.lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd P.A P.A).left = (snd P'.A P'.A).left ≫ ψ := TripleDescent.lift_left_snd _ _
  have v₁ : (fst P'.A P'.A ≫ a').left ≫ ψ = U₂.left ≫ (fst P.A P.A ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, ← u₁, Category.assoc]
  have v₂ : (snd P'.A P'.A ≫ b').left ≫ ψ = U₂.left ≫ (snd P.A P.A ≫ b).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, ← u₂, Category.assoc]
  have hφ : ∀ k, Out.rosatiφ P'.A a' b' k ≫ ψ = U₂.left ≫ Out.rosatiφ P.A a b k := fun k => by
    fin_cases k
    exacts [ArcPull.mul_push hψ U₂.left v₁ u₂.symm, v₁, u₂.symm, ArcPull.mul_push hψ U₂.left u₁.symm v₂, u₁.symm, v₂]
  obtain ⟨t, ht⟩ := RosatiDescent.exists_gen_of_rosatiAdj hr
  obtain ⟨w, hw⟩ := LBIso.symm hL
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : LB.Gen (LB.LinComb P.L (fun k => Out.rosatiφ P'.A a' b' k ≫ ψ) Out.rosatiε), t₁.IsGen := by
    rw [show (fun k => Out.rosatiφ P'.A a' b' k ≫ ψ) = fun k => U₂.left ≫ Out.rosatiφ P.A a b k from funext hφ]
    exact ⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩
  obtain ⟨a₀, ha₀⟩ := exists_down ((isGen_iff w).1 hw) P.isLB P'.isLB t₁ ht₁
  exact fun s => ⟨⊤, trivial, _, DVR.pullGen_isGen _ _ _ a₀ ha₀ _⟩

end GlobalTheory.PolPartPull

namespace GlobalTheory.PolPartPull

theorem polPart_of_isActPull : ∀ (O : Type) [CommRing O] (c : O →+* O) (K K' : Type) [Field K] [Field K'] (f : K →+* K') (G : Over (Sp K)) [GrpObj G] (i : OAct O G) (G' : Over (Sp K')) [GrpObj G'] (i' : OAct O G') (φ : G'.left ⟶ G.left), IsActPull i' i (spMap f) φ → PolPart c i → PolPart c i' := by
  intro O _ c K K' _ _ f G _ i G' _ i' φ h hP
  obtain ⟨T, P, e, j, hm, heq, hr⟩ := hP
  haveI := P.isAb.comm
  haveI := hm
  obtain ⟨P', ψ, -, hψ, hL⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.allSixLaws.1.polBaseChange f P
  obtain ⟨ge, hgm, hgg⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap f)) h.1
  obtain ⟨β, hβm, hβ⟩ := grpPullback_iso (isGrpPullback_pullback P.A (spMap f)) hψ
  haveI := hgm
  haveI := hβm
  have hgi : ∀ a, ge.hom ≫ i'.act a = (Over.pullback (spMap f)).map (i.act a) ≫ ge.hom := fun a => by
    apply Over.OverMorphism.ext
    apply h.1.1.hom_ext
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, h.2 a, hgg, ← Category.assoc, hgg,
        pbMap_fst]
    · rw [Over.w, Over.w]
  have h2 : ∀ a, i'.act a ≫ ge.inv = ge.inv ≫ (Over.pullback (spMap f)).map (i.act a) := fun a => by
    rw [Iso.comp_inv_eq, Category.assoc, ← hgi, Iso.inv_hom_id_assoc]
  let j' : OAct O P'.A := oActIso β (OAct.pullback (spMap f) P.A j)
  have hj : ∀ a, (j'.act a).left ≫ ψ = ψ ≫ (j.act a).left := fun a => by
    show (β.inv ≫ (Over.pullback (spMap f)).map (j.act a) ≫ β.hom).left ≫ ψ = _
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hβ, pbMap_fst, ← hβ, ← Category.assoc,
      ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
  let T' := torusExtOfIso ge (torusExtPull (spMap f) G T)
  have e1 : T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom =
      ge.inv ≫ (Over.pullback (spMap f)).map (T.q ≫ e.hom) ≫ β.hom := by
    show (ge.inv ≫ (Over.pullback (spMap f)).map T.q) ≫ (Over.pullback (spMap f)).map e.hom ≫ β.hom = _
    rw [Functor.map_comp, Category.assoc, Category.assoc]
  refine ⟨T', P', (Over.pullback (spMap f)).mapIso e ≪≫ β, j', ?_, fun a => ?_, fun a =>
    rosatiAdj_pull f hψ hL (hj a) (hj (c a)) (hr a)⟩
  · show IsMonHom (T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom)
    rw [e1]
    infer_instance
  · show i'.act a ≫ T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom =
      (T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom) ≫ j'.act a
    rw [e1]
    show i'.act a ≫ ge.inv ≫ (Over.pullback (spMap f)).map (T.q ≫ e.hom) ≫ β.hom =
      (ge.inv ≫ (Over.pullback (spMap f)).map (T.q ≫ e.hom) ≫ β.hom) ≫ β.inv ≫
        (Over.pullback (spMap f)).map (j.act a) ≫ β.hom
    rw [← Category.assoc (i'.act a), h2]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, heq a]

end GlobalTheory.PolPartPull
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMinQF
open ReciprocityTheory.ChartRestriction.G.DVR

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

theorem sab_gen (t : SAB H S) (a : 𝓞 E) : ∃ v : LB.Gen (LB.LinComb t.PP.L
    (rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) rosatiε), v.IsGen := by
  obtain ⟨u, hu⟩ := gen_of_lbIso (LBIso.symm (t.adj a))
  obtain ⟨v, hv, -⟩ := exists_gen t.PP.isLB (φ' := rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) (ε' := rosatiε)
    (fun U _ k => by
      have p := prod_ros (t.act.act a) (t.act.act (H.bar a)) (fst t.G t.G) (snd t.G t.G) k
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      refine (prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := U) _ (prod_cube₂ _ _ k)
        (prod_neg _ _ (prod_cube₂ _ _ k))).trans (Eq.trans ?_ p.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) u hu
  exact ⟨v, hv⟩

theorem rosati_fibre (t : SAB H S) {K : Type} [Field K] (P : PolAV (Sp K)) (x : Sp K ⟶ S)
    {α : P.A.left ⟶ t.G.left} (hα : IsGrpPullback P.A t.G x α) (hL : LBIso P.L (t.PP.L.pull α))
    {a b : P.A ⟶ P.A} (c : 𝓞 E) (ha : a.left ≫ α = α ≫ (t.act.act c).left)
    (hb : b.left ≫ α = α ≫ (t.act.act (H.bar c)).left) : RosatiAdj P.A P.L a b := by
  haveI := P.isAb.comm
  let U₂ := lift (pushPt hα.1.w (fst P.A P.A)) (pushPt hα.1.w (snd P.A P.A))
  have u₁ : U₂.left ≫ (fst t.G t.G).left = (fst P.A P.A).left ≫ α := TripleDescent.lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd t.G t.G).left = (snd P.A P.A).left ≫ α := TripleDescent.lift_left_snd _ _
  have v₁ : (fst P.A P.A ≫ a).left ≫ α = U₂.left ≫ (fst t.G t.G ≫ t.act.act c).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, ← u₁, Category.assoc]
  have v₂ : (snd P.A P.A ≫ b).left ≫ α = U₂.left ≫ (snd t.G t.G ≫ t.act.act (H.bar c)).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, ← u₂, Category.assoc]
  have hφ : ∀ k, rosatiφ P.A a b k ≫ α = U₂.left ≫ rosatiφ t.G (t.act.act c) (t.act.act (H.bar c)) k := fun k => by
    fin_cases k
    exacts [ArcPull.mul_push hα U₂.left v₁ u₂.symm, v₁, u₂.symm, ArcPull.mul_push hα U₂.left u₁.symm v₂, u₁.symm, v₂]
  obtain ⟨t₀, ht₀⟩ := sab_gen t c
  obtain ⟨w, hw⟩ := hL
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : LB.Gen (LB.LinComb t.PP.L (fun k => rosatiφ P.A a b k ≫ α) rosatiε), t₁.IsGen := by
    rw [show (fun k => rosatiφ P.A a b k ≫ α) = fun k => U₂.left ≫ rosatiφ t.G (t.act.act c) (t.act.act (H.bar c)) k
      from funext hφ]
    exact ⟨_, DVR.pullGen_isGen _ _ _ t₀ ht₀ _⟩
  obtain ⟨a₀, ha₀⟩ := exists_down ((isGen_iff w).1 hw) t.PP.isLB P.isLB t₁ ht₁
  exact fun s => ⟨⊤, trivial, _, DVR.pullGen_isGen _ _ _ a₀ ha₀ _⟩

theorem exists_oact (t : SAB H S) {K : Type} [Field K] (P : PolAV (Sp K)) (x : Sp K ⟶ S)
    {α : P.A.left ⟶ t.G.left} (hα : IsGrpPullback P.A t.G x α) (hL : LBIso P.L (t.PP.L.pull α)) :
    letI := H.starRing
    ∃ ρ : P.OAct (𝓞 E), ∀ c, (ρ.act c).left ≫ α = α ≫ (t.act.act c).left := by
  letI := H.starRing
  haveI := P.isAb.comm
  obtain ⟨β, hβm, hβ⟩ := grpPullback_iso (isGrpPullback_pullback t.G x) hα
  haveI := hβm
  let j' : OAct (𝓞 E) P.A := PolPartPull.oActIso β (OAct.pullback x t.G t.act)
  have hj : ∀ c, (j'.act c).left ≫ α = α ≫ (t.act.act c).left := fun c => by
    show (β.inv ≫ (Over.pullback x).map (t.act.act c) ≫ β.hom).left ≫ α = _
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hβ, PolPartPull.pbMap_fst, ← hβ,
      ← Category.assoc, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
  exact ⟨{ j'.toRingAct with rosati := fun c => rosati_fibre t P x hα hL c (hj c) (hj (star c)) }, hj⟩

end GlobalTheory.UMinQF

noncomputable section
namespace GlobalTheory.UMinQF
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem range_finite {La Q : Type} [AddCommGroup La] [Module.Finite ℤ La] [CommGroup Q] (f : La → Q)
    (hf : ∀ a b, f (a + b) = f a * f b) (n : ℕ) (hn : 0 < n) (hk : ∀ a, f (n • a) = 1) : (Set.range f).Finite := by
  let φ : Multiplicative La →* Q := MonoidHom.mk' (fun a => f a.toAdd) (fun a b => hf _ _)
  haveI : Group.FG (Multiplicative La) := AddGroup.fg_iff_mul_fg.1 (Module.Finite.iff_addGroup_fg.1 ‹_›)
  haveI := Group.fg_range φ
  have hpow : ∀ a : Multiplicative La, φ a ^ n = 1 := fun a => by
    rw [← map_pow]; exact hk a.toAdd
  haveI : Finite φ.range := CommGroup.finite_of_fg_isMulTorsion _ (fun y => by
    obtain ⟨_, a, rfl⟩ := y
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, Subtype.ext (hpow a)⟩)
  have : Set.range f = (φ.range : Set Q) := by
    ext q; constructor
    · rintro ⟨a, rfl⟩; exact ⟨Multiplicative.ofAdd a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨a.toAdd, rfl⟩
  rw [this]; exact Set.toFinite _

theorem tors_finite (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) {K : Type} [Field K] [IsAlgClosed K]
    (P : PolAV (Sp K)) (x : Sp K ⟶ Xo.X) {α : P.A.left ⟶ Xo.univ.t.G.left}
    (hα : IsGrpPullback P.A Xo.univ.t.G x α) (n : ℕ) (hn : 0 < n) :
    {z : baseOver (Sp K) ⟶ P.A | z ^ n = 1}.Finite := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  have hs : x ≫ Xo.s = spMap (Spec.preimage (x ≫ Xo.s)).hom := by simp [spMap]
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x _ hs
  have hR : (Set.range (I.ev n)).Finite := range_finite (I.ev n) (I.add n) n hn (fun a =>
    (I.ker n hn (n • a)).2 ⟨a, rfl⟩)
  let e : Over.mk x ⟶ Over.mk (𝟙 (Sp K) ≫ x) := Over.homMk (𝟙 _) (by simp)
  refine Set.Finite.of_injOn (f := fun z => e ≫ ObjPull.pushEquiv hα (baseOver (Sp K)) z) (t := Set.range (I.ev n))
    (fun z hz => ?_) (fun z _ z' _ h => ?_) hR
  · have : (e ≫ ObjPull.pushEquiv hα (baseOver (Sp K)) z) ^ n = 1 := by
      rw [← MonObj.comp_pow, ← map_pow, show z ^ n = 1 from hz, map_one, MonObj.comp_one]
    exact (I.onto n hn _).1 this
  · apply (ObjPull.pushEquiv hα (baseOver (Sp K))).injective
    apply Over.OverMorphism.ext
    have := congrArg CommaMorphism.left h
    simpa [e] using this

end GlobalTheory.UMinQF

noncomputable section
namespace GlobalTheory.UMinQF

theorem addFun_finite {La Q : Type} [AddCommGroup La] [Module.Finite ℤ La] [CommGroup Q] (T : Set Q) (hT : T.Finite) :
    {f : La → Q | (∀ a b, f (a + b) = f a * f b) ∧ ∀ a, f a ∈ T}.Finite := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := La)
  let hom : ∀ f : La → Q, (∀ a b, f (a + b) = f a * f b) → La →ₗ[ℤ] Additive Q := fun f hf =>
    (AddMonoidHom.mk' (fun a => Additive.ofMul (f a)) (fun a b => by rw [hf]; rfl)).toIntLinearMap
  refine Set.Finite.of_injOn (f := fun f (g : s) => f g) (t := {v : s → Q | ∀ i, v i ∈ T})
    (fun f hf => fun g => hf.2 g) (fun f hf f' hf' h => ?_) (Set.Finite.pi' fun _ => hT)
  have := LinearMap.ext_on hs (f := hom f hf.1) (g := hom f' hf'.1) (fun g hg => by
    show Additive.ofMul (f g) = Additive.ofMul (f' g)
    exact congrArg Additive.ofMul (congrFun h ⟨g, hg⟩))
  funext a
  exact congrArg Additive.toMul (LinearMap.congr_fun this a)

end GlobalTheory.UMinQF

noncomputable section
namespace GlobalTheory.UMinQF

theorem pow_of_add {La Q : Type} [AddCommGroup La] [Group Q] (f : La → Q) (hf : ∀ a b, f (a + b) = f a * f b)
    (n : ℕ) (a : La) : f (n • a) = f a ^ n :=
  (AddMonoidHom.mk' (fun a => Additive.ofMul (f a)) (fun a b => by rw [hf]; rfl)).map_nsmul n a

theorem finite_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (s₀ : Sp K ⟶ Sp (KA l)), Set.Finite {x : Sp K ⟶ Xo.X | x ≫ Xo.s = s₀ ∧ ∃ α : P.A.left ⟶ Xo.univ.t.G.left, IsGrpPullback P.A Xo.univ.t.G x α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α)} := by
  intro E _ _ _ H Dw l Xo K _ _ P s₀
  haveI := P.isAb.comm
  letI := H.starRing
  haveI := Dw.fin
  haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  haveI : CharZero K := charZero_of_injective_ringHom
    (((Spec.preimage s₀).hom.comp (algebraMap ℚ (KA l))).injective)
  set X0 := {x : Sp K ⟶ Xo.X | x ≫ Xo.s = s₀ ∧ ∃ α : P.A.left ⟶ Xo.univ.t.G.left,
    IsGrpPullback P.A Xo.univ.t.G x α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α)} with hX0
  have hx : ∀ x : X0, ∃ (α : P.A.left ⟶ Xo.univ.t.G.left) (_ : IsGrpPullback P.A Xo.univ.t.G x.1 α)
      (_ : LBIso P.L (Xo.univ.t.PP.L.pull α)) (ρ : P.OAct (𝓞 E)),
      ∀ c, (ρ.act c).left ≫ α = α ≫ (Xo.univ.t.act.act c).left := fun x => by
    obtain ⟨-, α, h₁, h₂⟩ := x.2
    obtain ⟨ρ, hρ⟩ := exists_oact Xo.univ.t P x.1 h₁ h₂
    exact ⟨α, h₁, h₂, ρ, hρ⟩
  choose α hα hL ρ hρ using hx
  let pt : ∀ x : X0, (𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) →* (baseOver (Sp K) ⟶ P.A) := fun x => ObjPull.secPull (hα x)
  rcases X0.eq_empty_or_nonempty with h0 | ⟨x₀, hx₀⟩
  · rw [h0]; exact Set.finite_empty
  have hM : 0 < l.M := by have := l.three_le; omega
  have TM := tors_finite Dw l Xo P _ (hα ⟨x₀, hx₀⟩) l.M hM
  have TA := tors_finite Dw l Xo P _ (hα ⟨x₀, hx₀⟩) l.A l.A_pos
  have hMb : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left h
  let F := fun x : X0 => ((fun c => (ρ x).act c), (fun a => pt x (Xo.univ.eta a)), (fun a => pt x (Xo.univ.etaA a)))
  set As := {act : 𝓞 E → (P.A ⟶ P.A) | ∃ ρ : P.OAct (𝓞 E), ∀ a, ρ.act a = act a}
  have hA : As.Finite := GlobalTheory.T.finite_integerRing_actions_principallyPolarised E H K P
  set FM := {f : Dw.La → (baseOver (Sp K) ⟶ P.A) | (∀ a b, f (a + b) = f a * f b) ∧
    ∀ a, f a ∈ {z : baseOver (Sp K) ⟶ P.A | z ^ l.M = 1}}
  set FA := {f : Dw.La → (baseOver (Sp K) ⟶ P.A) | (∀ a b, f (a + b) = f a * f b) ∧
    ∀ a, f a ∈ {z : baseOver (Sp K) ⟶ P.A | z ^ l.A = 1}}
  have hFM : FM.Finite := addFun_finite _ TM
  have hFA : FA.Finite := addFun_finite _ TA
  have mem : ∀ x, F x ∈ As ×ˢ FM ×ˢ FA := fun x => by
    refine ⟨⟨ρ x, fun _ => rfl⟩, ⟨fun a b => ?_, fun a => ?_⟩, ⟨fun a b => ?_, fun a => ?_⟩⟩
    · show pt x _ = pt x _ * pt x _
      rw [Xo.univ.eta_add, map_mul]
    · show pt x _ ^ l.M = 1
      rw [← map_pow, ← pow_of_add _ Xo.univ.eta_add, Xo.univ.eta_ker, map_one]
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul hMb Submodule.mem_top
    · show pt x _ = pt x _ * pt x _
      rw [Xo.univ.etaA_add, map_mul]
    · show pt x _ ^ l.A = 1
      rw [← map_pow, ← pow_of_add _ Xo.univ.etaA_add, Xo.univ.etaA_ker, map_one]
  have inj : Function.Injective F := by
    intro x x' h
    simp only [F, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    apply Subtype.ext
    refine GlobalTheory.T.moduli_geometric_point_eq_of_same_fibre_action_level E H Dw l Xo K P x.1 x'.1 (α x) (α x') (x.2.1.trans x'.2.1.symm) (hα x) (hα x') (hL x) (hL x')
      (fun a => ⟨(ρ x).act a, hρ x a, by rw [congrFun h1 a]; exact hρ x' a⟩)
      (fun a => ⟨pt x (Xo.univ.eta a), ObjPull.secPull_left (hα x) _, by
        rw [congrFun h2 a]; exact ObjPull.secPull_left (hα x') _⟩)
      (fun a => ⟨pt x (Xo.univ.etaA a), ObjPull.secPull_left (hα x) _, by
        rw [congrFun h3 a]; exact ObjPull.secPull_left (hα x') _⟩)
  haveI := (hA.prod (hFM.prod hFA)).to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_injective (fun x => (⟨F x, mem x⟩ : ↥(As ×ˢ FM ×ˢ FA)))
    (fun x x' h => inj (congrArg Subtype.val h)))

end GlobalTheory.UMinQF
end
end
end
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryModuli_finite_points_with_given_polarisedFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (s₀ : Sp K ⟶ Sp (KA l)), Set.Finite {x : Sp K ⟶ Xo.X | x ≫ Xo.s = s₀ ∧ ∃ α : P.A.left ⟶ Xo.univ.t.G.left, IsGrpPullback P.A Xo.univ.t.G x α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α)} := by
  atlas_forward_decl GlobalTheory.UMinQF.finite_points
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.QF

theorem polFib_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {K : Type}
    [Field K] {x : Sp K ⟶ S} {P P' : PolAV (Sp K)} (φ : P'.A ≅ P.A) (hφ : IsPolIso P' P φ)
    {α : P.A.left ⟶ G.left} (hα : IsGrpPullback P.A G x α) (hLα : LBIso P.L (L.pull α)) :
    IsGrpPullback P'.A G x (φ.hom.left ≫ α) ∧ LBIso P'.L (L.pull (φ.hom.left ≫ α)) := by
  have := hφ.1
  refine ⟨((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso φ).comp hα).congr (Category.id_comp _) rfl, ?_⟩
  obtain ⟨t, ht⟩ := hφ.2
  have h1 : LBIso P'.L (P.L.pull φ.hom.left) := LBIso.symm ⟨t, ht⟩
  have h2 : LBIso (P.L.pull φ.hom.left) (L.pull (φ.hom.left ≫ α)) :=
    LBIso.chartPull (chartPullPull P.L φ.hom.left)
      (chartPullSame L (fun _ : PUnit => φ.hom.left ≫ α) (fun _ => α) (fun _ => 1) φ.hom.left
        (fun _ => rfl)) hLα
  exact LBIso.trans P'.isLB (pull_isLB P.isLB _) (pull_isLB hL _) h1 h2

theorem charZero_of_pt {F K : Type} [Field F] [CharZero F] [Field K] (t : Sp K ⟶ Sp F) : CharZero K := by
  have f := (Spec.preimage t).hom
  exact (f.charZero_iff f.injective).1 inferInstance

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

def ThetaData (Xo : Moduli Dw l) {K : Type} [Field K] (y : Sp K ⟶ Xo.X) (g m : ℕ) (ze : Γ(Sp K, ⊤)ˣ)
    (v : (Fin (2 * g) → ZMod (m ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) : Prop :=
  ∃ (P : PolAV (Sp K)) (hg : P.g = g) (α : P.A.left ⟶ Xo.univ.t.G.left) (lev : Out.Level P (m ^ 2) ze),
    IsGrpPullback P.A Xo.univ.t.G y α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α) ∧ IsThetaPt P m (levelPoint lev hg) v

theorem finite_thetaData (Xo : Moduli Dw l) (c : Coeff l) (g j : ℕ) (hbig : 81 ^ g * g.factorial < 3 ^ j * 81)
    (K : Type) [Field K] [IsAlgClosed K] (h3 : ((3 : ℕ) : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (x : Sp K ⟶ Xo.XF c)
    (v : (Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) :
    Set.Finite {y : Sp K ⟶ Xo.XF c | y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧
      ThetaData Xo (y ≫ pullback.fst _ _) g (3 ^ j * 81) ze v} := by
  by_cases hne : ∃ y₀ : Sp K ⟶ Xo.XF c, y₀ ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧
      ThetaData Xo (y₀ ≫ pullback.fst _ _) g (3 ^ j * 81) ze v
  · obtain ⟨y₀, -, P₀, hg₀, -, lev₀, -, -, hθ₀⟩ := hne
    have hQ := GlobalTheory.T.unitaryModuli_finite_points_with_given_polarisedFibre E H Dw l Xo K P₀ (x ≫ pullback.fst _ _ ≫ Xo.s)
    refine Set.Finite.of_finite_image (f := fun y => y ≫ pullback.fst _ _) (hQ.subset ?_) ?_
    · rintro _ ⟨y, ⟨hys, P, hg, α, lev, hpb, hPL, hθ⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · show (y ≫ pullback.fst _ _) ≫ Xo.s = x ≫ pullback.fst _ _ ≫ Xo.s
        rw [Category.assoc, pullback.condition, ← Category.assoc, hys, Category.assoc, ← pullback.condition]
      · obtain ⟨φ, hφ, -⟩ := (GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion).1 g 3 2 j 81 (3 ^ j * 81) Nat.prime_three (by decide) le_rfl
          (by norm_num) rfl hbig K h3 P₀ P hg₀ hg ze lev₀ lev v hθ₀ hθ
        exact ⟨φ.hom.left ≫ α, polFib_transport Xo.univ.t.PP.isLB φ hφ hpb hPL⟩
    · intro y₁ h₁ y₂ h₂ h
      exact pullback.hom_ext h (h₁.1.trans h₂.1.symm)
  · convert Set.finite_empty
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hne ⟨y, h⟩

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem exists_thetaData (Xo : Moduli Dw l) (c : Coeff l) {o : Type} [CommRing o] {n j g : ℕ}
    (hg : g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (f : Xo.XF c ⟶ PSpace o n)
    (hn : n + 1 = (3 ^ j * 81) ^ (4 * g))
    (hth : ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f)
    (K : Type) [Field K] [IsAlgClosed K] (hm0 : ((3 ^ j * 81 : ℕ) : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ)
    (hze : IsPrimitiveRoot ze ((3 ^ j * 81) ^ 2)) (x : Sp K ⟶ Xo.XF c) (e : Fin (n + 1) → K)
    (he : PCrd (x ≫ f) e) (T : Finset (Fin (n + 1) → K))
    (hT : ∀ (c : Fin (n + 1) → K) (a : K), a ≠ 0 → (∀ j, symTup c j = a * e j) →
      ∃ mu : K, mu ≠ 0 ∧ (fun b => mu * c b) ∈ T)
    (y : Sp K ⟶ Xo.XF c) (hy : y ≫ f = x ≫ f) :
    ∃ (t : T) (β : (Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Fin (n + 1)),
      ThetaData Xo (y ≫ pullback.fst _ _) g (3 ^ j * 81) ze (fun a => GlobalTheory.ZH.fn ((t : Fin (n + 1) → K) (β a))) := by
  have hodd : Odd (3 ^ j * 81) := (Odd.pow (by decide : Odd 3)).mul (by decide : Odd 81)
  have hLB := Xo.univ.t.PP.isLB
  have hρ := Xo.univ.t.PP.rigGen
  obtain ⟨P, α, hPg, hpb, hPL⟩ := GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c K (y ≫ pullback.fst _ _)
  rw [← hg] at hPg
  have hfib : PolFib Xo.univ.t.G Xo.univ.t.PP.L g (y ≫ pullback.fst _ _) := ⟨P, α, hPg, hpb, hPL⟩
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable _ Xo.univ.t.G Xo.univ.t.PP.L hLB g K _ hfib
  obtain ⟨pt, cy, hcy⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hLB hρ g (3 ^ j * 81) (n + 1) K
    _ θ hodd hm0 hn hfib
  have hH : HasTh Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (y ≫ pullback.fst _ _) cy :=
    ⟨θ, pt, hθ, hcy⟩
  have hP1 : PCrd (y ≫ f) (symTup cy) := hth K y cy hH
  rw [hy] at hP1
  obtain ⟨a, ha0, ha⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend).2.1 o K n (x ≫ f) e (symTup cy) he hP1
  obtain ⟨mu, hmu0, hmuT⟩ := hT cy a ha0 ha
  haveI := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  have hP : HasTh P.A P.L rig (3 ^ j * 81) (𝟙 (Sp K)) cy := by
    rw [hasTh_iff] at hH ⊢
    refine (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hLB hρ (Sp K) P.A P.L rig
      (y ≫ pullback.fst _ _) α P.isLB hrig hpb hPL (3 ^ j * 81) (3 ^ j * 81) (n + 1) (n + 1) K (𝟙 _) cy cy).2 ?_
    rwa [Category.id_comp]
  obtain ⟨lev, β, hβ⟩ := GlobalTheory.T.exists_level_thetaPoint_of_thetaConstants_level_square K P rig g (3 ^ j * 81) (n + 1) hPg cy ze hrig hodd hm0 hze hP
  exact ⟨⟨_, hmuT⟩, β, P, hPg, α, lev, hpb, hPL, hβ mu hmu0⟩

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

theorem finite_fibre_thMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (j n : ℕ) (f : Xo.XF c ⟶ PSpace o n), 81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial < 3 ^ j * 81 → n + 1 = (3 ^ j * 81) ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.XF c), Set.Finite {y : Sp K ⟶ Xo.XF c | y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧ y ≫ f = x ≫ f} := by
  intro E _ _ _ H Dw l Xo c o _ j n f hbig hn hth K _ _ x
  haveI : CharZero K := charZero_of_pt (x ≫ pullback.snd _ _)
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hg
  have hm0 : ((3 ^ j * 81 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have h3 : ((3 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by norm_num)
  have hpos : 0 < (3 ^ j * 81) ^ 2 := by positivity
  haveI : NeZero (((3 ^ j * 81) ^ 2 : ℕ) : K) := ⟨Nat.cast_ne_zero.2 hpos.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ((3 ^ j * 81) ^ 2)
  let eK := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hz' := hz.map_of_injective eK.injective
  set ze : Γ(Sp K, ⊤)ˣ := (hz'.isUnit hpos.ne').unit with hzedef
  have hze : IsPrimitiveRoot ze ((3 ^ j * 81) ^ 2) := hz'.isUnit_unit hpos.ne'
  obtain ⟨⟨e, he⟩, -⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties).2.2 o K n (x ≫ f)
  obtain ⟨T, hT⟩ := GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_scaled_finite K (n + 1) e
  haveI : NeZero ((3 ^ j * 81) ^ 2) := ⟨hpos.ne'⟩
  refine (Set.finite_iUnion fun d : T × ((Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Fin (n + 1)) =>
    finite_thetaData Xo c g j hbig K h3 ze x
      (fun a => GlobalTheory.ZH.fn ((d.1 : Fin (n + 1) → K) (d.2 a)))).subset ?_
  rintro y ⟨h1, h2⟩
  obtain ⟨t, β, hd⟩ := exists_thetaData Xo c hg f hn hth K hm0 ze hze x e he T hT y h2
  exact Set.mem_iUnion.2 ⟨(t, β), h1, hd⟩

end GlobalTheory.UMin.QF
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMap_finite_geometricFibres_of_large_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (j n : ℕ) (f : Xo.XF c ⟶ PSpace o n), 81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial < 3 ^ j * 81 → n + 1 = (3 ^ j * 81) ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.XF c), Set.Finite {y : Sp K ⟶ Xo.XF c | y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧ y ≫ f = x ≫ f} := by
  atlas_forward_decl GlobalTheory.UMin.QF.finite_fibre_thMap
end
