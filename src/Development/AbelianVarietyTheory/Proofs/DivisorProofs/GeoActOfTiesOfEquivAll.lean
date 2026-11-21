import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbedding
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionPreservesIntegralCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvalInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll

section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_action_preserves_integral_cusp_forms : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → ∀ g (f f' : Cu T κ i), (f' : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) → Formalism.IndefR.FWT.IntAll T κ f → Formalism.IndefR.FWT.IntAll T κ f' := by
  first | exact @GlobalTheory.LevActInt.intAll_actLev | exact GlobalTheory.LevActInt.intAll_actLev | (intros; apply GlobalTheory.LevActInt.intAll_actLev <;> assumption)
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.ReadingEquivGood

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem extendByOne_eq_one_of_trivial {M L : Type} [Group M] [Monoid L] (H : Subgroup M) (χ : H → L) (h : ∀ x, χ x = 1) (x : M) :
    Formalism.L2.DIV.ext1 H χ x = 1 := by
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · exact h _
  · rfl

section
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem levChi_flag (i : Fin D.R.m) (k : GA D (Wc D i)) :
    Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) k = 1 := by
  have h2 : Formalism.L2.DIV.ext1 (Lev.flagL (R.datWp i R.triv)).P.H (Lev.flagL (R.datWp i R.triv)).P.chi
      (Formalism.L2.DIV.rTup (R.βW i) (Lev.flagL (R.datWp i R.triv)) (Lev.finE (Wc D i) k)) = 1 := extendByOne_eq_one_of_trivial _ _ (fun _ => rfl) _
  unfold Lev.levChi Formalism.L2.DIV.levFn
  rw [h2]
  show ((1 * (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ ∅, _ : ℂˣ) : ℂ) = 1
  simp

theorem actW_apply {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {g : G}
    (hk : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (x : MMap (R.MW i σ)) (v : (R.MW i σ).Vec)
    (h : GA D (Wc D i)) : actW R i σ g x v h = x v (h * hk.choose) := by
  show Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (x v) h = _
  unfold Lev.actG0
  rw [dif_pos hk]
  simp only [levChi_flag, inv_one, one_mul]

theorem actW_mem (hθ : IsInfFam R.θ) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (g : G) {x : MMap (R.MW i σ)}
    (hx : x ∈ R.Wall i σ) : actW R i σ g x ∈ R.Wall i σ :=
  GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) (R.eG g) x hx _ fun _ => rfl

theorem equiv_of_values (hθ : IsInfFam R.θ) (he : R.models_HW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec}
    (hv : IsUnitV v) {g : G} {x y : (R.HW i σ).H} {c : ℂ}
    (h : ∀ h, evAt R i σ v x h = c * actW R i σ g ((R.HW i σ).e y) v h) :
    (R.HW i σ).e x = c • actW R i σ g ((R.HW i σ).e y) := by
  have hr : LinearMap.range (R.HW i σ).e = R.Wall i σ := (he i σ).2.1
  have h1 : c • actW R i σ g ((R.HW i σ).e y) ∈ LinearMap.range (R.HW i σ).e := by
    rw [hr]
    exact Submodule.smul_mem _ _ (actW_mem R hθ g (hr ▸ LinearMap.mem_range_self _ y))
  obtain ⟨z, hz⟩ := h1
  have h2 : x = z := by
    refine GlobalTheory.EvalAtUnitVector.eval_injective (R.MW i σ) (R.HW i σ).H (R.HW i σ).e _ _ _ (he i σ).2.2 v hv
      (funext fun h' => ?_)
    show (R.HW i σ).e x v h' = (R.HW i σ).e z v h'
    rw [hz]
    exact h h'
  rw [h2, hz]

theorem chiIs_of_values {i : Fin D.R.m} (h1 : ∀ g, ∃ a, D.what₂.embLL a = (chiC R i g : ℂ)) : ChiIs R i (chiTop R i) := by
  choose a ha using h1
  have hne : ∀ g, a g ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 (a g) (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dif_pos hex]
  exact hex.choose_spec

theorem coe_chiC (i : Fin D.R.m) (g : G) : (chiC R i g : ℂ) =
    ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) := by
  rw [chiC, Units.coe_prod]

end

theorem phiC_eq (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    phiC T hV a f h = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * phiAt T i σ hV (T.cE ((i : ℕ) + 1) σ) f h := by
  have key : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W) (g : GA D W), phiC T hV a f g =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
        (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) f)) g := by
    intro W hV g
    subst hV
    rfl
  exact key _ hV h

theorem reading_equivariant : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → (∀ σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → ∀ (ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)), (∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))) → ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρC g f)) = σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hθ he ht i hl hq ρC hρ σ hσ g f
  have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := ht.laws.spaceW _ (inR i) _ hσ
  by_cases hj : JEvAt T R κ v₀ i σ hV
  · have hq' := hq _ hσ hV
    have hc : ChiIs R i (chiTop R i) := chiIs_of_values R fun g' => by
      obtain ⟨-, y, hy, -⟩ := hq' g' _ (hl g').choose_spec 0 (zero_mem _)
      exact ⟨_, hy.trans (coe_chiC R i g').symm⟩
    obtain ⟨-, y, hy, h2⟩ := hq' g _ (hl g).choose_spec (f : T.R ((i : ℕ) + 1)) f.2
    have hy' : ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) = algebraMap T.Q.c.F D.what₂.LL y :=
      D.what₂.embLL.injective ((hc g).trans ((coe_chiC R i g).trans hy.symm))
    have hs : σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) = res T σ y := congrArg σ hy'
    refine equiv_of_values R hθ he (v := v₀ i σ) ((ht.hv₀ i σ).norm R) fun h => ?_
    have e1 := congrFun (jTop_good T R κ v₀ hσ hV hj (ρC g f)) h
    have e2 := congrFun (jTop_good T R κ v₀ hσ hV hj f) (h * (hl g).choose)
    have e3 := actW_apply R (hl g) ((R.HW i σ).e (jTop T R κ v₀ i σ f)) (v₀ i σ) h
    have e4 : phiC T hV (wtA (κ i)) ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) h =
        res T σ y * phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) (h * (hl g).choose) := by
      rw [hρ, phiC_eq, phiC_eq, h2, mul_left_comm]
    exact e1.trans (e4.trans (congrArg₂ (· * ·) hs.symm (e2.symm.trans e3.symm)))
  · rw [jTop_good0 T R κ v₀ hσ hV hj]
    simp

end GlobalTheory.ReadingEquivGood

end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormReading_equivariant_good_embedding : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → (∀ σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → ∀ (ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)), (∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))) → ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρC g f)) = σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f)) := by
  atlas_forward_decl GlobalTheory.ReadingEquivGood.reading_equivariant
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingConjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Model

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

set_option maxHeartbeats 1000000 in

theorem exists_lift_act {i : Fin D.R.m} (σ : D.what₂.LL →+* ℂ) {g : G}
    (hk : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k)
    (hchi : ∀ k, Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) k = 1) :
    ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k ∧
      ∀ (x : MMap (R.MW i σ)) v h, actW R i σ g x v h = x v (h * k) := by
  refine ⟨hk.choose, hk.choose_spec, fun x v h => ?_⟩
  show Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (x v) h = _
  unfold Lev.actG0
  rw [dif_pos hk]
  simp only [hchi, inv_one, one_mul]

set_option maxHeartbeats 1000000 in

theorem exists_act_eq (hθ : IsInfFam R.θ) (he : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) (y : (R.HW i σ).H) :
    ∃ z, (R.HW i σ).e z = actW R i σ g ((R.HW i σ).e y) := by
  have h1 : (R.HW i σ).e y ∈ R.Wall i σ := (he i σ).2.1 ▸ LinearMap.mem_range_self _ y
  have h2 : actW R i σ g ((R.HW i σ).e y) ∈ R.Wall i σ :=
    GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) (R.eG g) _ h1 _ fun _ => rfl
  rw [← (he i σ).2.1] at h2
  exact h2

set_option maxHeartbeats 1000000 in

theorem equiv_of_values (hθ : IsInfFam R.θ) (he : R.models_HW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec}
    (hv : IsUnitV v) {g : G} {k : GA D (Wc D i)} (hk : ∀ (x : MMap (R.MW i σ)) v h, actW R i σ g x v h = x v (h * k))
    {x y : (R.HW i σ).H} {c : ℂ} (h : ∀ h, evAt R i σ v x h = c * evAt R i σ v y (h * k)) :
    (R.HW i σ).e x = c • actW R i σ g ((R.HW i σ).e y) := by
  obtain ⟨z, hz⟩ := exists_act_eq R hθ he i σ g y
  have h4 : (R.HW i σ).e (c • z) = c • actW R i σ g ((R.HW i σ).e y) := by
    rw [← hz]; exact (R.HW i σ).e.map_smul _ _
  have h3 : x = c • z := by
    refine GlobalTheory.EvalAtUnitVector.eval_injective (R.MW i σ) (R.HW i σ).H (R.HW i σ).e _ _ _ (he i σ).2.2 v hv (funext fun h' => ?_)
    show (R.HW i σ).e x v h' = (R.HW i σ).e (c • z) v h'
    rw [h4]
    exact (h h').trans (congrArg (c * ·) (hk _ v h').symm)
  exact (congrArg (R.HW i σ).e h3).trans h4

theorem chiTop_eq {i : Fin D.R.m} (h1 : ∀ g, ∃ a, D.what₂.embLL a = (chiC R i g : ℂ)) : ChiIs R i (chiTop R i) := by
  choose a ha using h1
  have hne : ∀ g, a g ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 (a g) (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dif_pos hex]
  exact hex.choose_spec

end Model

set_option maxHeartbeats 1000000 in

theorem reading_equiv_of_not_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → (∀ σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → ∀ (ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)), (∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))) → ∀ σ : D.what₂.LL →+* ℂ, ¬ GoodEmb T.Q.c (res T σ) → ∀ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρC g f)) = σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hθ he ht i hl hq ρC hρ σ hσ g f
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := ht.laws.spaceW _ (inR i) _ (good_resC T hσ)
  by_cases hj : JEvBarAt T R κ i σ hV
  swap
  · rw [top_lift_vanishes_off_good_embeddings T R κ v₀ hσ hV hj]
    simp
  obtain ⟨v, hv, h5⟩ := jTop_bar T R κ v₀ hσ hV hj
  have hE := hq _ (good_resC T hσ) hV
  have hchi : ChiIs R i (chiTop R i) := chiTop_eq R fun g' => by
    obtain ⟨k, hk⟩ := hl g'
    obtain ⟨-, y, hy, -⟩ := hE g' k hk 0 (zero_mem _)
    exact ⟨_, by rw [chiC, Units.coe_prod]; exact hy⟩
  obtain ⟨k, hk1, hk2⟩ := exists_lift_act R σ (hl g) (GlobalTheory.TiedUnif.levChi_flag_datWp i)
  obtain ⟨-, y, hy, h2⟩ := hE g k hk1 f f.2
  have hy' : ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) = algebraMap T.Q.c.F D.what₂.LL y :=
    D.what₂.embLL.injective ((hchi g).trans (by rw [chiC, Units.coe_prod]; exact hy.symm))
  refine equiv_of_values R hθ he hv hk2 fun h => ?_
  rw [h5, h5]
  show starRingEnd ℂ _ = _ * starRingEnd ℂ _
  rw [hρ, GlobalTheory.TiedUnif.phiC_eq_phiAt, GlobalTheory.TiedUnif.phiC_eq_phiAt, h2, mul_left_comm, hy', map_mul]
  exact congrArg (· * _) (Complex.conj_conj _)

end GlobalTheory.ReadingConjEquiv

end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormReading_equivariant_not_good_embedding : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → (∀ σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → ∀ (ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)), (∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))) → ∀ σ : D.what₂.LL →+* ℂ, ¬ GoodEmb T.Q.c (res T σ) → ∀ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρC g f)) = σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f)) := by
  atlas_forward_decl GlobalTheory.ReadingConjEquiv.reading_equiv_of_not_good
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.geoAct_of_eqAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → (∀ i σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → GeoAct T R κ v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hθ hm ht hp he i
  have hact : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (O i).lev2 := (hp i).2.act.1
  have hlift : ∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k := fun g =>
    ((hp i).2.lift.lev g).imp fun _ h => h.1
  have hs : GoodEmb T.Q.c (O i).s0 := by
    have e : (O i).s0 = T.toCore.σ₀ := sOv_eq T.toCore (O i).c' (O i).hle
    rw [e]
    exact T.toCore.good_σ₀
  obtain ⟨ρC, hρ⟩ := GlobalTheory.T.exists_level_action_cusp_form_representation T κ i (O i).lev2 ht.laws hact
    (fun g f hf => (hlift g).elim fun k hk =>
      (he i (O i).s0 hs (O i).hV g k hk f hf).1)
  refine ⟨ρC, fun σ g f => ?_, fun g f hf => ?_⟩
  · by_cases hσ : GoodEmb T.Q.c (res T σ)
    · exact GlobalTheory.T.cuspFormReading_equivariant_good_embedding T R κ v₀ O hθ hm ht i hlift (he i) ρC hρ σ hσ g f
    · exact GlobalTheory.T.cuspFormReading_equivariant_not_good_embedding T R κ v₀ O hθ hm ht i hlift (he i) ρC hρ σ hσ g f
  · exact GlobalTheory.T.level_action_preserves_integral_cusp_forms T κ i (O i).lev2 ht.laws hact g f (ρC g f) (hρ g f) hf
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricAction_coveringGroup_of_core_equivariance : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → (∀ i σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → GeoAct T R κ v₀ := by
  atlas_forward_decl GlobalTheory.geoAct_of_eqAt
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

set_option maxHeartbeats 1000000 in

theorem geoAct_of_ties_of_equivAll : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → EquivAll T R κ O → GeoAct T R κ v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hl hi hw ht hpb hp he
  exact GlobalTheory.T.geometricAction_coveringGroup_of_core_equivariance T R κ v₀ O hi hw ht hp fun i σ hσ hV =>
    he i σ hσ hV (GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R κ v₀ O hl ht hpb hp i σ hσ hV)

end GlobalTheory
end
