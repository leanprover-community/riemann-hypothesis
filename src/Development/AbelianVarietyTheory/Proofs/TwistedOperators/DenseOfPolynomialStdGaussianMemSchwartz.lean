import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrChInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MvZOneEqMapUnivSubst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvalAtJetMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerMovedVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC

section
section
open Formalism.BasicNotions Formalism.L2.DIV MeasureTheory
open scoped Matrix

noncomputable section
open MvPolynomial GlobalTheory.KJInf

namespace GlobalTheory.AvgJet

variable {ι : Type} [Fintype ι]

def evalL {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) : PY ι a →ₗ[ℂ] ℂ where
  toFun := evalAt y
  map_add' F G := by simp [evalAt]
  map_smul' c F := by simp [evalAt, smul_eval]

theorem evalL_apply {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) : evalL y F = evalAt y F := rfl

theorem dual_eq_sum_evalAt {a : ℕ} (V : Submodule ℂ (PY ι a)) [FiniteDimensional ℂ V]
    (hsep : ∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) (Λ : Module.Dual ℂ V) :
    ∃ (S : Finset {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y}) (c : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} → ℂ),
      ∀ v : V, Λ v = ∑ y ∈ S, c y * evalAt y.1 (v : PY ι a) := by
  set E : Submodule ℂ (Module.Dual ℂ V) := Submodule.span ℂ
    (Set.range fun y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} => (evalL y.1).comp V.subtype) with hE
  have hco : E.dualCoannihilator = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    rw [Submodule.mem_dualCoannihilator] at hv
    have h0 : (v : PY ι a) = 0 := hsep _ fun y hy => hv _ (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
    exact Subtype.ext h0
  have htop : E = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := E), hco, Submodule.dualAnnihilator_bot]
  have hΛ : Λ ∈ E := htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hΛ
  refine ⟨c.support, c, fun v => ?_⟩
  rw [← hc, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, evalL_apply, smul_eq_mul]

theorem evalAt_rhoK {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (G : VV ℂ lam)
    (Y : ι → Matrix (Fin n) (Fin n) ℂ) :
    evalAt Y ((rhoK lam (invTrK g⁻¹) G : VV ℂ lam) : PY ι n) =
      (∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift) *
        evalAt (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Y τ) (G : PY ι n) := by
  have htr : trAct (invTrK g⁻¹) = lft (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
    unfold trAct lft Formalism.GradedWeylDivisibility.blockAct
    congr 1
  have hdet : detTwK lam (invTrK g⁻¹) =
      ∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift := by
    unfold detTwK
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [detPow, invTrK, inside₂, Units.val_zpow_eq_zpow_val]
  show evalAt Y (actP lam (invTrK g⁻¹) G) = _
  rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, htr, hdet]
  rw [evalAt, smul_eval, ← evalAt, evalAt_lft]

theorem integrable_term {a b : ℕ} {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
    [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν] {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r)
    (Λ : FP ι a b →ₗ[ℂ] ℂ) (Q : FP ι a b) (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Integrable (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) Q) * evalAt (fun τ => r k τ * y τ) F) ν := by
  set U := GlobalTheory.KJAvg.univSubst Q with hU
  set p : PY ι a := ∑ m ∈ U.support, C (Λ (monomial m 1)) * coeff m U with hp'
  have hp : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, Λ (mvZ g (fun _ => 1) Q) = eval (fun w => g w.1 w.2.1 w.2.2) p := by
    intro g
    rw [GlobalTheory.KJAvg.mvZ_one_eq_map_univSubst, GlobalTheory.KJAvg.linear_eq_sum_coeff Λ U.support _ (support_map_subset _ _)]
    simp only [hp', map_sum, map_mul, eval_C, coeff_map]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have e : (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) Q) * evalAt (fun τ => r k τ * y τ) F) =
      fun k => eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) p * evalAt (fun τ => r k τ * y τ) F := by
    funext k
    rw [hp]
    simp only [GlobalTheory.KJAvg.ontoUni_inv hr]
  rw [e]
  exact GlobalTheory.KJAvg.integrable_avg_term ν hr p y F

end GlobalTheory.AvgJet

open GlobalTheory.AvgJet in

theorem GlobalTheory.AvgJet.avg_jet : ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b → 0 < a → ∀ (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (nn : ι → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' nn → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (r : K →* (ι → GL (Fin a) ℂ)), GlobalTheory.KJInf.OntoUni (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) →
    ∀ (Q : MvPolynomial (ι × Fin b × Fin a) ℂ) (Λ : Module.Dual ℂ (VV ℂ lam)), ∃ Λ' : Module.Dual ℂ (VV ℂ lam'),
    ∀ (ℓ : MvPolynomial (ι × Fin b × Fin a) ℂ →ₗ[ℂ] ℂ) (h : ι → GL (Fin b) ℂ) (v : VV ℂ lam),
      ∫ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) ∂ν =
        Λ' (rhoK lam' (invTrK h⁻¹) (Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v)) := by
  intro ι _ a b hab ha lam lam' nn hJ K _ _ _ _ _ ν _ _ r hr Q Λ
  classical
  obtain ⟨-, hcomp, -, -, -, -, hsep, -⟩ := GlobalTheory.T.fockSubstitution_identities ι a b hab
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  obtain ⟨S, c, hΛ⟩ := dual_eq_sum_evalAt (VV ℂ lam) hsep Λ
  have hav := fun y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} =>
    GlobalTheory.KJAvg.avg_span ι a b hab ha lam nn K ν (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) hr y.1 Q
  choose m y' s hinv hspan using hav
  let d : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} → ℂ := fun y => (∏ τ, (y.1 τ).det ^ nn τ)⁻¹
  refine ⟨∑ y ∈ S, (c y * d y) • ∑ j, s y j • (evalL (y' y j)).comp (VV ℂ lam').subtype, fun ℓ h v => ?_⟩
  let hh : ι → Matrix (Fin b) (Fin b) ℂ := fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ)
  let Hh : ℂ := ∏ τ, (hh τ).det ^ (lam' τ).detShift
  let ℓ₀ : FP ι a b →ₗ[ℂ] ℂ := ℓ ∘ₗ (mvZ (fun _ => 1) hh).toLinearMap
  let F : PY ι a := (v : PY ι a) * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ nn τ
  have hFV : F ∈ Vn lam nn := ⟨v, (GlobalTheory.KJInf.ClsVal.cSpan_eq_VV' lam).symm ▸ v.2, rfl⟩

  have hpt : ∀ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) =
        Hh * ∑ y ∈ S, c y * d y * (ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F) := by
    intro k
    have hsub : GlobalTheory.CompactHowe.substF hh (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q =
        mvZ (fun _ => 1) hh (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) := by
      rw [hcomp]
      simp only [mul_one, one_mul, Matrix.coe_units_inv]
      rfl
    rw [map_inv r k, hΛ]
    simp only [evalAt_rhoK]
    rw [hsub]
    set L := ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) with hL
    have hL' : ℓ (mvZ (fun _ => 1) hh (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q)) = L := rfl
    have hH : (∏ τ, ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) = Hh := rfl
    rw [hL', Finset.prod_mul_distrib, hH, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hdet : ∀ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := fun τ => (Matrix.isUnits_det_units _).ne_zero
    have key : (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift)) *
        (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ (lam τ).detShift) =
        ∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [← zpow_add₀ (hdet τ), sub_add_cancel, zpow_natCast]
    have hdy : d y * ∏ τ, (y.1 τ).det ^ nn τ = 1 :=
      inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (y.2 τ).ne_zero)
    have hF : evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F =
        evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a) *
          ((∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ) * ∏ τ, (y.1 τ).det ^ nn τ) := by
      rw [GlobalTheory.KJInf.ValPol.evalAt_mul_prod, ← Finset.prod_mul_distrib]
      simp only [Matrix.det_mul, mul_pow]
    rw [hF]
    linear_combination (Hh * L * c y * evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a)) * key -
      (Hh * L * c y * evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a) *
        ∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ) * hdy
  have hint : ∀ y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y}, Integrable (fun k => c y * d y *
      (ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F)) ν :=
    fun y => (integrable_term ν hr ℓ₀ Q y.1 F).const_mul _
  have hjet : ((Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v : VV ℂ lam') : PY ι b) =
      Formalism.L2.Ker.jetMap (fun m => ℓ (MvPolynomial.monomial m 1)) nn (v : PY ι a) := by
    have hx : Formalism.L2.Ker.jetMap (fun m => ℓ (MvPolynomial.monomial m 1)) nn (v : PY ι a) =
        ((⟨_, hJ _ _ v.2⟩ : VV ℂ lam') : PY ι b) := rfl
    simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.retrVV, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hx, Submodule.projectionOnto_apply_left]
  have hav' : ∀ y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y},
      ∫ k, ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F ∂ν =
        ∑ j, s y j * ℓ (subY hab (fun τ => hh τ * y' y j τ) F) := by
    intro y
    rw [hspan y F hFV ℓ₀]
    refine Finset.sum_congr rfl fun j _ => ?_
    show s y j * ℓ (mvZ (fun _ => 1) hh (subY hab (y' y j) F)) = _
    rw [mvZ_subY]
  have hH : (∏ τ, ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) = Hh := rfl
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun y _ => hint y]
  simp only [integral_const_mul, hav']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, evalL_apply,
    smul_eq_mul, evalAt_rhoK, hjet, GlobalTheory.KJInf.ClsVal.evalAt_jetMap hab, hH]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end
end

open Formalism.BasicNotions Formalism.L2.DIV MeasureTheory
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitaryAverage_fockPolynomial_jetFunctional : ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b → 0 < a → ∀ (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (nn : ι → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' nn → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (r : K →* (ι → GL (Fin a) ℂ)), GlobalTheory.KJInf.OntoUni (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) →
    ∀ (Q : MvPolynomial (ι × Fin b × Fin a) ℂ) (Λ : Module.Dual ℂ (VV ℂ lam)), ∃ Λ' : Module.Dual ℂ (VV ℂ lam'),
    ∀ (ℓ : MvPolynomial (ι × Fin b × Fin a) ℂ →ₗ[ℂ] ℂ) (h : ι → GL (Fin b) ℂ) (v : VV ℂ lam),
      ∫ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) ∂ν =
        Λ' (rhoK lam' (invTrK h⁻¹) (Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v)) := by
  atlas_forward_decl GlobalTheory.AvgJet.avg_jet
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest

theorem realPts_ontoUni_haar_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j ≤ D.R.m →
    GlobalTheory.KJInf.OntoUni (fun (k : GinfC (G.V (.top j))) τ =>
      ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
        Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) ∧
    ∀ κ κ' : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ → κ'.IsHaarMeasure →
      IsProbabilityMeasure κ' → κ = κ' := by
  intro D T L sc G W U S μ0 _ j hj
  have hX : DefNode D.R.m (Node.top j) := hj
  have hO := GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.top j)) (S.N.frC _) W.θ_is (GlobalTheory.RealType.frC_on S.N hX)
  refine ⟨?_, ?_⟩
  · have e : (fun (k : GinfC (G.V (.top j))) τ =>
        ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
          Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) =
        fun k : GinfC (G.V (.top j)) => GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (S.N.frC (.top j)) k.1 :=
      funext fun k => funext fun τ => GlobalTheory.RowHoweAvg.realIn_coe W.θ S.N _ _ τ
    rw [e]
    exact hO
  · intro κ κ' h1 h2 h3 h4
    haveI : LocallyCompactSpace (GinfC (G.V (.top j))) :=
      (GlobalTheory.AdelicSplit.isClosed_GinfC' _).locallyCompactSpace
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure κ κ'

end GlobalTheory.RowTest
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_topNode_onto_unitary_haar_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j ≤ D.R.m →
    GlobalTheory.KJInf.OntoUni (fun (k : GinfC (G.V (.top j))) τ =>
      ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
        Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) ∧
    ∀ κ κ' : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ → κ'.IsHaarMeasure →
      IsProbabilityMeasure κ' → κ = κ' := by
  atlas_forward_decl GlobalTheory.RowTest.realPts_ontoUni_haar_unique
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnArrowKernel_real_eq_detChar_mul_fockKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (x : FinPt G (.top j)) (k : GA D (G.V (.top j))),
    k ∈ GinfC (G.V (.top j)) → ∀ (h : GA D (G.V (.top (j + 1)))),
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * k) h =
        (∏ τ, ((realIn W.θ S.N.fr (.top j) k τ : GL (Fin (G.V (.top j)).rank) ℂ) :
              Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^
                ((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift) *
            ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
              Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ (wt G (.top (j + 1)) τ).detShift) *
          W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j
            (GlobalTheory.CompactHowe.substF
              (fun τ => ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
                Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
              (fun τ => (((realIn W.θ S.N.fr (.top j) k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) :
                Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ)
              (GlobalTheory.AvgCol.frChInv W S.N j Q))))
            (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))) := by
  first | exact @GlobalTheory.ColKer.kerA_col_mul_real | exact GlobalTheory.ColKer.kerA_col_mul_real | (intros; apply GlobalTheory.ColKer.kerA_col_mul_real <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.AvgColJet

theorem fockIn_frC {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T} (hL : L.Is μ0)
    (W : G.Weil) {U : Set T} (N : Std G U) (t : T) (j : ℕ) (hj : j < D.R.m)
    (f : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (hf : IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) f)
    (Q : PolF D (G.pT (.top t j)).rank (G.pS (.top t j)).rank) :
    fockIn W N.frC (.top t j) f Q = W.fock (.top t j) f (AvgCol.frCh W N j Q) := by
  have hn : DefNode D.R.m (.top j) ∧ DefNode D.R.m (.top (j + 1)) :=
    ⟨show j ≤ D.R.m by omega, show j + 1 ≤ D.R.m by omega⟩
  have c1 : W.cart (.top j) = fun _ => 1 := funext (GlobalTheory.FockReal.cart_def hL W hn.1)
  have c2 : W.cart (.top (j + 1)) = fun _ => 1 := funext (GlobalTheory.FockReal.cart_def hL W hn.2)
  have e : ∀ X, DefNode D.R.m X → N.frC X = fun τ => W.onb X τ * AvgCol.frRel W N X τ := by
    intro X hX
    funext τ
    have hu : IsUnit (W.onb X τ).det := Matrix.isUnit_det_of_left_inverse (GlobalTheory.FockReal.onb_def hL W hX τ)
    rw [AvgCol.frRel, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  simp only [fockIn, GridData.Weil.fock, GridData.cartS, GridData.onT, GridData.onS, c1, c2, e _ hn.1, e _ hn.2]
  rw [GlobalTheory.FockBaseChange.pureTensorO_subst D W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ f hf]
  rfl

theorem fockComp_frC_eq_jetOp : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (x : FinPt G (.top j)) (y : FinPt G (.top (j + 1))),
      fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (y * S.N.u _) =
        Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1)))
          (fun m => W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j (MvPolynomial.monomial m 1)))
            (x : GA D (G.V (.top j))) (y : GA D (G.V (.top (j + 1)))))
          (nuEnd G (.top t j)) := by
  intro D T L sc G W U S μ0 hL j hj t d hd x y
  have hp : DefPair D.R.m (Pair.top t j : Pair T) := show j + 1 ≤ D.R.m by omega
  have hf := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd).1
  unfold fockComp
  refine congrArg (fun F => Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1))) F (nuEnd G (.top t j))) (funext fun m => ?_)
  unfold jetTab kerFin
  have hid : m.mapDomain (fvar G (.top t j)) = m := Finsupp.mapDomain_id
  rw [hid, Subgroup.coe_mul, Subgroup.coe_mul, GlobalTheory.FockReal.ker_mul, fockIn_frC hL W S.N t j hj _ hf]
  congr 1
  exact GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om (.top t j)) (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega))
    W.θ W.θ_is _ (S.N.u _).2 _ (S.N.u _).2 _ _ _ _ _ _ hf

end GlobalTheory.AvgColJet
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockComponent_transportedPoints_eq_jetOperator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (x : FinPt G (.top j)) (y : FinPt G (.top (j + 1))),
      fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (y * S.N.u _) =
        Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1)))
          (fun m => W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j (MvPolynomial.monomial m 1)))
            (x : GA D (G.V (.top j))) (y : GA D (G.V (.top (j + 1)))))
          (nuEnd G (.top t j)) := by
  atlas_forward_decl GlobalTheory.AvgColJet.fockComp_frC_eq_jetOp
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.AvgCol

theorem avg_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top j)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.top (j + 1)))), ∀ t ∈ U, ∀ d : FinDatum G t (.top t j), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.top j)) (h : GA D (G.V (.top (j + 1)))) (v : VV ℂ (wt G (.top j))),
        ∫ k, W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.top (j + 1)) h⁻¹
            (fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (finOf _ h * S.N.u _) v)) := by
  intro D T L sc G W U S μ0 hL j hj Q Λ
  obtain ⟨hr, huniq⟩ := GlobalTheory.T.realPoints_topNode_onto_unitary_haar_unique S hL j hj.le
  let r : GinfC (G.V (.top j)) →* (D.what₂.Tau → GL (Fin (G.V (.top j)).rank) ℂ) :=
    (realIn W.θ S.N.fr (.top j)).comp (GinfC (G.V (.top j))).subtype
  have hrk : (G.V (.top j)).rank ≤ (G.V (.top (j + 1))).rank ∧ 0 < (G.V (.top j)).rank := by
    rw [(node_isV G hL (X := .top j) (show j ≤ D.R.m by omega)).rank,
      (node_isV G hL (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)).rank]
    simp only [Node.rank, rankX, rankP, nRk]
    constructor
    · nlinarith
    · omega
  obtain ⟨hab, ha⟩ := hrk
  have hJ : Formalism.L2.Ker.JetInVV ℂ (wt G (.top j)) (wt G (.top (j + 1))) (nuEnd G (.top μ0 j)) :=
    (wtOK_of_defPair G (.top μ0 j) (show j + 1 ≤ D.R.m from hj)).2
  by_cases hex : ∃ κ₀ : Measure (GinfC (G.V (.top j))), κ₀.IsHaarMeasure ∧ IsProbabilityMeasure κ₀
  · obtain ⟨κ₀, h1, h2⟩ := hex
    haveI := h1
    haveI := h2
    obtain ⟨Λ', hΛ'⟩ := GlobalTheory.T.compactUnitaryAverage_fockPolynomial_jetFunctional D.what₂.Tau _ _ hab ha (wt G (.top j)) (wt G (.top (j + 1))) (nuEnd G (.top μ0 j)) hJ
      (GinfC (G.V (.top j))) κ₀ r hr (frChInv W S.N j Q) Λ
    refine ⟨Λ', fun t ht d hd κ hκ hκp x h v => ?_⟩
    obtain rfl := huniq κ κ₀ hκ hκp h1 h2
    let ℓ : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₗ[ℂ] ℂ :=
      (LinearMap.proj (R := ℂ) (φ := fun _ : WO (G.pS (.top t j)) (G.pT (.top t j)) => ℂ) 0).comp
        ((W.om (.top t j) (G.toPair (.top t j) (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))))).comp
          ((W.fock (.top t j) (movedVec t S d)).comp (frCh W S.N j).toLinearMap))
    have hℓ : ∀ P, ℓ P = W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (frCh W S.N j P))
        (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))) := fun P => rfl
    have e1 : ∀ k : GinfC (G.V (.top j)),
        W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j))))⁻¹ v) =
          (∏ τ, ((r k τ : GL (Fin (G.V (.top j)).rank) ℂ) : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^ ((nuEnd G (.top μ0 j) τ : ℤ) - (wt G (.top j) τ).detShift) *
              ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ (wt G (.top (j + 1)) τ).detShift) *
            ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
              (fun τ => (((r k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ) (frChInv W S.N j Q)) *
            Λ (rhoK (wt G (.top j)) (invTrK (r k⁻¹)) v) := by
      intro k
      rw [GlobalTheory.T.columnArrowKernel_real_eq_detChar_mul_fockKernel S hL j hj t d hd Q x k k.2 h, hℓ]
      rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall e1), hΛ' ℓ (realIn W.θ S.N.fr (.top (j + 1)) h) v,
      GlobalTheory.T.fockComponent_transportedPoints_eq_jetOperator S hL j hj t d hd x (finOf _ h)]
    have e2 : realAct W.θ S.N.fr (.top (j + 1)) h⁻¹ =
        rhoK (wt G (.top (j + 1))) (invTrK (realIn W.θ S.N.fr (.top (j + 1)) h)⁻¹) := by
      simp only [realAct, MonoidHom.comp_apply, map_inv]
    rw [e2]
    rfl
  · exact ⟨0, fun t _ d _ κ hκ hκp => absurd ⟨κ, hκ, hκp⟩ hex⟩

end GlobalTheory.AvgCol

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_integral_arrowKernel_fock_eq_fockComp_top : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top j)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.top (j + 1)))), ∀ t ∈ U, ∀ d : FinDatum G t (.top t j), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.top j)) (h : GA D (G.V (.top (j + 1)))) (v : VV ℂ (wt G (.top j))),
        ∫ k, W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.top (j + 1)) h⁻¹
            (fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (finOf _ h * S.N.u _) v)) := by
  atlas_forward_decl GlobalTheory.AvgCol.avg_col
end
