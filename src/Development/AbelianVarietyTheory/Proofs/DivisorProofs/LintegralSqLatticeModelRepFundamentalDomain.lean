module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantMeanSquareForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwiner
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantThetaMeanSquareForm, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqLatticeModelRepFundamentalDomain

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantThetaMeanSquareForm =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantThetaMeanSquareForm", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Formalism.LocalToGlobal.IndefiniteReal.DatumF\npublic import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars\npublic import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantMeanSquareForm\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa\nimport Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.ThetaMeanSquareF

theorem exists_invariant_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ M : Submodule ℂ (WOF F E nS nT → ℂ), (∀ f ∈ M, IsThetaFunOF σ JS JT ξ₀ B.ψ f) →
      ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ →
        ∃ Bf : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WOF F E nS nT) (f g f' g' : M),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u f → (g' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u g →
            Bf f' g' = Bf f g) ∧
          ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (Bf f f).re := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ M hM μ 𝓕 hμ h𝓕
  have hψ : IsCharAF F B.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := countable_of_discrete_addSubgroup _
  haveI := hμ
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hb : ∀ f ∈ M, ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := fun f hf => by
    have hp : ∀ γ ∈ ratLF F E nS nT, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm ((hM f hf).quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hM f hf).cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  obtain ⟨Bf, hBf, hN⟩ := GlobalTheory.ThetaMeanSquareForm.exists_form (μ.restrict 𝓕) M
    (fun f hf => (hM f hf).cont.measurable) hb
  refine ⟨Bf, fun u f g f' g' hf hg => ?_, hN⟩
  rw [hBf, hBf, hf, hg]
  have key := GlobalTheory.HeisOrtho.setIntegral_add_right (G := WOF F E nS nT) (ratLF F E nS nT) μ 𝓕 h𝓕
    (fun w => (f : WOF F E nS nT → ℂ) w * (starRingEnd ℂ) ((g : WOF F E nS nT → ℂ) w)) (by
      rintro _ ⟨γ, rfl⟩ w
      have h0 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.2.1 (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)))
      have h1 := (hM f f.2).quasi γ w
      have h2 := (hM g g.2).quasi γ w
      show (f : WOF F E nS nT → ℂ) (ratWF γ + w) * (starRingEnd ℂ) ((g : WOF F E nS nT → ℂ) (ratWF γ + w)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]) u
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have h0 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.2.1 (symplOHF σ JS JT ξ₀ w u))
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * (f : WOF F E nS nT → ℂ) (w + u) *
    (starRingEnd ℂ) (B.ψ (symplOHF σ JS JT ξ₀ w u) * (g : WOF F E nS nT → ℂ) (w + u)) = _
  rw [map_mul, mul_mul_mul_comm, h0, one_mul]

end GlobalTheory.ThetaMeanSquareF

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantThetaMeanSquareForm =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqLatticeModelRepFundamentalDomain =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqLatticeModelRepFundamentalDomain", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Formalism.LocalToGlobal.IndefiniteReal.DatumF\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantThetaMeanSquareForm\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial\npublic import Mathlib.Algebra.Algebra.Basic\npublic import Mathlib.Algebra.Module.LinearMap.Star\npublic import Mathlib.Analysis.Complex.Norm\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwiner\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatUnitF

open GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have h1 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hS.2)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact GlobalTheory.SymplOInv.sum_unitary (cAF σ) (JT.map (incAF F E)) (mtF σ JT h) (JS⁻¹.map (incAF F E))
    (JS.map (incAF F E)) (mtF σ JS g⁻¹) h1 h.2 (g⁻¹).2 x y

theorem gamFF_rhoFF (hS : IsHermND σ JS) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (p : GAF σ JS × GAF σ JT)
    (x y : XFF F E nS nT) :
    gamFF σ JS JT ξ₀ ψ (rhoFF σ JS JT p x) (rhoFF σ JS JT p y) = gamFF σ JS JT ξ₀ ψ x y := by
  unfold gamFF
  rw [coe_rhoFF, coe_rhoFF]
  unfold symplOF
  rw [hOF_actOF hS]

alias sigma_sigma := _root_.GlobalTheory.AdelicU.cm_conj_conj

theorem lintegral_sq_Om : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f,
            ∫⁻ w in 𝓕, ‖(Om p f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξ hc Λ w lam Om h μ 𝓕 hμ h𝓕 p f
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hB.cm
  have hn : ∀ a, ‖B.ψ a‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hB.std
  obtain ⟨Bf, hB1, hB2⟩ := _root_.GlobalTheory.ThetaMeanSquareF.exists_invariant_form F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξ
    (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ) (fun _ hf => hf) μ 𝓕 hμ h𝓕
  rw [hB2, hB2, _root_.GlobalTheory.FinWeil.invForm_intertwiner (isHeis_opFF hσ hS hT hξ hc h.hw) (fun x y => hn _) lam h.good _ h.sd h.span
    (rhoFF σ JS JT p) (gamFF_rhoFF hS ξ₀ B.ψ p) (h.sd' p) (h.fin p) (Om p) (h.op p) (h.vac p) Bf]
  intro x u v
  have h1 : ∀ u : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, opFF hc w x u =
      phaseF σ JS JT ξ₀ B.ψ w x • (⟨heisOF σ JS JT ξ₀ B.ψ x u, hc x u u.2⟩ : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ) :=
    fun u => rfl
  have h2 : phaseF σ JS JT ξ₀ B.ψ w x * (starRingEnd ℂ) (phaseF σ JS JT ξ₀ B.ψ w x) = 1 := by
    rw [Complex.mul_conj', show ‖phaseF σ JS JT ξ₀ B.ψ w x‖ = 1 from hn _]; simp
  rw [h1, h1, Bf.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_smul, h2, one_smul]
  exact hB1 x u v _ _ rfl rfl

end GlobalTheory.FinLatUnitF

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqLatticeModelRepFundamentalDomain =====
