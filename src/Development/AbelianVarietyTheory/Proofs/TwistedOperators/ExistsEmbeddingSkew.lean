module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.CuspL2

theorem exists_toLp_ext {G : Type} [MeasurableSpace G] (ν : Measure G) :
    ∃ E : (G → ℂ) →ₗ[ℂ] Lp ℂ 2 ν, ∀ φ, MemLp φ 2 ν → E φ =ᵐ[ν] φ := by
  classical
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {φ | MemLp φ 2 ν}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := by
        first
          | exact MemLp.zero
      smul_mem' := fun c _ h => h.const_smul c }
  let f : S →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun φ => MemLp.toLp (φ : G → ℂ) φ.2
      map_add' := fun φ ψ => MemLp.toLp_add φ.2 ψ.2
      map_smul' := fun c φ => MemLp.toLp_const_smul c φ.2 }
  obtain ⟨E, hE⟩ := LinearMap.exists_extend f
  refine ⟨E, fun φ hφ => ?_⟩
  have hval : E φ = f ⟨φ, hφ⟩ := LinearMap.congr_fun hE ⟨φ, hφ⟩
  rw [hval]
  exact MemLp.coeFn_toLp hφ

theorem inner_eq {G : Type} [MeasurableSpace G] {ν : Measure G} {f f' : Lp ℂ 2 ν} {φ φ' : G → ℂ}
    (h : f =ᵐ[ν] φ) (h' : f' =ᵐ[ν] φ') : ⟪f, f'⟫_ℂ = ∫ g, (starRingEnd ℂ) (φ g) * φ' g ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h, h'] with g hg hg'
  rw [hg, hg']
  first
    | (rw [RCLike.inner_apply]; try ring)

theorem conj_mul {G : Type} [TopologicalSpace G] {φ φ' : G → ℂ} (c : Continuous φ) (c' : Continuous φ')
    (b : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B) (b' : ∃ B : ℝ, ∀ g, ‖φ' g‖ ≤ B) :
    Continuous (fun g => (starRingEnd ℂ) (φ g) * φ' g) ∧ ∃ B : ℝ, ∀ g, ‖(starRingEnd ℂ) (φ g) * φ' g‖ ≤ B := by
  obtain ⟨B, hB⟩ := b
  obtain ⟨B', hB'⟩ := b'
  refine ⟨(Complex.continuous_conj.comp c).mul c', max B 0 * max B' 0, fun g => ?_⟩
  calc ‖(starRingEnd ℂ) (φ g) * φ' g‖ = ‖φ g‖ * ‖φ' g‖ := by simp
    _ ≤ max B 0 * max B' 0 :=
      mul_le_mul ((hB g).trans (le_max_left _ _)) ((hB' g).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)

end GlobalTheory.Chain.CuspL2

end
