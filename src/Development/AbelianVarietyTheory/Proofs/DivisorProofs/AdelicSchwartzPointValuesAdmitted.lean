module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoRows

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

namespace GlobalTheory.TowU.PointVal

theorem adelicSchwartz_pointValues_admitted_alt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], (∀ x : κ → AF F, (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ) ∧ (∃ φ ∈ schA F κ, φ 0 = 1) ∧ (∀ w, ∀ φ ∈ schA F κ, schr ψ w φ ∈ schA F κ) ∧ ∀ (w w' : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ), schr ψ w (schr ψ w' φ) = ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  intro F _ _ ψ hψ κ _
  have h3 : ∀ w, ∀ φ ∈ schA F κ, schr ψ w φ ∈ schA F κ := fun w φ hφ => GlobalTheory.ConeMeasV.schr_mem_schA hψ w hφ
  refine ⟨?_, ?_, h3, ?_⟩
  · intro x g _
    refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
    simp [pureA, mul_comm]
  · obtain ⟨φ, hφ, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F κ
    have : ∃ ξ : κ → F, φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (by simp [thetaSum, h])
    obtain ⟨ξ, hξ⟩ := this
    refine ⟨(φ (fun i => algebraMap F (AF F) (ξ i)))⁻¹ • schr ψ ((fun i => algebraMap F (AF F) (ξ i)), 0) φ,
      Submodule.smul_mem _ _ (h3 _ φ hφ), ?_⟩
    simp [schr, hξ]
  · intro w w' φ
    funext x
    simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
    congr 2
    simp only [add_dotProduct, dotProduct_add]
    have h2 : (2 : AF F) * ⅟(2 : AF F) = 1 := mul_invOf_self 2
    linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

end GlobalTheory.TowU.PointVal
