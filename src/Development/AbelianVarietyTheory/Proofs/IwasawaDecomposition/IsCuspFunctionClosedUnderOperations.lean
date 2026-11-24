module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem isCuspFun_closed : ∀ (D : D7) (V : HSp D) (φ φ' : GA D V → ℂ), IsAutFun V φ → IsAutFun V φ' → IsCuspFun V φ → IsCuspFun V φ' → IsCuspFun V (φ + φ') ∧ (∀ c : ℂ, IsCuspFun V (c • φ)) ∧ (∀ k, IsCuspFun V (rTr V k φ)) ∧ IsCuspFun V (fun g => star (φ g)) := by
  intro D V φ φ' h h' c c'
  refine ⟨?_, fun a r C hC μ 𝓕 hμ h𝓕 g => ?_, fun k r C hC μ 𝓕 hμ h𝓕 g => ?_, fun r C hC μ 𝓕 hμ h𝓕 g => ?_⟩
  · refine (GlobalTheory.AutFunCompare.isCuspFun_iff V (φ + φ') (h.cont.add h'.cont) fun γ hγ g => ?_).2
      (add_mem ((GlobalTheory.AutFunCompare.isCuspFun_iff V φ h.cont h.left).1 c)
        ((GlobalTheory.AutFunCompare.isCuspFun_iff V φ' h'.cont h'.left).1 c'))
    rw [Pi.add_apply, Pi.add_apply, h.left γ hγ, h'.left γ hγ]
  · simp only [Pi.smul_apply]
    rw [integral_smul, c r C hC μ 𝓕 hμ h𝓕 g, smul_zero]
  · simp only [rTr, mul_assoc]
    exact c r C hC μ 𝓕 hμ h𝓕 (g * k)
  · have e := integral_conj (𝕜 := ℂ) (μ := μ.restrict 𝓕) (f := fun n : NI V C => φ ((n : GA D V) * g))
    rw [c r C hC μ 𝓕 hμ h𝓕 g, map_zero] at e
    exact e

end GlobalTheory.Mem.Th
