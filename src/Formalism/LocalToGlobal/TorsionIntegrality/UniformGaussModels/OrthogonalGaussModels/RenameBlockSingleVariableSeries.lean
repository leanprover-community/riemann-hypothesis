module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.IsHypPair
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TrDual
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.InhA

open Formalism.L2.Th1.D Formalism.L2.Th1.Top
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

theorem hyp_of_gram (l : ℕ) [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hU : UnrOK (MaximalUnramifiedExtension l) l σ)
    (hζ : ∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1)) (E : Type) [Fintype E] [DecidableEq E] :
    ∃ f f' : E → (Bool × E) → MaximalUnramifiedExtension l, IsHypPair σ f f' := by
  obtain ⟨c, hc, hG⟩ := gramExists (MaximalUnramifiedExtension l) l σ hU hζ E
  refine ⟨fun e i => c i (false, e), fun e i => c i (true, e), fun e i => hc _ _, fun e i => hc _ _,
    ?_, ?_, ?_⟩
  · intro e e'
    have := hG (false, e') (false, e)
    simp only [ne_eq, not_true_eq_false, false_and, if_false] at this
    rw [← this]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · intro e e'
    have := hG (true, e') (true, e)
    simp only [ne_eq, not_true_eq_false, false_and, if_false] at this
    rw [← this]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · intro e e'
    have := hG (true, e') (false, e)
    have h2 : (∑ i, σ (c i (false, e)) * c i (true, e')) = ∑ k, c k (true, e') * σ (c k (false, e)) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h2, this]
    by_cases h : e = e'
    · subst h; simp
    · have h' : ¬ e' = e := fun q => h q.symm
      simp [h, h']

theorem joint (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) (ν r0 r1 : ℕ) [NeZero ν] :
    ∃ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin ν → MaximalUnramifiedExtension l)
      (f f' : Fin ν × Fin r0 × Fin r1 → (Bool × Fin ν × Fin r0 × Fin r1) → MaximalUnramifiedExtension l),
      UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsLawOfLog l F ∧ 2 ≤ 2 * ν ∧ Even (2 * ν) ∧ OwOK (2 * ν) σ om oms ∧
      TrDual (2 * ν) σ om oms ∧ (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ (2 * ν) - 1)) ∧ IsHypPair σ f f' := by
  obtain ⟨σ, F, be, om, oms, U0, Φ, ph, hU, _, _, hζ2, hζ, h2, hev, _, hO, hT, hF, _⟩ :=
    chainNonVacuous l (by omega) ν r0 r1
  obtain ⟨f, f', hff⟩ := hyp_of_gram l σ hU hζ2 (Fin ν × Fin r0 × Fin r1)
  exact ⟨σ, F, om, oms, f, f', hU, hF, h2, hev, hO, hT, hζ, hff⟩

end Formalism.L2.Th1.Top.InhA

namespace Formalism.L2.Th1.Top.InhB

open Formalism.L2.Th1.D Formalism.L2.Th1.Top
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

end Formalism.L2.Th1.Top.InhB
