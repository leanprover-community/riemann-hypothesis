module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIntegralAdditiveSystemFrobeniusPower
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.PMonE

theorem glOnto_zero_and_glCount_zero : GLOnto 0 ∧ GLCount 0 := by
  constructor
  · intro F _ _ _ _ p _ _ m _ _ e D he _ M hM b hb
    obtain ⟨x, hx, -⟩ := existsUnique_integral_gsum_eq F p m e D he M
      (fun i j => by simp [hM.top]) (fun n hn i j => hM.small n (by omega) i j) b hb
    exact ⟨x, hx⟩
  · intro F _ _ _ _ p _ _ m _ _ e D he _ M hM _
    obtain ⟨y, hy, huniq⟩ := existsUnique_integral_gsum_eq F p m e D he M
      (fun i j => by simp [hM.top]) (fun n hn i j => hM.small n (by omega) i j) 0 (fun i => by simp)
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_exists]
    exact ⟨⟨y, hy⟩, fun z => Subtype.ext (huniq z.1 z.2)⟩

end GlobalTheory.PMonE
