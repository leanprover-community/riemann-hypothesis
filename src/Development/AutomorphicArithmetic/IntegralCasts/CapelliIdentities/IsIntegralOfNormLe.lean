module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
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

namespace UpperTheory.Reformulated.B.S4

theorem isIntegral_of_norm_le {l : ℕ} [Fact l.Prime] {z : PadicAlgCl l} (hz : ‖z‖ ≤ 1) : IsIntegral ℤ_[l] z := by
  have hi : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  have hm : (minpoly ℚ_[l] z).Monic := minpoly.monic hi
  have hv : spectralValue (minpoly ℚ_[l] z) ≤ 1 := hz
  have hc : ∀ n, ‖(minpoly ℚ_[l] z).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hv
  have hl : minpoly ℚ_[l] z ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  have h0 : Polynomial.aeval z (q.map (algebraMap ℤ_[l] ℚ_[l])) = 0 := by
    rw [hq]
    exact minpoly.aeval _ _
  rw [Polynomial.aeval_map_algebraMap] at h0
  exact h0

end UpperTheory.Reformulated.B.S4
