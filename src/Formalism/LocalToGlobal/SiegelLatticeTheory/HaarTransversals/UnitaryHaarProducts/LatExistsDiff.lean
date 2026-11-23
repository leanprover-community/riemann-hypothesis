module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsDefs
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.SG.Pf.LatEx

theorem splitDiff_holds : SplitDiff := by
  intro F E _ _ _ _ _ p P hp hPm hpP hpP2 h
  haveI : P.IsPrime := hPm.isPrime
  have hDE : differentIdeal ℤ (𝓞 E) ≤ P := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)]
    exact le_trans Ideal.mul_le_right h
  have hdvd : P ∣ differentIdeal ℤ (𝓞 E) := Ideal.dvd_iff_le.mpr hDE
  rw [dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain] at hdvd
  apply hdvd
  have hpu : ((p : ℤ)) ∈ P.under ℤ := by
    show (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) P
    rw [Ideal.mem_comap]
    simpa using hpP
  have hne : P.under ℤ ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpu
    exact hp.ne_zero (by exact_mod_cast hpu)
  haveI : P.LiesOver (P.under ℤ) := ⟨rfl⟩
  rw [← Ideal.ramificationIdx_eq_ramificationIdx' (P.under ℤ) P hne]
  apply Ideal.ramificationIdx'_spec
  · rw [pow_one]
    exact Ideal.map_comap_le
  · intro hle
    have h2 := hle (Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 E)) hpu)
    apply hpP2
    simpa using h2

end Formalism.L2.SG.Pf.LatEx
