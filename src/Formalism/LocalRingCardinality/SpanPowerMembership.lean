module

public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
public import Formalism.LocalRingCardinality.SpanPowerMembership.SizeData₂
public import Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

instance instFactExamplePrime : Fact T0.Prime := ⟨examplePrime_prime⟩

theorem exampleHost_type_primes_split : ∀ k, (placesOver H0.E (H0.g k)).ncard = Module.finrank ℚ H0.E := by
  refine g_split_of H0 (fun k => ?_)
  fin_cases k
  · show 413718278401 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num
  · show 603339156001 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num

theorem exampleHost_typeHypothesis : THyp H0 :=
  { cond := fun k => by
      fin_cases k
      · show 413718278401 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num
      · show 603339156001 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num
    bb := BB_disj0
    jac := fun k => by
      fin_cases k
      · exact ⟨by show (413718278401 : ℕ) ≠ 2; norm_num, by show jacobiSym (-599) 413718278401 = 1; norm_num⟩
      · exact ⟨by show (603339156001 : ℕ) ≠ 2; norm_num, by show jacobiSym (-599) 603339156001 = 1; norm_num⟩ }

theorem examplePrime_ne_split_primes : T0 ≠ H0.pde ∧ T0 ≠ H0.pde' :=
  ⟨by show T0 ≠ 751; norm_num [T0], by show T0 ≠ 991; norm_num [T0]⟩

def exampleRecord (G : LocalGap H0) : D7 :=
  exampleRecordOfData H0 T0 exampleHost_type_primes_split exampleHost_typeHypothesis examplePrime_mem_levelPrimes examplePrime_ne_split_primes π0O π0_mem_K π0_norm π0_cong G

theorem nonempty_D7_of_localGap (G : LocalGap H0) : Nonempty D7 := ⟨exampleRecord G⟩

theorem record_nonempty_of_localGap : Nonempty (LocalGap H0) → Nonempty D7 := fun ⟨G⟩ => nonempty_D7_of_localGap G

end Formalism.BasicNotions.Examples₂
