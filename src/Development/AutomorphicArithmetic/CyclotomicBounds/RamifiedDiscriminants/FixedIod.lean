module

public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField Formalism.BasicNotions

namespace UpperTheory.Ram

theorem image_mem_of_fixed_iod {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω)
    (hM : ∀ y : Ω, y ^ (H.QS * H.q) = 1 → y ∈ M) (x : H.E) (hx : H.sigmaOf R.toFrame.iod x = x) : J x ∈ M := by
  refine H.toHostRaw.image_mem_of_fixed J M (Dvd.intro _ rfl) hM x fun u hu => ?_
  rcases H.art_d u hu with h | h
  · rw [h, map_one]; rfl
  · rw [h]; exact hx

end UpperTheory.Ram
