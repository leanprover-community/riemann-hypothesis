module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
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

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.PartSupp

open Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum.VacInt

theorem zeroAt_mul_left (D : Formalism.BasicNotions.D7) {q : ℕ} {e z : AE D} (he : e ∈ OhE D) (hz : ZeroAt D q z) :
    ZeroAt D q (e * z) := by
  intro k
  obtain ⟨m, hm, hc, s, hs, h⟩ := hz k
  exact ⟨m, hm, hc, e * s, mul_mem he hs, by linear_combination e * h⟩

theorem trivAt_part_of_trivAt (D : Formalism.BasicNotions.D7) {N : ℕ} (P : ℕ → Prop) (g : GA D N) {q : ℕ}
    (h : TrivAt D q (g : GL (Fin N) (AE D))) : TrivAt D q (part D P g : GL (Fin N) (AE D)) := by
  intro i j
  have := zeroAt_mul_left D (e := eps D.host.E P) (eps_mem P) (h i j)
  convert this using 1
  show cutM _ _ _ i j - _ = _
  rw [cutM_apply]
  ring

theorem suppInert_part_of_suppInert : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (P : ℕ → Prop) (y : Formalism.MainNotions.StandardLatticesGL3.GA D N),
    Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
      Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.NormSum.VacInt.part D P y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :=
  fun {D} {_} P y hy q hq h => trivAt_part_of_trivAt D P y (hy q hq h)

end GlobalTheory.NormSum.PartSupp
