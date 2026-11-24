module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twist_mul {D : Formalism.BasicNotions.D7} (p : PlF D) (s : ℕ) (x : (D.s.atP p).Ep) :
    twist p s x = x * twist p s 1 := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp [mul_comm]

theorem twist_one_pow {D : Formalism.BasicNotions.D7} (p : PlF D) (s : ℕ) :
    twist p s (1 : (D.s.atP p).Ep) = twist p 1 (1 : (D.s.atP p).Ep) ^ s := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp

theorem twist_sq {D : Formalism.BasicNotions.D7} (p : PlF D) :
    twist p 1 (1 : (D.s.atP p).Ep) ^ 2 = 1 := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp

def hF (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (a s : ℕ) : (D.s.atP p).Ep :=
  Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
    (nu D.R.rS a (a + s - 1))) * twist p s 1 * Ring.inverse (qE p)

end PI.SupportDatumW
