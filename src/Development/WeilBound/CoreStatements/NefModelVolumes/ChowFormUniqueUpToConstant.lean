module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.MvPolynomial.Nilpotent
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open MvPolynomial

namespace ChowFormCompatibility

theorem chow_form_unique_up_to_constant : ∀ (k : Type) [Field k] (N B : ℕ) (I : Ideal (MvPolynomial (Fin N) k)) (f g : MvPolynomial (Fin B × Fin N) k), GroundTheory.Heights₂.Heights.IsChowForm I B f → GroundTheory.Heights₂.Heights.IsChowForm I B g → ∃ c : k, c ≠ 0 ∧ g = C c * f := by
  intro k _ N B I f g hf hg
  have hfg : f ∣ g := (hf.2 g).1 ((hg.2 g).2 dvd_rfl)
  have hgf : g ∣ f := (hg.2 f).1 ((hf.2 f).2 dvd_rfl)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hfg hgf
  obtain ⟨c, hc, hcu⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 u.isUnit
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← hu, hcu, mul_comm]

end ChowFormCompatibility
