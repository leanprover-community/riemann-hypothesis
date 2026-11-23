module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIntegerRingAlmostAllPlaces
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etale_neighbourhood_kills_class : ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) → ∀ (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∀ (m i : ℤ), 0 < m → ∀ y : Ht q (sp B) m i, ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D), Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧ pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.oneCoh_main) | (exact GlobalTheory.EtC.oneCoh_main) | (intros; apply GlobalTheory.EtC.oneCoh_main <;> assumption)
