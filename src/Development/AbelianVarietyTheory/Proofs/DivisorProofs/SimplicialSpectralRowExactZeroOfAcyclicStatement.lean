module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialSpectralRowExactZeroOfAcyclic
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

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
  (∀ (p : ℕ) (s : ℤ), 0 < s → Subsingleton (H R (disc.obj (E.obj (op ⦋p⦌))) F s)) →
  (∀ m : ℤ, 0 < m → Subsingleton (H R E F m)) → ∀ p : ℕ, RowExact R E F 0 p := by
  first | (exact @GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (exact GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (intros; apply GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic  <;> assumption)
