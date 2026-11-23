module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPairDichotomy
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.locally_equal_or_unit : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) (e u : A' ⊗[A] A'), (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) → algebraMap A (A' ⊗[A] A') f * u = 1 - e → ∀ (T : Scheme.{0}) (y y' : T ⟶ Spec (CommRingCat.of A')), y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) = y' ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) → Loc T fun V k => k ≫ y = k ≫ y' ∨ IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (k ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop).hom f) := by
  first | (exact @GlobalTheory.EtC.PairDich.pair_dich) | (exact GlobalTheory.EtC.PairDich.pair_dich) | (intros; apply GlobalTheory.EtC.PairDich.pair_dich  <;> assumption)
