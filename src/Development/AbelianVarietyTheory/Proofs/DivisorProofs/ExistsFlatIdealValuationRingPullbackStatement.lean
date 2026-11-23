module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatIdealValuationRingPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.exists_flat_ideal_valuationRing_pullback : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X'] (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X), IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))) → ∀ I : Ideal Γ(X', ⊤), ∃ J : Ideal Γ(X, ⊤), ((Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat ∧ Ideal.map b.appTop.hom J = I := by
  first | exact @GlobalTheory.FlatHilbAff.exists_flat_ideal | exact GlobalTheory.FlatHilbAff.exists_flat_ideal | (intros; apply GlobalTheory.FlatHilbAff.exists_flat_ideal <;> assumption)
