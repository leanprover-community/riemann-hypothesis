module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatRankClosedSubschemeOfQuotientBasis
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_quotient_basis : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) {r : ℕ} (v : Fin r → B), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → GlobalTheory.HilbAff.Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (GlobalTheory.HilbAff.xI A B C J) := by
  first | (exact @GlobalTheory.HilbAff.good_xI) | (exact GlobalTheory.HilbAff.good_xI) | (intros; apply GlobalTheory.HilbAff.good_xI  <;> assumption)
