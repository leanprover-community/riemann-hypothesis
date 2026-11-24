module

public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomPadicAlgClNeZero
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_ringHom_padicAlgCl_ne_zero' : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by
  first | exact @GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero | exact GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero | (intros; apply GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero <;> assumption)
