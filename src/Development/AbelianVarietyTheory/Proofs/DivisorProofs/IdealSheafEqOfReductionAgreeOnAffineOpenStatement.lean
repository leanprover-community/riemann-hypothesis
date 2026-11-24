module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfReductionAgreeOnAffineOpen
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.idealSheaf_eq_of_reduction_agree_on_affineOpen : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) [IsLocallyNoetherian W] (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → ∀ V : W.affineOpens, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData), Reduces (π ≫ f) I T' (fun e => (t e).comap π) → Reduces f I T'' (fun e => t e ⊔ K ^ k) → ∀ e, ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V = (t e).ideal V := by
  first | exact @GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine | exact GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine | (intros; apply GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine <;> assumption)
