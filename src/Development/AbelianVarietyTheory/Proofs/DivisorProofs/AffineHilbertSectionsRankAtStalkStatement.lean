module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsRankAtStalk
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.affineHilbertSections_rankAtStalk : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens) (P : PrimeSpectrum Γ(Z, W)), Module.rankAtStalk (GlobalTheory.HilbAff.Sec A B y W) P = r := by
  first | (exact @GlobalTheory.HilbAff.rankAtStalk_sec) | (exact GlobalTheory.HilbAff.rankAtStalk_sec) | (intros; apply GlobalTheory.HilbAff.rankAtStalk_sec  <;> assumption)
