module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitSectionAvoid
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

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

theorem _root_.GlobalTheory.T.cone_contracting_homotopy : ∃ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (ε : ∀ a b : ℕ, (bo a b ⟶ bo 0 0) →+ ℤ), (∀ (a b : ℕ) (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) (β : SimplexCategory.mk 0 ⟶ SimplexCategory.mk b), ε a b (bop α β) = 1) ∧ (∀ (a b : ℕ) (r : bo a b ⟶ bo 0 0), cone a b 0 r ≫ dD 1 0 = r - ε a b r • bop (idc a 0) (idc b 0)) ∧ ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)), cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n) := by
  first | (exact @GlobalTheory.EZ.Cone.coneContraction) | (exact GlobalTheory.EZ.Cone.coneContraction) | (intros; apply GlobalTheory.EZ.Cone.coneContraction  <;> assumption)
