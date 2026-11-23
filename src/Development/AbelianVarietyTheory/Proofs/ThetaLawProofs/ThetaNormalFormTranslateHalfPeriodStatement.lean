module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaNormalFormTranslateHalfPeriod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

theorem _root_.GlobalTheory.T.thetaNormalForm_translate_halfPeriod : Out.Laws → ThetaUnifAV → ∀ (x x' : KeyIn ℂ) (g : ℕ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b a' b' : Fin g → ℂ) (m n : Fin g → ℤ) (ν : ℂˣ), charHalf g a b → charHalf g a' b' → Wit x h u τ a b → (∀ i, ∃ k : ℤ, a' i = a i + n i / 2 + k) → (∀ i, ∃ k : ℤ, b' i = b i + m i / 2 + k) → IsTrl x' x (u.ex (frac τ 2 m n)) ν → ∃ (h' : x'.P.g = g) (u' : HolUnif x'.P.A x'.P.L g) (φ : x'.P.A ≅ x.P.A) (c : ℂ), IsMonHom φ.hom ∧ (∀ z, u'.ex z ≫ φ.hom = u.ex z) ∧ c ^ 8 * (ν : ℂ) ^ 2 = 1 ∧ (∀ z, z ∈ u'.Λ ↔ z ∈ u.Λ) ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th (fun z => c * thetaChar τ a' b' z) ∧ ∀ i : Fin g, u'.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x'.v (i.cast h'.symm)) := by
  first | exact @GlobalTheory.HalfTranslate.normalForm_translate | exact GlobalTheory.HalfTranslate.normalForm_translate | (intros; apply GlobalTheory.HalfTranslate.normalForm_translate <;> assumption)
