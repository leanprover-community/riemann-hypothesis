module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEllipticKeyDataValueEqDiscriminant
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.exists_ellipticKeyData_value_eq_discriminant : ThetaUnifAV → ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic], ∃ x : KeyIn R, x.P.g = 1 ∧ ∀ (s : R →+* ℂ) (x' : KeyIn ℂ) (τ M : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a b : Fin x'.P.g → ℂ) (c : ℂ), KeyPB x' x s → charHalf x'.P.g a b → c ≠ 0 → NormalAt x' τ M a b c → M.det ^ 4 / c ^ 8 = s W.Δ := by
  first | exact @GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant | exact GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant | (intros; apply GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant <;> assumption)
