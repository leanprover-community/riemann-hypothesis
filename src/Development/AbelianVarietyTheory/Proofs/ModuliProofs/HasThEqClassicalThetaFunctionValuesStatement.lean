module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThEqClassicalThetaFunctionValues
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.hasTh_eq_classicalThetaFunction_values : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (t : TObj g (N' ^ 2) J b (spMap em)) (u : HolUnif t.A t.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (lam : Fin (2 * g) → u.Λ), Odd N' → u.IsAH Hm χ → u.IsThetaFn Hm χ 1 θ → θ ≠ 0 → (∀ i, (t.pt i).left = (u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ))).left) → t.HasTh (𝟙 _) (fun a => χ (∑ i, ((a i).val : ℤ) • lam i) * Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ)) (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) * θ ((N' : ℂ)⁻¹ • ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) := by
  first | exact @GlobalTheory.ThetaClassical.hasTh_classical | exact GlobalTheory.ThetaClassical.hasTh_classical | (intros; apply GlobalTheory.ThetaClassical.hasTh_classical <;> assumption)
