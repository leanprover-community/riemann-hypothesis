module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.SimilTheta
open Matrix

variable {g : ℕ}

def lat (τ : Matrix (Fin g) (Fin g) ℂ) (k n : Fin g → ℤ) : Fin g → ℂ :=
  (fun i => (k i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))

def aut (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (k n : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ (fun i => (k i : ℂ)) - b ⬝ᵥ (fun i => (n i : ℂ)) -
    ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z))

def tors (τ : Matrix (Fin g) (Fin g) ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (r : Fin 4) :
    Fin g → ℂ := (m : ℂ)⁻¹ • ∑ c, al r c • lat τ (k c) (n c)

def simTheta (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ)
    (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) : ℂ :=
  (∏ r, thetaChar τ a b (∑ c, al r c • y c + tors τ al m k n r)) *
    Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.aut_ne_zero (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (k n : Fin g → ℤ) (z : Fin g → ℂ) :
    _root_.GlobalTheory.SimilTheta.aut τ a b k n z ≠ 0 :=
  Complex.exp_ne_zero _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.isLevel_iff_aut (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ) (F : (Fin g → ℂ) → ℂ) :
    _root_.GlobalTheory.KeyKa.IsLevel τ a b l F ↔ Differentiable ℂ F ∧ ∀ k n z, F (z + _root_.GlobalTheory.SimilTheta.lat τ k n) = _root_.GlobalTheory.SimilTheta.aut τ a b k n z ^ l * F z :=
  Iff.rfl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_add (τ : Matrix (Fin g) (Fin g) ℂ) (k n k' n' : Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (k + k') (n + n') = _root_.GlobalTheory.SimilTheta.lat τ k n + _root_.GlobalTheory.SimilTheta.lat τ k' n' := by
  have h : (fun i => ((n + n') i : ℂ)) = (fun i => (n i : ℂ)) + fun i => (n' i : ℂ) := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_add]
  ext i
  simp only [Pi.add_apply, Int.cast_add]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_zsmul (τ : Matrix (Fin g) (Fin g) ℂ) (s : ℤ) (k n : Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (s • k) (s • n) = s • _root_.GlobalTheory.SimilTheta.lat τ k n := by
  have h : (fun i => ((s • n) i : ℂ)) = (s : ℂ) • fun i => (n i : ℂ) := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
private theorem lat_zero_zero (τ : Matrix (Fin g) (Fin g) ℂ) :
    _root_.GlobalTheory.SimilTheta.lat τ 0 0 = 0 := by
  have h : (fun i : Fin g => (((0 : Fin g → ℤ) i : ℤ) : ℂ)) = 0 := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_zero]
  ext i
  simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_sum (τ : Matrix (Fin g) (Fin g) ℂ) {K : Type} (s : Finset K) (k n : K → Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (∑ c ∈ s, k c) (∑ c ∈ s, n c) = ∑ c ∈ s, _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lat_zero_zero τ
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, Finset.sum_insert hc, _root_.GlobalTheory.SimilTheta.lat_add, ih]

end GlobalTheory.SimilTheta
end
