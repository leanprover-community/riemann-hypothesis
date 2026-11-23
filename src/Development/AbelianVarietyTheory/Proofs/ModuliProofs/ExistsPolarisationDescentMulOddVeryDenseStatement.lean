module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationDescentMulOddVeryDense
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_polarisation_descent_mul_odd_veryDense : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (P : Set (Ideal R)) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Fin (2 * g) → ZMod m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) := by
  first | exact @GlobalTheory.MulDescent.exists_polarisation_of_veryDense | exact GlobalTheory.MulDescent.exists_polarisation_of_veryDense | (intros; apply GlobalTheory.MulDescent.exists_polarisation_of_veryDense <;> assumption)
