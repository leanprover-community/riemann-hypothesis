module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.GoodMetric

open Polynomial in
theorem chernPoly_zero' {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : chernPoly G v 0 = 1 := by
  rw [chernPoly, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

open Polynomial in
theorem chernPoly_above {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) (hk : Fintype.card r < k) : chernPoly G v k = 0 := by
  rw [chernPoly]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [← Matrix.reverse_charpoly]
  calc _ ≤ (Matrix.charpoly (-curvPoly G v)).natDegree := Polynomial.reverse_natDegree_le _
    _ = Fintype.card r := Matrix.charpoly_natDegree_eq_dim _
    _ < k := hk

theorem chernTop_unit : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (τ : ι) (Q : MvPolynomial (ι × ℕ) ℝ), chernTop ((MvPolynomial.X (τ, 0) - 1) * Q) G v = 0 ∧ ∀ k : ℕ, m τ < k → chernTop (MvPolynomial.X (τ, k) * Q) G v = 0 := by
  intro n ι m G v τ Q
  refine ⟨?_, fun k hk => ?_⟩
  · simp only [chernTop, map_mul, map_sub, map_one, MvPolynomial.aeval_X, chernPoly_zero', sub_self, zero_mul,
      topCoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_zero, Finset.sum_const_zero, Complex.zero_re]
  · have h := chernPoly_above (fun u => G u τ) v k (by simpa using hk)
    simp only [chernTop, map_mul, MvPolynomial.aeval_X, h, zero_mul,
      topCoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_zero, Finset.sum_const_zero, Complex.zero_re]

end GlobalTheory.GoodMetric
