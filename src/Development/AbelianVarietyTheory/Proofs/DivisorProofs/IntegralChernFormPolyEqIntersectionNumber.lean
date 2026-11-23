module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceComplexPointsOfProjVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolynomialEqIntersectionNumberStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityHermitianFormsEqZeroOffDegreeStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernLine

theorem eq_homogeneousComponent {κ R : Type} [AddCommGroup R] (f : MvPolynomial κ ℝ →+ R) (D : ℕ)
    (hf : ∀ d, d ≠ D → ∀ Q : MvPolynomial κ ℝ, Q.IsHomogeneous d → f Q = 0) (P : MvPolynomial κ ℝ) :
    f P = f (homogeneousComponent D P) := by
  conv_lhs => rw [← sum_homogeneousComponent P]

  rw [map_sum, Finset.sum_eq_single D]
  · intro b _ hb
    exact hf b hb _ (homogeneousComponent_isHomogeneous b P)
  · intro hD
    rw [Finset.mem_range, not_lt] at hD
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem interPoly_eq_zero {F : Type} [Field F] (Y : Var F) {κ : Type} (Δ : κ → Y.Dv) (d : ℕ) (hd : d ≠ Y.dim)
    (Q : MvPolynomial κ ℝ) (hQ : Q.IsHomogeneous d) : Y.interPoly Δ Q = 0 := by
  classical

  rw [Q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm' : m.degree = d := by
    have := hQ (mem_support_iff.mp hm)
    first
    | (rw [Finsupp.degree_eq_weight_one]; exact this)
    | exact this
  rw [show monomial m (AddMonoidAlgebra.coeff Q m) = AddMonoidAlgebra.coeff Q m • basisMonomials κ ℝ m by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, Var.interPoly, Module.Basis.constr_basis, dite_eq_right, smul_zero]
  rintro ⟨s, hs⟩
  apply hd

  rw [← hm', ← hs, map_sum]
  simp

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hC F _ σ X κ _ Δ L r ψ hψ P
  have hR : X.interPoly Δ P = X.interPoly Δ (homogeneousComponent X.dim P) :=
    eq_homogeneousComponent (X.interPoly Δ).toAddMonoidHom X.dim (fun d hd Q hQ => interPoly_eq_zero X Δ d hd Q hQ) P
  have hL : ∀ x, dens (evalF (atlas X σ) (fun a => c1W (ψ a)) P x) =
      dens (evalF (atlas X σ) (fun a => c1W (ψ a)) (homogeneousComponent X.dim P) x) := by
    intro x
    let f : MvPolynomial κ ℝ →+ ℂ :=
      { toFun := fun Q => dens (evalF (atlas X σ) (fun a => c1W (ψ a)) Q x)
        map_zero' := by simp [evalF, LineForm.fld, dens]
        map_add' := fun Q Q' => by
          simp only [evalF, LineForm.fld, map_add (f := _), Subalgebra.coe_add]
          exact LineForm.TopInt.dens_add _ _ }
    refine eq_homogeneousComponent f X.dim (fun d hd Q hQ => ?_) P
    exact GlobalTheory.T.topDensity_hermitianForms_eq_zero_offDegree X.dim κ _ d Q hQ hd
  rw [hR, ← GlobalTheory.T.integral_chernForm_polynomial_eq_intersectionNumber hC F σ X κ Δ L r ψ hψ _ (homogeneousComponent_isHomogeneous _ P)]
  simp only [HolAtlas.integral, LineForm.TopInt.part_congr _ hL]

end GlobalTheory.ChernLine
