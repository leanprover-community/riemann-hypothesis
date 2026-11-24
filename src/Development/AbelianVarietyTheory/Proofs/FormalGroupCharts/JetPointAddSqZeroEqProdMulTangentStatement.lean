module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointAddSqZeroEqProdMulTangent
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

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.jetPoint_add_sqZero_eq_prod_mul_tangent : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (J : Ideal A), J * RingHom.ker aug = ⊥ → J ≤ RingHom.ker aug → ∀ (m : ℕ) (ψ ψ' : JetR R (Fin d) m →ₐ[R] A), aug.comp ψ = jetAug R (Fin d) m → aug.comp ψ' = jetAug R (Fin d) m → ∀ e : Fin d → (DualNumber R →ₐ[R] A), (∀ j, e j (TrivSqZeroExt.inr 1) ∈ J) → (∀ j, ψ' (zR m j) = ψ (zR m j) + e j (TrivSqZeroExt.inr 1)) → spMap ψ' ≫ x m = (∏ j, (spMap (e j) ≫ v j : sp (R₀ := R) A ⟶ G)) * (spMap ψ ≫ x m) := by
  first | exact @GlobalTheory.jet_add_sqZero_eq_prod_mul | exact GlobalTheory.jet_add_sqZero_eq_prod_mul | (intros; apply GlobalTheory.jet_add_sqZero_eq_prod_mul <;> assumption)
