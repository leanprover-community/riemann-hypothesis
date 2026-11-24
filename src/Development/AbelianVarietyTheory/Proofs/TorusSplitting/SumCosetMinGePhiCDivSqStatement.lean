module

public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCosetMinGePhiCDivSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.le_sum_of_le_phiC_div_sq : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E), (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) → ∀ w₀ : 𝓞 E, (w₀ : E) + cj w₀ = 1 → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X] (Q : X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X), (∀ a, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → (∀ a, 0 ≤ Q a) → ∀ (m : ℕ), 2 ≤ m → ∀ (n : ℕ) (y : Fin n → X), (∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m ^ 2 • t) → ∀ v : Fin n → WithTop ℚ, (∀ b (q : ℚ), (∀ χ, q ≤ (Q (m • χ + y b) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v b) → ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (m : ℝ) ^ 2 → (q : WithTop ℚ) ≤ ∑ b, v b := by
  first | exact @GlobalTheory.EtaVal.sum_cosetMin_ge_phiC_div_sq | exact GlobalTheory.EtaVal.sum_cosetMin_ge_phiC_div_sq | (intros; apply GlobalTheory.EtaVal.sum_cosetMin_ge_phiC_div_sq <;> assumption)
