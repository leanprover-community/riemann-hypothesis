module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeySectionEqConstMulThetaFunctionFibre
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries


theorem _root_.GlobalTheory.T.keySection_eq_const_mul_thetaFunction_fibre : ∀ (x : KeyIn ℂ) (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (y : Sp ℂ ⟶ S) (Φ : x.P.A.left ⟶ G.left) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (w : LB.Iso (L.pull Φ) x.P.L) (θ : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ) (s : (L.pull (pullback.fst G.hom y)).Sec), L.IsLB → IsPullback Φ x.P.A.hom G.hom y → w.IsGen → (∃ z, θ z ≠ 0) → (∀ j z, ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ k j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (x.P.L.U k ⊓ (L.pull Φ).U j) → u.fr k z = valAt' (u.ex z).left (x.P.L.U k ⊓ (L.pull Φ).U j) (w.s (k, j)).val * fr (j PUnit.unit) z) → (∀ j z (p : Sp ℂ ⟶ pullback G.hom y), p ≫ pullback.fst _ _ = (u.ex z).left ≫ Φ → p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → valAt' p ((L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) → ∃ c₀ : ℂ, u.IsFn x.th (fun z => c₀ * θ z) := by
  first | exact @GlobalTheory.FibreKeyTheta.th_isFn_const_mul | exact GlobalTheory.FibreKeyTheta.th_isFn_const_mul | (intros; apply GlobalTheory.FibreKeyTheta.th_isFn_const_mul <;> assumption)
