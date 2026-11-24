module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonUnitAtOfNotIsUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapFibreDivisibilityIdealCompletionLimit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.mem_map_fibreDivisibilityIdeal_completion_limit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z) (hπ : M₁.IsHom M (AlgHom.id o Ω) π), IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (D : EffCartierData M.Z) (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ (F : AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a : ℕ → M₁.O z), (∀ n, F - algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a n) ∈ (maximalIdeal (M₁.O z)).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) ^ n) → (∀ x' : M.Z, π x' = z → IsClosed ({x'} : Set M.Z) → ∀ f', EqAt M D x' f' → ∀ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∃ c d : M.O x', (a n : Ω) = c * f' + d ∧ d ∈ maximalIdeal (M.O x') ^ e) → F ∈ (GlobalTheory.FibreCorr.fibreIdeal hπ D z).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) := by
  first | exact @GlobalTheory.FormalCorr.mem_map_fibreIdeal | exact GlobalTheory.FormalCorr.mem_map_fibreIdeal | (intros; apply GlobalTheory.FormalCorr.mem_map_fibreIdeal <;> assumption)
