module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerIsoDiagonalOfLPowerTorsionAction
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eighthPower_iso_diagonal_of_lPower_torsion_action : ∀ (K : Type) [Field K] [IsAlgClosed K] (G₀ G₁ H₀ H₁ : Over (Sp K)) [GrpObj G₀] [GrpObj G₁] [GrpObj H₀] [GrpObj H₁] [IsCommMonObj H₀] [IsCommMonObj H₁], IsSemiAbelian H₀ → IsSemiAbelian H₁ → ∀ (l : ℕ), l.Prime → (l : K) ≠ 0 → ∀ (p₀ : Fin 8 → (G₀ ⟶ H₀)) (p₁ : Fin 8 → (G₁ ⟶ H₁)), (∀ a, IsMonHom (p₀ a)) → (∀ a, IsMonHom (p₁ a)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₀)), ∃! x : T ⟶ G₀, ∀ a, x ≫ p₀ a = y a) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₁)), ∃! x : T ⟶ G₁, ∀ a, x ≫ p₁ a = y a) → ∀ (F : G₀ ⟶ G₁), IsMonHom F → IsIso F → (∀ (z z' : 𝟙_ (Over (Sp K)) ⟶ G₀), (∃ k : ℕ, z ^ (l ^ k) = 1) → (∃ k : ℕ, z' ^ (l ^ k) = 1) → ∀ a a', z ≫ p₀ a = z' ≫ p₀ a' → z ≫ F ≫ p₁ a = z' ≫ F ≫ p₁ a') → ∃ f₁ : H₀ ⟶ H₁, IsMonHom f₁ ∧ IsIso f₁ ∧ ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
  first | exact @GlobalTheory.PowerDiagonal.exists_diagonal | exact GlobalTheory.PowerDiagonal.exists_diagonal | (intros; apply GlobalTheory.PowerDiagonal.exists_diagonal <;> assumption)
