module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueEqQuotientSectionByPowerAtField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pointValue_eq_quotient_section_by_power_at_field : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j₀ → ∀ (k : ℕ) (s : SecM (𝟙 X) L k), ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus s → (∀ f : Γ(X, Out.nonzeroLocus s), ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N, valR ξ _ (c.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m) ∧ ∀ m N : ℕ, N = k * m → ∀ ρ : SecM (𝟙 X) L N, ∃ f : Γ(X, Out.nonzeroLocus s), valR ξ _ (ρ.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m := by
  first | exact @GlobalTheory.SecQuot.valR_secM_eq_mul_pow | exact GlobalTheory.SecQuot.valR_secM_eq_mul_pow | (intros; apply GlobalTheory.SecQuot.valR_secM_eq_mul_pow <;> assumption)
