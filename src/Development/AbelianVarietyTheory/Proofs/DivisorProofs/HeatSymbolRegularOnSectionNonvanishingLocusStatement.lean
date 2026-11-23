module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatSymbolRegularOnSectionNonvanishingLocus
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

theorem _root_.GlobalTheory.T.heat_symbol_regular_on_section_nonvanishing_locus : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → ∀ (k : ℕ), 1 ≤ k → ∀ s : SecM (𝟙 P₀.A.left) P₀.L k, ⊤ ≤ ξ ⁻¹ᵁ (Out.nonzeroLocus s) → (∀ f f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ h : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) ∧ (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a (valR ξ _ (s.f fun _ => j₀)) / valR ξ _ (s.f fun _ => j₀)) * δ e (valR ξ _ f)) := by
  first | exact @GlobalTheory.HeatLoc.symb_regular | exact GlobalTheory.HeatLoc.symb_regular | (intros; apply GlobalTheory.HeatLoc.symb_regular <;> assumption)
