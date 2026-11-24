module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolEntriesRegularAffineOpen
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

theorem _root_.GlobalTheory.T.symbol_entries_regular_affineOpen : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (Λ : Matrix (Fin n) (Fin n) F) (W : P₀.A.left.Opens), IsAffineOpen W → ⊤ ≤ ξ ⁻¹ᵁ W → (∀ f f' : Γ(P₀.A.left, W), ∃ h : Γ(P₀.A.left, W), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) → ∀ a e, ∃ h : Γ(P₀.A.left, W), valR ξ W h = Λ a e := by
  first | exact @GlobalTheory.Heat.SymReg.entry_regular | exact GlobalTheory.Heat.SymReg.entry_regular | (intros; apply GlobalTheory.Heat.SymReg.entry_regular <;> assumption)
