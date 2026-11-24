module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverByPolarizationPowerSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstOfRegularOnCoverAbelianVarietyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatSymbolRegularOnSectionNonvanishingLocusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixZeroDerivationEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRelationZeroDerivationOfShiftedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolEntriesRegularAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjectiveStatement
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
import Mathlib.Tactic.Linter.Style
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

theorem GlobalTheory.Heat.gc_symbol_vanishes : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), Λᵀ = Λ → (∀ r, δ₀ (ψ r) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → Λ = 0 := by
  intro K _ _ P₀ n v dd hv F _ ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ Λ hΛ hδ₀ hbr
  obtain ⟨k, I, s, hk, hcov, hai⟩ := GlobalTheory.T.exists_affine_cover_by_polarization_power_sections K P₀
  have haff : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) := fun i => (hai i).1
  have hne := fun i => (hai i).2
  have hloc : ∀ i, ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i =>
    GlobalTheory.T.top_le_preimage_nonempty_open_of_pointValue_injective K P₀ F ψ ξ hξ hval _ (hne i)
  have hL := fun i => GlobalTheory.T.heat_symbol_regular_on_section_nonvanishing_locus K P₀ n v dd hv F ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ Λ hbr k hk (s i) (hloc i)
  have hreg : ∀ i a e, ∃ h : Γ(P₀.A.left, Out.nonzeroLocus (s i)), valR ξ _ h = Λ a e := fun i =>
    GlobalTheory.T.symbol_entries_regular_affineOpen K P₀ n v dd hv F ψ ξ hξ hval δ hδ Λ _ (haff i) (hloc i) (hL i).1
  have hc : ∀ a e, ∃ r : K, ψ r = Λ a e := fun a e =>
    GlobalTheory.T.exists_const_of_regular_on_cover_abelianVariety K P₀ F ψ ξ hξ hval I (fun i => Out.nonzeroLocus (s i)) hcov hloc (Λ a e) (fun i => hreg i a e)
  choose lam hlam using hc
  have hsym : lamᵀ = lam := by
    ext a e
    apply ψ.injective
    show ψ (lam e a) = ψ (lam a e)
    rw [hlam, hlam]
    exact congrFun (congrFun hΛ a) e
  have hks := GlobalTheory.T.kodairaSpencer_relation_zero_derivation_of_shifted K P₀ n v dd hv F ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ lam hsym hδ₀ k hk I s hcov haff hloc
    (fun i f => by
      obtain ⟨f', hf'⟩ := (hL i).2 f
      exact ⟨f', by rw [hf']; simp only [hlam]⟩)
  have h0 := GlobalTheory.T.kodairaSpencer_matrix_zero_derivation_eq_zero K P₀ n v dd hv lam hks
  ext a e
  rw [← hlam a e, h0]
  simp
