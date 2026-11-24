module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominator
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_rational_unitary_split_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N N (fm F γ.1 * g.1) ∧ ∃ s : 𝓞 E, SplitOff c N s ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • ((fm F γ.1 * g.1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) ∧ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (((g⁻¹).1 * fm F (γ⁻¹).1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | exact GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | (intros; apply GlobalTheory.UnRep.LatForm.exists_rep_split_denominator <;> assumption)
