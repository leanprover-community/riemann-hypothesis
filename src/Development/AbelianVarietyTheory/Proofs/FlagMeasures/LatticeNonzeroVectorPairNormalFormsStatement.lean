module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeNonzeroVectorPairNormalForms
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.lattice_nonzero_vector_pair_normal_forms : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ), ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → (∀ 𝔞 Λ', 𝔞 ≠ ⊥ → Submodule.IsFullLattice E Λ' → Submodule.IsFullLattice E (Lf 𝔞 Λ') ∧ Pi.single 0 1 ∈ Lf 𝔞 Λ') ∧ (∀ Λ : Submodule (𝓞 E) (Fin (k + 1) → E), Submodule.IsFullLattice E Λ → ∀ x ∈ Λ, x ≠ 0 → ∃ (γ : GL (Fin (k + 1)) E) (𝔞 : Ideal (𝓞 E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), 𝔞 ≠ ⊥ ∧ Submodule.IsFullLattice E Λ' ∧ (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ x = Pi.single 0 1 ∧ ∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ y ∈ Lf 𝔞 Λ' ↔ y ∈ Λ) ∧ ∀ 𝔞 𝔟 Λ₁ Λ₂, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → Submodule.IsFullLattice E Λ₁ → Submodule.IsFullLattice E Λ₂ → ∀ γ : GL (Fin (k + 1)) E, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Pi.single 0 1 = Pi.single 0 1 → ((∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ y ∈ Lf 𝔟 Λ₂ ↔ y ∈ Lf 𝔞 Λ₁) ↔ 𝔞 = 𝔟 ∧ (∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).submatrix Fin.succ Fin.succ *ᵥ y ∈ Λ₂ ↔ y ∈ Λ₁) ∧ ∀ y ∈ Λ₁, ∀ t ∈ 𝔞, (t : E) * ((fun b => (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) 0 b.succ) ⬝ᵥ y) ∈ (algebraMap (𝓞 E) E).range) := by
  first | exact @GlobalTheory.LatVecPair.classes | exact GlobalTheory.LatVecPair.classes | (intros; apply GlobalTheory.LatVecPair.classes <;> assumption)
