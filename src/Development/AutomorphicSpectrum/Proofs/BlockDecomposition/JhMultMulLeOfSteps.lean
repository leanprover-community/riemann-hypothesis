module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.CsStages

variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

theorem jhMult_add_le {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (h0 : ∀ u, p (ι u) = 0) :
    jhMult σ ρ₁ + jhMult σ ρ₂ ≤ jhMult σ ρ := by
  refine ENat.biSup_add_biSup_le' ⟨0, occurs_zero _ _⟩ ⟨0, occurs_zero _ _⟩ fun a ha b hb => ?_
  rw [← Nat.cast_add]
  exact le_iSup₂_of_le _ (occurs_add ι p hι hp h0 ha hb) le_rfl

theorem jhMult_mul_le_of_steps (σ : Representation F G W) (ρ : Representation F G V)
    (A : Subrepresentation ρ → ℕ∞) (m : ℕ∞) (hmono : ∀ S T : Subrepresentation ρ, T ≤ S → A T ≤ A S)
    (hstep : ∀ S T : Subrepresentation ρ, T ≤ S → Nonempty ((subQuot S T).Equiv σ) → A T + m ≤ A S) :
    jhMult σ ρ * m ≤ A ⊤ := by
  have key : ∀ r, OccursTimes σ ρ r → (r : ℕ∞) * m ≤ A ⊤ := by
    rintro r ⟨S, T, h1, h2, h3⟩
    have hi : ∀ (i : ℕ) (hi : i < r), ((i + 1 : ℕ) : ℕ∞) * m ≤ A (S ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero =>
        intro hi
        have := hstep _ _ (h1 ⟨0, hi⟩) (h3 ⟨0, hi⟩)
        simpa using le_trans le_add_self this
      | succ i ih =>
        intro hi
        have h4 := ih (by omega)
        have h5 := hmono _ _ (h2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))
        have h6 := hstep _ _ (h1 ⟨i + 1, hi⟩) (h3 ⟨i + 1, hi⟩)
        refine le_trans ?_ h6
        have : (((i + 1 + 1 : ℕ)) : ℕ∞) * m = ((i + 1 : ℕ) : ℕ∞) * m + m := by
          push_cast; ring
        rw [this]
        exact add_le_add (h4.trans h5) le_rfl
    rcases r with _ | r
    · simp
    · exact (hi r (by omega)).trans (hmono _ _ le_top)
  unfold jhMult
  rw [ENat.iSup_mul]
  refine iSup_le fun r => ?_
  rw [ENat.iSup_mul]
  exact iSup_le fun hr => key r hr

end GlobalTheory.CompanionTheory.CsStages
