module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KFiniteDerivativesFiniteSpan
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.UnitBoxWords

open PI.UpqRep _root_.Gp91.GlobalTheory.DerivedAction

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}

def lieSubspace (k r : ℕ) : Submodule ℝ (Mx k r) where
  carrier := {X | InLieHpk k r X}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_setOf_eq, InLieHpk] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp [InLieHpk]
  smul_mem' := fun c X hX => by
    simp only [Set.mem_setOf_eq, InLieHpk] at *
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem exists_box_generators (k r : ℕ) : ∃ (J : Type) (_ : Fintype J) (Z : J → Mx k r),
    (∀ j, InLieHpk k r (Z j)) ∧ ∀ Y, B.unitLie k r Y → ∃ c : J → ℝ, (∀ j, |c j| ≤ 1) ∧ Y = ∑ j, c j • Z j :=
  _root_.GlobalTheory.UnitBoxWords.exists_box_generators k r

theorem dsig_sum_letter {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    {J : Type} [Fintype J] {Z : J → Mx k r} (hZ : ∀ j, InLieHpk k r (Z j)) (c : J → ℝ) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ (∑ j, c j • Z j) v = ∑ j, (c j : ℂ) • dsig (k := k) (r := r) σ (Z j) v :=
  _root_.GlobalTheory.UnitBoxWords.dsig_sum_letter hZ c hv

theorem dsig_sum_vec (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    {v : ι → R.H} (hv : ∀ i, v i ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • dsig (k := k) (r := r) R.σ X (v i) :=
  _root_.GlobalTheory.UnitBoxWords.dsig_sum_vec R hX s c hv

theorem box_words_fintype (hK : PI.KFinSmooth) (R : Rep k r) (hR : R.IsDG ε mu) {x : R.H} (hx : x ∈ R.TK) (m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (xs : ι → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r),
      (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : ι → ℝ, (∀ i, |co i| ≤ 1) ∧
        dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i :=
  _root_.GlobalTheory.UnitBoxWords.box_words_fintype hK R (GlobalTheory.isDS_of_isDG hR) hx m

theorem box_words : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ x ∈ R.TK, ∀ m : ℕ, ∃ (M : ℕ) (xs : Fin M → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : Fin M → ℝ, (∀ i, |co i| ≤ 1) ∧ PI.UpqRep.dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i :=
  fun h1 k r ε mu R h2 =>
    _root_.GlobalTheory.UnitBoxWords.box_words h1 k r ε mu R (GlobalTheory.isDS_of_isDG h2)

end GlobalTheory.UnitBoxWords
