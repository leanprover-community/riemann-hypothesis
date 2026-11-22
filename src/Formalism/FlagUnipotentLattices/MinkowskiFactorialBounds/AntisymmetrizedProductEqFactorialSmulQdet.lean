module

public import Mathlib
public import Formalism.RealPlaceAnalysis.StatementC
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd

@[expose] public section

open Formalism.REAL TensorProduct Finset

set_option linter.all false

noncomputable section

namespace Formalism.HermitianLatticeCounting.P

def orderedTermProduct {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ)
    (σ τ : Equiv.Perm (Fin n)) : A :=
  (List.ofFn fun k : Fin n => Tm E (arg k) (σ k) (τ k)).prod

def doublyAntisymmetrizedProduct {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ) : A :=
  ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E arg σ τ)

theorem list_prod_ofFn_update_adjacent {A : Type} [Ring A] {t : ℕ} (f g : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k) :
    (List.ofFn g).prod = ((List.ofFn f).take i).prod * (g ⟨i, by omega⟩ * g ⟨i + 1, hi⟩) *
      ((List.ofFn f).drop (i + 2)).prod := by
  have hg : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k := h
  have htake : (List.ofFn g).take i = (List.ofFn f).take i := by
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_take, List.getElem_ofFn]
      simp only [List.length_take, List.length_ofFn] at h1
      exact hg _ (by simp; omega) (by simp; omega)
  have hdrop : (List.ofFn g).drop (i + 2) = (List.ofFn f).drop (i + 2) := by
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_drop, List.getElem_ofFn]
      exact hg _ (by simp; omega) (by simp; omega)
  rw [← List.take_append_drop i (List.ofFn g), List.drop_eq_getElem_cons (by simp; omega),
    List.drop_eq_getElem_cons (by simp; omega), htake, List.getElem_ofFn, List.getElem_ofFn,
    show i + 1 + 1 = i + 2 from rfl, hdrop]
  simp only [List.prod_append, List.prod_cons, mul_assoc]

theorem mul_signed_four_sum_mul_eq {A : Type} [Ring A] (L R a1 a2 a3 a4 : A) :
    L * a1 * R - L * a2 * R - L * a3 * R + L * a4 * R = L * (a1 - a2 - a3 + a4) * R := by
  noncomm_ring

theorem antisymmetrizedProduct_eq_factorial_smul_qdet {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ) :
    doublyAntisymmetrizedProduct E (fun k => u - (k : ℂ)) = (n.factorial : ℂ) • qdet E u := by

  have hcol : ∀ (b : Fin n → Fin n) (τ : Equiv.Perm (Fin n)),
      qminor E id (b ∘ τ) u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E id b u := by
    cases n with
    | zero =>
      intro b τ
      rw [Subsingleton.elim τ 1]
      simp
    | succ m =>
      intro b τ
      have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        trivial
      revert b
      induction hτ using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        intro b
        rw [quantumMinor_adjacent_col_swap E hE id b i u, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := i)).ne]
        simp
      | one =>
        intro b
        simp
      | mul x y _ _ hx hy =>
        intro b
        show qminor E id ((b ∘ x) ∘ y) u = _
        rw [hy (b ∘ x), hx b]
        simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc]
        congr 1
        exact (Int.cast_commute _ _).eq
  simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
  have hin : ∀ τ : Equiv.Perm (Fin n), ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) *
      orderedTermProduct E (fun k => u - (k : ℂ)) σ τ = qminor E id (id ∘ τ) u := fun τ => rfl
  have hsq : ∀ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign τ : ℤ) : A) * qminor E id id u) = qminor E id id u := by
    intro τ
    rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one,
      one_mul]
  simp only [hin, hcol, hsq, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rfl

end Formalism.HermitianLatticeCounting.P
