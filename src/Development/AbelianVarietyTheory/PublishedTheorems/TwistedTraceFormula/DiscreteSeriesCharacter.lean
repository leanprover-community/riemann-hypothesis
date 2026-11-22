module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

@[expose] public section

open MeasureTheory Set Filter Matrix Polynomial GlobalTheory.Orb GlobalTheory.OpTrace
open GlobalTheory.AutomorphicL2Unitary (descend LeftInv mk measurable_mk)
open Formalism.REAL (UJ KG muK Jm)
open Formalism.QuantumDeterminants (IsHCParam IsCRepOn)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsDS UJset)
open GlobalTheory.FlagMeas (IsIsoFlag flagM)
open GlobalTheory.RealInd (IsIrrAdm IsIndModel IndModule Flag groupRep indFun leviOne mats)
open scoped ENNReal NNReal Topology

noncomputable section

namespace GlobalTheory.HCChar

section Disc

variable {n : ℕ}

end Disc

section Cartan

variable {n : ℕ} {ε : Fin n → Bool}

theorem continuous_ujMat : Continuous (ujMat ε) := Units.continuous_val.comp continuous_subtype_val

end Cartan

section Char

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

end Char

section Torus

variable {n : ℕ}

def torusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) : UJ ε :=
  ⟨⟨diagonal fun a => Complex.exp (θ a * Complex.I), diagonal fun a => Complex.exp (-(θ a * Complex.I)),
    by simp [← Complex.exp_add], by simp [← Complex.exp_add]⟩, by
      change _ᴴ * Jm ε * _ = Jm ε
      simp only [Jm, diagonal_conjTranspose, diagonal_mul_diagonal]
      congr 1
      funext a
      rw [mul_right_comm, Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp⟩

def wtVal (μ θ : Fin n → ℝ) : ℂ := Complex.exp ((∑ a, μ a * θ a : ℝ) * Complex.I)

def weylDenom (θ : Fin n → ℝ) : ℂ :=
  ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (((θ a - θ b) / 2 : ℝ) * Complex.I) -
    Complex.exp ((-((θ a - θ b) / 2) : ℝ) * Complex.I))

def compactWeyl (ε : Fin n → Bool) : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter fun w => ε ∘ w = ε

def halfDim (ε : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun a => ε a = true).card * (Finset.univ.filter fun a => ε a = false).card

def dsChar (ε : Fin n → Bool) (lam θ : Fin n → ℝ) : ℂ :=
  (-1) ^ halfDim ε * (∑ w ∈ compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * wtVal (lam ∘ w.symm) θ) / weylDenom θ

theorem weylDenom_mul (θ : Fin n → ℝ) : weylDenom θ * wtVal (fun _ => ((n : ℝ) - 1) / 2) θ =
    ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (θ a * Complex.I) - Complex.exp (θ b * Complex.I)) := by
  have h : ∑ a, ((n : ℝ) - 1) / 2 * θ a = ∑ a, ∑ b ∈ Finset.Ioi a, (θ a + θ b) / 2 := by
    have h1 : ∑ a, ∑ b ∈ Finset.Ioi a, θ b = ∑ b, ∑ _a ∈ Finset.Iio b, θ b :=
      Finset.sum_comm' (by simp)
    simp only [← Finset.sum_div, Finset.sum_add_distrib, h1, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio,
      nsmul_eq_mul]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := a.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [weylDenom, wtVal, h]
  simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 2 <;> push_cast <;> ring

theorem dsChar_eq (ε : Fin n → Bool) {lam : Fin n → ℝ} {m : Fin n → ℤ} (hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a)
    (θ : Fin n → ℝ) : dsChar ε lam θ = (-1) ^ halfDim ε *
      (∑ w ∈ compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, Complex.exp (θ a * Complex.I) ^ m (w.symm a)) /
        ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (θ a * Complex.I) - Complex.exp (θ b * Complex.I)) := by
  rw [dsChar, ← weylDenom_mul, ← mul_div_mul_right _ _ (c := wtVal (fun _ => ((n : ℝ) - 1) / 2) θ) (Complex.exp_ne_zero _),
    mul_assoc, Finset.sum_mul]
  congr 2
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_assoc, wtVal, wtVal, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  simp only [← add_mul, Function.comp, hm, ← Complex.exp_int_mul, ← Complex.exp_sum, Complex.ofReal_sum,
    Finset.sum_mul]
  simp [mul_assoc]

end Torus

end GlobalTheory.HCChar

namespace GlobalTheory.Published

open GlobalTheory.HCChar

end GlobalTheory.Published
