import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmu
import Mathlib
import Formalism.PeriodIntegrals.UpqRep

section
namespace Formalism.FourierDecayAlt.P.CutBP.Jmu

open Formalism.FourierDecayAlt MeasureTheory Finset
open scoped ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def Present (F : JFam P.k P.r Wp Wq) (μ : Fin (2 * P.r + P.k + 1) → ℤ) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam (lamOf F.sh μ) ∧ (F.A μ).l (F.A μ).w0 ≠ 0 ∧ (F.A μ).l' (F.A μ).w0 ≠ 0




def NormDeg (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Present F μ →
    TBB.jN2 p (F.J p.T.base μ) = ENNReal.ofReal (c * (F.A μ).deg p.T.base.μG)

def DegPos (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Present F μ → 0 < (F.A μ).deg p.T.base.μG

def DegRatio (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∀ μ (I : Finset (Fin (2 * P.r + P.k + 1))), I.card = P.r + 1 → LatticeNorms.N1 (μ - lam0) ≤ q0 →
    LatticeNorms.N1 (μ + LatticeNorms.eI I - lam0) ≤ q0 → Present F μ → Present F (μ + LatticeNorms.eI I) →
    (F.A (μ + LatticeNorms.eI I)).deg p.T.base.μG ≤
      (Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) * (F.A μ).deg p.T.base.μG


end

end Formalism.FourierDecayAlt.P.CutBP.Jmu
end

section
namespace Formalism.FourierDecayAlt.P.CutBP.JmuHC

open Finset

theorem prod_one_add_inv_le (D : Finset ℕ) (h0 : 0 ∉ D) : ∏ d ∈ D, (1 + 1 / (d : ℝ)) ≤ D.card + 1 := by
  induction D using Finset.induction_on_max with
  | empty => simp
  | insert m D hlt ih =>
    have hm : m ∉ D := fun h => lt_irrefl _ (hlt m h)
    have h0' : 0 ∉ D := fun h => h0 (mem_insert_of_mem h)
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun e => h0 (e ▸ mem_insert_self m D)
    have hcard : D.card + 1 ≤ m := by
      have hsub : D ⊆ (range m).erase 0 := fun x hx =>
        mem_erase.2 ⟨fun e => h0' (e ▸ hx), mem_range.2 (hlt x hx)⟩
      have := card_le_card hsub
      rw [card_erase_of_mem (mem_range.2 hm0), card_range] at this
      omega
    rw [prod_insert hm, card_insert_of_notMem hm]
    have ih' := ih h0'
    have hP : 0 ≤ ∏ d ∈ D, (1 + 1 / (d : ℝ)) := prod_nonneg fun d _ => by positivity
    have hc : ((D.card : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hcard
    have hc0 : (0 : ℝ) < (D.card : ℝ) + 1 := by positivity
    have h1 : 1 + 1 / (m : ℝ) ≤ 1 + 1 / ((D.card : ℝ) + 1) := by
      have := one_div_le_one_div_of_le hc0 hc
      linarith
    calc (1 + 1 / (m : ℝ)) * ∏ d ∈ D, (1 + 1 / (d : ℝ))
        ≤ (1 + 1 / ((D.card : ℝ) + 1)) * ((D.card : ℝ) + 1) :=
          mul_le_mul h1 ih' hP (by positivity)
      _ = ((D.card + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          field_simp

variable {n : ℕ}

theorem prod_ratio_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (s : Fin n) (T : Finset (Fin n)) (hs : s ∉ T) :
    ∏ t ∈ T, |x s + 1 - x t| / |x s - x t| ≤ n := by
  classical
  have hne : ∀ t ∈ T, x s ≠ x t := fun t ht e => hs (hinj e ▸ ht)
  rw [← prod_filter_mul_prod_filter_not T (fun t => x t < x s)]

  have hlow : ∏ t ∈ T.filter (fun t => ¬ x t < x s), |x s + 1 - x t| / |x s - x t| ≤ 1 := by
    apply prod_le_one (fun t _ => by positivity)
    intro t ht
    obtain ⟨ht, hlt⟩ := mem_filter.1 ht
    have hgt : x s < x t := lt_of_le_of_ne (not_lt.1 hlt) (hne t ht)
    obtain ⟨m, hmv⟩ := hint t s
    have hm1 : (1 : ℝ) ≤ x t - x s := by
      rw [hmv]
      have : (0 : ℤ) < m := by exact_mod_cast (hmv ▸ sub_pos.2 hgt)
      exact_mod_cast this
    rw [div_le_one (abs_pos.2 (sub_ne_zero.2 (hne t ht)))]
    rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    linarith

  set Tp := T.filter (fun t => x t < x s) with hTp
  let dN : Fin n → ℕ := fun t => (⌊x s - x t⌋).toNat
  have hdN : ∀ t ∈ Tp, ((dN t : ℕ) : ℝ) = x s - x t ∧ 1 ≤ x s - x t := by
    intro t ht
    obtain ⟨-, hlt⟩ := mem_filter.1 ht
    obtain ⟨m, hmv⟩ := hint s t
    have hm0 : (0 : ℤ) < m := by exact_mod_cast (hmv ▸ sub_pos.2 hlt)
    refine ⟨?_, ?_⟩
    · simp only [dN, hmv, Int.floor_intCast]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0.le]
    · rw [hmv]; exact_mod_cast hm0
  have hinjOn : Set.InjOn dN Tp := by
    intro t ht t' ht' e
    have h1 := (hdN t ht).1
    have h2 := (hdN t' ht').1
    apply hinj
    have : x s - x t = x s - x t' := by rw [← h1, ← h2, e]
    linarith
  have hup : ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t| = ∏ d ∈ Tp.image dN, (1 + 1 / (d : ℝ)) := by
    rw [prod_image hinjOn]
    refine prod_congr rfl fun t ht => ?_
    obtain ⟨h1, h2⟩ := hdN t ht
    rw [h1, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    field_simp
    ring
  have hD0 : 0 ∉ Tp.image dN := by
    intro h
    obtain ⟨t, ht, e⟩ := mem_image.1 h
    have h1 := hdN t ht
    rw [e] at h1
    simp at h1
    linarith [h1.1, h1.2]
  have hbound := prod_one_add_inv_le (Tp.image dN) hD0
  rw [card_image_of_injOn hinjOn] at hbound
  have hTcard : Tp.card + 1 ≤ n := by
    have h1 : Tp.card ≤ T.card := card_le_card (filter_subset _ _)
    have h2 : T.card < n := by
      have := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨subset_univ T, fun e => hs (e ▸ mem_univ s)⟩)
      simpa using this
    omega
  have hupnn : 0 ≤ ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t| := prod_nonneg fun t _ => by positivity
  calc (∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t|) *
        ∏ t ∈ T.filter (fun t => ¬ x t < x s), |x s + 1 - x t| / |x s - x t|
      ≤ (∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t|) * 1 := mul_le_mul_of_nonneg_left hlow hupnn
    _ ≤ (n : ℝ) := by
        rw [mul_one, hup]
        refine hbound.trans ?_
        exact_mod_cast hTcard

def numHC (x : Fin n → ℝ) : ℝ := ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |x a - x b|




end Formalism.FourierDecayAlt.P.CutBP.JmuHC
end

section
namespace Formalism.FourierDecayAlt.P.CutBP.Jmu

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData MeasureTheory Finset
open scoped ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def DegHC (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Present F μ →
    (F.A μ).deg p.T.base.μG = C * PI.UpqRep.fdegHC (lamOf F.sh μ)

def FdegHpkHC : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)),
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w : H),
      Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → w ≠ 0 →
      PI.BesselPeriodGGP.fdegH μG σ w = C * PI.UpqRep.fdegHC lam


theorem fdegHC_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ PI.UpqRep.fdegHC x := by
  unfold PI.UpqRep.fdegHC
  refine div_nonneg (prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _)
    (prod_nonneg fun a _ => prod_nonneg fun b hb => ?_)
  have := (mem_filter.1 hb).2
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
  linarith




end

end Formalism.FourierDecayAlt.P.CutBP.Jmu
end
