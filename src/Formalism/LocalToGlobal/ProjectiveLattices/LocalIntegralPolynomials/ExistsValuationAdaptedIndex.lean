import Formalism.LocalToGlobal.ProjectiveLattices.LocalIntegralPolynomials.LocStructSt
import ReciprocityTheory.SemistableReduction.AlgAll

noncomputable section

namespace Formalism.L2.Pj.LocAlg

open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial

variable {Ω : Type} [Field Ω] {D N : ℕ}

def yv (jc : Fin (N + 1)) (x : Fin N → Ω) : Fin (N + 1) → Ω :=
  Fin.insertNth (α := fun _ => Ω) jc 1 x

theorem yv_self (jc : Fin (N + 1)) (x : Fin N → Ω) : yv jc x jc = 1 := by
  unfold yv
  exact Fin.insertNth_apply_same (α := fun _ => Ω) jc 1 x



theorem sImg_succAbove (jc : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) (k : Fin N) :
    sImg jc x (i, jc.succAbove k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inr (i, k))) := by
  unfold sImg
  congr 1
  exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar D N) Ω) jc _ _ k


theorem exists_valuation_adapted_index (jc : Fin (N + 1)) (x : Fin N → Ω) (W : ValuationSubring Ω) :
    ∃ j0, yv jc x j0 ≠ 0 ∧ ∀ j, yv jc x j / yv jc x j0 ∈ W := by
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ (fun j => W.valuation (yv jc x j))
    ⟨jc, Finset.mem_univ _⟩
  have h1 : W.valuation (yv jc x jc) = 1 := by rw [yv_self, map_one]
  have hne : W.valuation (yv jc x j0) ≠ 0 := by
    intro h
    have hle := hj0 jc (Finset.mem_univ _)
    rw [h, h1] at hle
    exact one_ne_zero (le_antisymm hle zero_le')
  refine ⟨j0, fun h => hne (by rw [h, map_zero]), fun j => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
  exact (div_le_one₀ (zero_lt_iff.mpr hne)).mpr (hj0 j (Finset.mem_univ _))

def tj (jc j0 : Fin (N + 1)) (x : Fin N → Ω) : SVar D N → OmS Ω D N :=
  Sum.elim (fun _ => sImg jc x (0, j0)) (fun p => sImg jc x (p.1, j0.succAbove p.2))

def qj (jc j0 : Fin (N + 1)) (x : Fin N → Ω) (p : TVar D N) : MvPolynomial (SVar D N) Ω :=
  Fin.insertNth (α := fun _ => MvPolynomial (SVar D N) Ω) j0
    (if p.1 = 0 then X (Sum.inl ())
      else -∑ k, C (yv jc x (j0.succAbove k) / yv jc x j0) * X (Sum.inr (p.1, k)))
    (fun k => X (Sum.inr (p.1, k))) p.2

variable {jc j0 : Fin (N + 1)} {x : Fin N → Ω}


def intPoly (σ : Type) (W : Subring Ω) : Subring (MvPolynomial σ Ω) where
  carrier := {P | ∀ e, P.coeff e ∈ W}
  mul_mem' := by
    intro P Q hP hQ e
    classical
    rw [coeff_mul]
    exact sum_mem fun d _ => W.mul_mem (hP _) (hQ _)
  one_mem' := by
    intro e
    classical
    rw [coeff_one]
    split_ifs
    exacts [W.one_mem, W.zero_mem]
  add_mem' := by
    intro P Q hP hQ e
    rw [coeff_add]
    exact W.add_mem (hP e) (hQ e)
  zero_mem' := by
    intro e
    rw [coeff_zero]
    exact W.zero_mem
  neg_mem' := by
    intro P hP e
    rw [coeff_neg]
    exact W.neg_mem (hP e)

theorem mem_intPoly {σ : Type} {W : Subring Ω} {P : MvPolynomial σ Ω} :
    P ∈ intPoly σ W ↔ ∀ e, P.coeff e ∈ W :=
    Iff.rfl

theorem C_mem_intPoly {σ : Type} {W : Subring Ω} {a : Ω} (ha : a ∈ W) : (C a : MvPolynomial σ Ω) ∈ intPoly σ W := by
  intro e
  classical
  rw [coeff_C]
  split_ifs
  exacts [ha, W.zero_mem]

theorem X_mem_intPoly {σ : Type} {W : Subring Ω} (s : σ) : (X s : MvPolynomial σ Ω) ∈ intPoly σ W := by
  intro e
  classical
  rw [coeff_X']
  split_ifs
  exacts [W.one_mem, W.zero_mem]



end Formalism.L2.Pj.LocAlg
