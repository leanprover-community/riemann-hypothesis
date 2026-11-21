import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField

set_option autoImplicit false

noncomputable section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.NX
open scoped TensorProduct
open Classical

namespace GlobalTheory.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

export GlobalTheory.TowerCov (IsLevN LevN LevN.one modN KgW InKN IsLevDat IsCompFn IsLevG serAt TowerRat AdaptL TowerInt)

theorem IsLevN.insert {E : ExpSet D} {N p : ℕ} (hN : IsLevN E N) (hp : p.Prime)
    (h : p ≠ 2 ∧ Nat.Coprime p E.l ∧ (∀ a, p ≠ E.pde a) ∧ (∀ a, p ≠ E.gp a) ∧ D.host.cls p = .splitK ∧
      ¬ p ∣ Ideal.absNorm D.host.ccK) : ∃ N', IsLevN E N' ∧ N ∣ N' ∧ p ∣ N' := by
  by_cases hd : p ∣ N
  · exact ⟨N, hN, dvd_rfl, hd⟩
  · refine ⟨p * N, ⟨mul_ne_zero hp.ne_zero hN.1, fun q hq hq' => ?_, ?_⟩, dvd_mul_left _ _, dvd_mul_right _ _⟩
    · rcases (Nat.Prime.dvd_mul hq).1 hq' with h1 | h1
      · rw [(Nat.prime_dvd_prime_iff_eq hq hp).1 h1]
        exact h
      · exact hN.2.1 q hq h1
    · exact (Nat.squarefree_mul ((Nat.Prime.coprime_iff_not_dvd hp).2 hd)).2 ⟨hp.prime.squarefree, hN.2.2⟩



def halfLat (E : ExpSet D) (e : AE D) : AddSubgroup (WO E.V E.W) where
  carrier := {x | IsHalf (cA D e) x ∧ IsIntM (frMapO E.V E.W E.βV E.βW x)}
  zero_mem' := by
    refine ⟨fun i j => mul_zero _, fun i j => ?_⟩
    unfold frMapO
    rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]
    exact zero_mem _
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show cA D e * (a i j + b i j) = a i j + b i j
      rw [mul_add, ha i j, hb i j]
    · unfold frMapO
      rw [Matrix.map_add _ (toEAf D).map_add, Matrix.mul_add, Matrix.add_mul]
      exact add_mem (ha' i j) (hb' i j)
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show cA D e * (-a i j) = -a i j
      rw [mul_neg, ha i j]
    · unfold frMapO
      rw [Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul]
      exact neg_mem (ha' i j)

def halfLatInd (E : ExpSet D) (e : AE D) : WO E.V E.W → ℂ := fun x => if x ∈ halfLat E e then 1 else 0




theorem IsCompFn.const (E : ExpSet D) (N : ℕ) (z : ℂ) : IsCompFn E N fun _ => z :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem IsCompFn.map₂ {E : ExpSet D} {N : ℕ} {c c' : GA D E.W → ℂ} (h : IsCompFn E N c) (h' : IsCompFn E N c')
    (f : ℂ → ℂ → ℂ) : IsCompFn E N fun g => f (c g) (c' g) :=
  ⟨fun g g' e => by rw [h.det g g' e, h'.det g g' e], fun γ hγ g => by rw [h.left γ hγ, h'.left γ hγ],
    fun u hu g => by rw [h.arch u hu, h'.arch u hu], fun κ hκ g => by rw [h.right κ hκ, h'.right κ hκ]⟩

example (E : ExpSet D) : (LevN.one E).1 = 1 := rfl

example (E : ExpSet D) : AdaptL E 1 :=
  ⟨1, one_mem _, 1, (mul_one _).symm, fun _ _ _ _ a b => by
    have h1 : Formalism.L2.Theta.mt E.V 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
    rw [h1, sub_self]
    simp⟩

example {E : ExpSet D} {O : Type} [CommRing O] {C : CoefLat E O} {Base : Set (GA D E.W → ℂ)} {L1 FO : Subfield ℂ}
    (T : GlobalTheory.TowerCov.TowerRat E C Base L1 FO) : GlobalTheory.Tow.TowerRat E C Base L1 FO := T

end GlobalTheory.Tow

end

end
