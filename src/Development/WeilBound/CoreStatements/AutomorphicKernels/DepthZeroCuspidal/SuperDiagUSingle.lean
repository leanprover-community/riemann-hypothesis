import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.IsLevelOne
import GroundTheory.AutomorphicForms.Iwasawa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Basics
variable {m : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem corner_cs_cs (g : GL (Fin m) k) (i j : Fin m) :
    (corner g : Matrix (Fin (m+1)) (Fin (m+1)) k) i.castSucc j.castSucc = (g : Matrix _ _ k) i j := by
  simp [corner, val_emb₂, stdSum, Matrix.reindex_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem corner_cs_last (g : GL (Fin m) k) (i : Fin m) :
    (corner g : Matrix (Fin (m+1)) (Fin (m+1)) k) i.castSucc (Fin.last m) = 0 := by
  simp [corner, val_emb₂, stdSum, Matrix.reindex_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem corner_last_cs (g : GL (Fin m) k) (j : Fin m) :
    (corner g : Matrix (Fin (m+1)) (Fin (m+1)) k) (Fin.last m) j.castSucc = 0 := by
  simp [corner, val_emb₂, stdSum, Matrix.reindex_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem corner_last_last (g : GL (Fin m) k) :
    (corner g : Matrix (Fin (m+1)) (Fin (m+1)) k) (Fin.last m) (Fin.last m) = 1 := by
  simp [corner, val_emb₂, stdSum, Matrix.reindex_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem corner_mul (g h : GL (Fin m) k) : corner (g * h) = corner g * corner h := by
  simp only [corner]
  rw [← map_mul]
  simp

theorem mem_fixed_iff {V : Type} [AddCommGroup V] [Module ℂ V] {G : Type} [Group G]
    (ρ : Representation ℂ G V) (H : Subgroup G) (x : V) :
    x ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h x = x := by
  constructor
  · intro hx h hh
    have := hx ⟨h, hh⟩
    simpa using this
  · intro hx h
    simpa using hx h h.2

theorem rho_mul {V : Type} [AddCommGroup V] [Module ℂ V] {G : Type} [Group G]
    (ρ : Representation ℂ G V) (a b : G) (x : V) : ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul, Module.End.mul_apply]

def stabG {V : Type} [AddCommGroup V] [Module ℂ V] {G : Type} [Group G]
    (ρ : Representation ℂ G V) (x : V) : Subgroup G where
  carrier := {g | ρ g x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [rho_mul, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [← rho_mul, inv_mul_cancel, map_one, Module.End.one_apply]


theorem val_eq_unif {c : kˣ} (hc : ord k c = 1) : valuation k (c : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact uniformizer_ne_zero hx.symm
  set u := Units.mk0 x hx0
  have h1 : ord k u = 1 := ord_eq_one (by simpa [u] using hx)
  have h3 : ord k (u * u⁻¹) = 0 := by rw [mul_inv_cancel]; exact ord_eq_zero (by simp)
  have h2 : ord k (c * u⁻¹) = 0 := by
    rw [ord_mul] at h3 ⊢
    omega
  have h4 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀] at h4
  have hu0 : valuation k (u : k) ≠ 0 := by simp [u, hx0]
  rw [← hx]
  have := (mul_inv_eq_one₀ hu0).1 h4
  simpa [u] using this



end Basics

section Mask
variable {N : ℕ} (P : Fin N → Fin N → Prop) [DecidableRel P]

def maskM (X : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k := fun a b => if P a b then X a b else 0

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem maskM_mul (hP : ∀ a b c, P a b → P b c → False) (X Y : Matrix (Fin N) (Fin N) k) :
    maskM P X * maskM P Y = 0 := by
  ext a c
  simp only [Matrix.mul_apply, maskM, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h1 : P a b
  · by_cases h2 : P b c
    · exact (hP a b c h1 h2).elim
    · simp [h2]
  · simp [h1]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem maskM_add (X Y : Matrix (Fin N) (Fin N) k) : maskM P (X + Y) = maskM P X + maskM P Y := by
  ext a b
  simp only [maskM, Matrix.add_apply]
  split_ifs <;> simp

def U (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k) : GL (Fin N) k :=
  ⟨1 + maskM P X, 1 - maskM P X, by simp [add_mul, mul_sub, maskM_mul P hP],
    by simp [sub_mul, mul_add, maskM_mul P hP]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem U_val (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k) :
    ((U P hP X : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = 1 + maskM P X := rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem U_inv_val (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k) :
    (((U P hP X)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = 1 - maskM P X := rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem U_mul (hP : ∀ a b c, P a b → P b c → False) (X Y : Matrix (Fin N) (Fin N) k) :
    U P hP X * U P hP Y = U P hP (X + Y) := by
  apply Units.ext
  rw [Units.val_mul, U_val, U_val, U_val, maskM_add, add_mul, one_mul, mul_add, mul_one, maskM_mul P hP]
  abel

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem U_mem_unipB (hP : ∀ a b c, P a b → P b c → False) (hlt : ∀ a b, P a b → a < b)
    (X : Matrix (Fin N) (Fin N) k) : U P hP X ∈ unipB k (Fin N) := by
  rw [mem_unipB]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [U_val, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hji), maskM,
      if_neg (fun h => absurd (hlt i j h) (not_lt.2 hji.le)), add_zero]
  · rw [U_val, Matrix.add_apply, Matrix.one_apply_eq, maskM, if_neg (fun h => lt_irrefl _ (hlt i i h)), add_zero]



omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem diag_conj_U (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k) (τ : Fin N → kˣ) :
    GroundTheory.Automorphic.Iwasawa.diagGL k N τ * U P hP X * (GroundTheory.Automorphic.Iwasawa.diagGL k N τ)⁻¹ =
      U P hP (Matrix.of fun a b => (τ a : k) * X a b * ((τ b : k))⁻¹) := by
  apply Units.ext
  rw [← map_inv, Units.val_mul, Units.val_mul, GroundTheory.Automorphic.Iwasawa.coe_diagGL,
    GroundTheory.Automorphic.Iwasawa.coe_diagGL, U_val, U_val]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, maskM, Matrix.one_apply, Pi.inv_apply, Units.val_inv_eq_inv_val, Matrix.of_apply]
  by_cases hab : a = b
  · subst hab
    split_ifs <;> field_simp
  · split_ifs <;> simp_all

end Mask

section Rep
variable {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]



omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem superDiag_U_single {M : ℕ} (p : Fin M)
    (hP : ∀ a b c : Fin (M + 1), (a = p.castSucc ∧ b = p.succ) → (b = p.castSucc ∧ c = p.succ) → False)
    (y : k) : superDiag (U (fun a b : Fin (M + 1) => a = p.castSucc ∧ b = p.succ) hP (Matrix.of fun _ _ => y)) = y := by
  unfold superDiag
  rw [Finset.sum_eq_single p.castSucc]
  · rw [Finset.sum_eq_single p.succ]
    · simp [U_val, maskM, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := p)).ne]
    · intro j hj hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc] at hj
      exact absurd (Fin.ext (by simp [hj])) hne
    · simp
  · intro i _ hne
    refine Finset.sum_eq_zero fun j hj => ?_
    have hij : i ≠ j := by
      rintro rfl
      simp at hj
    rw [U_val, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add, maskM, if_neg (fun h => hne h.1)]
  · simp


end Rep

section Parab
variable {M : ℕ}

def dTwo (p : Fin M) : Fin 2 → ℕ := ![p.val + 1, M - p.val]

theorem dTwo_sum (p : Fin M) : ∑ a, dTwo p a = M + 1 := by
  have := p.isLt
  simp [dTwo, Fin.sum_univ_two]
  omega

def eTwo (p : Fin M) : (Σ a, Fin (dTwo p a)) ≃ Fin (M + 1) := stdBlocks (dTwo p) (dTwo_sum p)

theorem eTwo_zero (p : Fin M) (i : Fin (dTwo p 0)) : ((eTwo p ⟨0, i⟩ : Fin (M + 1)) : ℕ) ≤ p.val := by
  have h := stdBlocks_val (dTwo p) (dTwo_sum p) 0 i
  have hi := i.isLt
  simp only [dTwo] at hi
  simp only [eTwo, h]
  simp
  simp at hi
  omega

theorem eTwo_one (p : Fin M) (j : Fin (dTwo p 1)) : p.val < ((eTwo p ⟨1, j⟩ : Fin (M + 1)) : ℕ) := by
  have h := stdBlocks_val (dTwo p) (dTwo_sum p) 1 j
  simp only [eTwo, h]
  simp [dTwo]
  omega

def PB (p : Fin M) (a b : Fin (M + 1)) : Prop := a.val ≤ p.val ∧ p.val < b.val

instance (p : Fin M) : DecidableRel (PB p) := fun a b => by unfold PB; infer_instance

theorem hPB (p : Fin M) : ∀ a b c, PB p a b → PB p b c → False := by
  rintro a b c ⟨-, h1⟩ ⟨h2, -⟩
  omega


theorem PB_e (p : Fin M) (a b : Fin 2) (i : Fin (dTwo p a)) (j : Fin (dTwo p b)) :
    PB p (eTwo p ⟨a, i⟩) (eTwo p ⟨b, j⟩) ↔ a = 0 ∧ b = 1 := by
  fin_cases a <;> fin_cases b
  · have := eTwo_zero p j
    simp [PB]
    omega
  · have := eTwo_zero p i
    have := eTwo_one p j
    simp [PB]
    omega
  · have := eTwo_one p i
    simp [PB]
    omega
  · have := eTwo_one p i
    simp [PB]
    omega

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem one_e (p : Fin M) (a b : Fin 2) (i : Fin (dTwo p a)) (j : Fin (dTwo p b)) :
    (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) k) (eTwo p ⟨a, i⟩) (eTwo p ⟨b, j⟩) =
      if (⟨a, i⟩ : Σ a, Fin (dTwo p a)) = ⟨b, j⟩ then 1 else 0 := by
  rw [Matrix.one_apply]
  exact if_congr (eTwo p).injective.eq_iff rfl rfl

theorem fin_two_lt {a b : Fin 2} (h : b < a) : a = 1 ∧ b = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem U_mem_unipRad (p : Fin M) (X : Matrix (Fin (M + 1)) (Fin (M + 1)) k) :
    U (PB p) (hPB p) X ∈ unipRad k (eTwo p) := by
  rw [mem_unipRad]
  refine ⟨?_, ?_⟩
  · rw [mem_parab_iff]
    intro a b i j hba
    obtain ⟨rfl, rfl⟩ := fin_two_lt hba
    have hP' : ¬ PB p (eTwo p ⟨1, i⟩) (eTwo p ⟨0, j⟩) := by rw [PB_e]; simp
    rw [U_val, Matrix.add_apply, one_e, maskM, if_neg hP']
    simp
  · intro a i j
    have hP' : ¬ PB p (eTwo p ⟨a, i⟩) (eTwo p ⟨a, j⟩) := by rw [PB_e]; rintro ⟨rfl, h⟩; simp at h
    rw [U_val, Matrix.add_apply, one_e, maskM, if_neg hP']
    simp [Matrix.one_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem unipRad_eq_U (p : Fin M) {g : GL (Fin (M + 1)) k} (hg : g ∈ unipRad k (eTwo p)) :
    (g : Matrix (Fin (M + 1)) (Fin (M + 1)) k) = 1 + maskM (PB p) (g : Matrix (Fin (M + 1)) (Fin (M + 1)) k) := by
  obtain ⟨hpar, hdiag⟩ := mem_unipRad.1 hg
  rw [mem_parab_iff] at hpar
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := (eTwo p).surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := (eTwo p).surjective y
  rw [Matrix.add_apply, one_e, maskM]
  by_cases hab : a = b
  · subst hab
    have hP' : ¬ PB p (eTwo p ⟨a, i⟩) (eTwo p ⟨a, j⟩) := by rw [PB_e]; rintro ⟨rfl, h⟩; simp at h
    rw [if_neg hP', hdiag]
    simp [Matrix.one_apply]
  · have hne : ¬ ((⟨a, i⟩ : Σ a, Fin (dTwo p a)) = ⟨b, j⟩) := fun h => hab (congrArg Sigma.fst h)
    rw [if_neg hne, zero_add]
    rcases lt_or_gt_of_ne hab with h | h
    · have : a = 0 ∧ b = 1 := by
        obtain ⟨h1, h2⟩ := fin_two_lt h
        exact ⟨h2, h1⟩
      rw [if_pos ((PB_e p a b i j).2 this)]
    · have hP' : ¬ PB p (eTwo p ⟨a, i⟩) (eTwo p ⟨b, j⟩) := by rw [PB_e]; rintro ⟨rfl, rfl⟩; simp at h
      rw [if_neg hP', hpar a b i j h]

end Parab

section Main



end Main


end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
