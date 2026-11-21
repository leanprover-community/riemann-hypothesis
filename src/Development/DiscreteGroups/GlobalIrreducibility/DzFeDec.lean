import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFeCut
import Development.DiscreteGroups.GlobalIrreducibility.DzLcFin

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

def sv (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1))) (x : Mt g (m + 1)) (v : τ) : τ :=
  ∑ y : Gn g (m + 1), (ψ₀ (trace (x * (y : Mt g (m + 1)))) : ℂ) • τ.ρ y⁻¹ v

def Hm (b : Fin (m + 1) → ZMod g) : Mt g (m + 1) :=
  Matrix.of fun i k => if k = 0 then b i else (1 : Mt g (m + 1)) i k

def Ez : Mt g (m + 1) := Matrix.diagonal fun i : Fin (m + 1) => if i = 0 then (0 : ZMod g) else 1

variable (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1)))

theorem rho_inv_mul_apply (y a : Gn g (m + 1)) (v : τ) : τ.ρ (y⁻¹ * a⁻¹) (τ.ρ a v) = τ.ρ y⁻¹ v := by
  rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (τ.ρ a⁻¹), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem rho_mul_inv_apply (y a : Gn g (m + 1)) (v : τ) : τ.ρ a (τ.ρ (a⁻¹ * y⁻¹) v) = τ.ρ y⁻¹ v := by
  rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (τ.ρ a), ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

theorem sv_mul_right (x : Mt g (m + 1)) (a : Gn g (m + 1)) (v : τ) :
    sv ψ₀ τ (x * (a : Mt g (m + 1))) v = sv ψ₀ τ x (τ.ρ a v) := by
  unfold sv
  refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun y => ?_)
  rw [Equiv.coe_mulLeft]
  beta_reduce
  rw [Units.val_mul, ← Matrix.mul_assoc, _root_.mul_inv_rev, rho_inv_mul_apply]

theorem sv_mul_left (a : Gn g (m + 1)) (x : Mt g (m + 1)) (v : τ) :
    sv ψ₀ τ ((a : Mt g (m + 1)) * x) v = τ.ρ a (sv ψ₀ τ x v) := by
  unfold sv
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun y => ?_)
  have ht : trace ((a : Mt g (m + 1)) * x * (y : Mt g (m + 1))) =
      trace (x * ((y * a : Gn g (m + 1)) : Mt g (m + 1))) := by
    rw [Units.val_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm (x * (y : Mt g (m + 1))), ← Matrix.mul_assoc]
  rw [Equiv.coe_mulRight]
  beta_reduce
  rw [map_smul, _root_.mul_inv_rev, rho_mul_inv_apply, ht]

theorem sv_unit {γ : ℂ}
    (hγ : ∀ v : τ, ∑ᶠ y : Gn g (m + 1), (ψ₀ (Matrix.trace (y : Mt g (m + 1))) : ℂ) • τ.ρ y⁻¹ v = γ • v)
    (a : Gn g (m + 1)) (v : τ) : sv ψ₀ τ (a : Mt g (m + 1)) v = γ • τ.ρ a v := by
  have h1 : sv ψ₀ τ 1 v = γ • v := by
    unfold sv
    rw [← hγ v, finsum_eq_sum_of_fintype]
    simp only [Matrix.one_mul]
  have := sv_mul_left ψ₀ τ a 1 v
  rw [Matrix.mul_one, h1, map_smul] at this
  exact this

theorem sv_sum {ι : Type} (s : Finset ι) (x : Mt g (m + 1)) (f : ι → τ) :
    sv ψ₀ τ x (∑ i ∈ s, f i) = ∑ i ∈ s, sv ψ₀ τ x (f i) := by
  unfold sv
  simp_rw [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem sv_zero (x : Mt g (m + 1)) : sv ψ₀ τ x 0 = 0 := by
  simp [sv]

theorem Ez_mul_unip (u : Gn g (m + 1))
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1)) :
    (Ez : Mt g (m + 1)) * (u : Mt g (m + 1)) = Ez := by
  ext i k
  rw [Ez, Matrix.diagonal_mul]
  by_cases hi : i = 0
  · subst hi
    simp [Matrix.diagonal_apply]
  · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    have hb : GlobalTheory.FiniteGL.twoBlocks (m + 1) 1 k ≤ GlobalTheory.FiniteGL.twoBlocks (m + 1) 1 i := by
      simp only [GlobalTheory.FiniteGL.twoBlocks]
      split_ifs <;> omega
    have h0 := (GlobalTheory.FiniteGL.mem_unipRadical.1 hu) i k hb
    rw [Matrix.sub_apply, sub_eq_zero] at h0
    rw [if_neg hi, one_mul, h0, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp_all

theorem sv_Ez (hτ : IsCusp τ.character) (hm : 0 < m) (v : τ) : sv ψ₀ τ Ez v = 0 := by
  have h1 : ∀ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1),
      sv ψ₀ τ Ez v = sv ψ₀ τ Ez (τ.ρ (u : Gn g (m + 1)) v) := fun u => by
    rw [← sv_mul_right, Ez_mul_unip _ u.2]
  have hsum := DiscreteGroups.sglob.DzLc.sum_unip_eq_zero τ hτ (a := 1) one_pos (by omega)
  have h2 : (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1)) : ℂ) •
      sv ψ₀ τ Ez v = 0 := by
    calc _ = ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1),
          sv ψ₀ τ Ez (τ.ρ (u : Gn g (m + 1)) v) := by
          rw [← Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
      _ = sv ψ₀ τ Ez ((∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1),
          τ.ρ (u : Gn g (m + 1))) v) := by rw [LinearMap.sum_apply, sv_sum]
      _ = 0 := by rw [hsum, LinearMap.zero_apply, sv_zero]
  exact (smul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

theorem hm_mul (b c : Fin (m + 1) → ZMod g) :
    (Hm b : Mt g (m + 1)) * Hm c = Hm (fun i => b i * c 0 + if i = 0 then 0 else c i) := by
  ext i k
  rw [Matrix.mul_apply]
  by_cases hk : k = 0
  · subst hk
    rw [Fin.sum_univ_succ]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · simp [Hm, Matrix.one_apply, Fin.succ_ne_zero]
      exact Finset.sum_eq_zero (fun x _ => if_neg (Fin.succ_ne_zero x).symm)
    · simp [Hm, Matrix.one_apply, Fin.succ_ne_zero, Fin.succ_inj]
  · have hc : ∀ l, Hm c l k = (1 : Mt g (m + 1)) l k := fun l => by simp [Hm, hk]
    rw [Finset.sum_congr rfl (fun l _ => by rw [hc l]), ← Matrix.mul_apply, Matrix.mul_one]
    simp [Hm, hk]

theorem hm_zero : (Hm (0 : Fin (m + 1) → ZMod g) : Mt g (m + 1)) = Ez := by
  ext i k
  simp only [Hm, Ez, Matrix.of_apply, Pi.zero_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hk : k = 0
  · subst hk; split_ifs <;> simp_all
  · split_ifs <;> simp_all

theorem det_hm (b : Fin (m + 1) → ZMod g) : (Hm b : Mt g (m + 1)).det = b 0 := by
  have hl : (Hm b : Mt g (m + 1)).BlockTriangular OrderDual.toDual := by
    intro i k hik
    have hik' : i < k := hik
    have hk : k ≠ 0 := fun h => by subst h; exact absurd hik' (Fin.not_lt_zero i)
    simp [Hm, hk, Matrix.one_apply, ne_of_lt hik']
  rw [Matrix.det_of_lowerTriangular _ hl, Fin.prod_univ_succ]
  simp [Hm, Fin.succ_ne_zero]

def hmGL (b : Fin (m + 1) → ZMod g) (hb : b 0 ≠ 0) : Gn g (m + 1) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Hm b) (by rw [det_hm]; exact hb)

theorem hmGL_val (b : Fin (m + 1) → ZMod g) (hb : b 0 ≠ 0) : ((hmGL b hb : Gn g (m + 1)) : Mt g (m + 1)) = Hm b :=
  rfl

theorem sv_singular (hτ : IsCusp τ.character) (hm : 0 < m) (u : Gn g (m + 1)) (b : Fin (m + 1) → ZMod g)
    (hb : b 0 = 0) (v : τ) : sv ψ₀ τ ((u : Mt g (m + 1)) * Hm b) v = 0 := by
  set c : Fin (m + 1) → ZMod g := fun i => (if i = 0 then 1 else 0) - b i with hc
  have hc0 : c 0 ≠ 0 := by simp [hc, hb]
  have hprod : (Hm b : Mt g (m + 1)) * ((hmGL c hc0 : Gn g (m + 1)) : Mt g (m + 1)) = Ez := by
    rw [hmGL_val, hm_mul, ← hm_zero]
    congr 1
    funext i
    by_cases hi : i = 0
    · subst hi; simp [hc, hb]
    · simp [hc, hi, hb]
  have hH : (Hm b : Mt g (m + 1)) = Ez * (((hmGL c hc0)⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) := by
    rw [← hprod, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [sv_mul_left, hH, sv_mul_right, sv_Ez ψ₀ τ hτ hm, map_zero]

end DiscreteGroups.sglob.DzFe
end
end

section
noncomputable section

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime]

def psiC (ψ₀ : AddChar (ZMod g) Circle) : AddChar (ZMod g) ℂ where
  toFun x := (ψ₀ x : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [AddChar.map_add_eq_mul]

theorem psiC_apply (ψ₀ : AddChar (ZMod g) Circle) (x : ZMod g) : psiC ψ₀ x = (ψ₀ x : ℂ) := rfl

theorem sum_psi_mul (ψ₀ : AddChar (ZMod g) Circle) (hψ : ψ₀ ≠ 1) (c : ZMod g) :
    ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) = if c = 0 then (g : ℂ) else 0 := by
  split_ifs with hc
  · subst hc; simp [ZMod.card]
  · obtain ⟨s, hs⟩ : ∃ s, ψ₀ s ≠ 1 := by
      by_contra h
      push Not at h
      exact hψ (by ext s; rw [h s, AddChar.one_apply])
    have key : (ψ₀ s : ℂ) * ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) = ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight (s * c⁻¹)) _ _ (fun t => ?_)
      rw [Equiv.coe_addRight, add_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one, AddChar.map_add_eq_mul,
        Circle.coe_mul, mul_comm]
    have hs' : (ψ₀ s : ℂ) ≠ 1 := fun h => hs (Circle.ext (by simpa using h))
    have : ((ψ₀ s : ℂ) - 1) * ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) = 0 := by rw [sub_mul, key, one_mul, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hs')

theorem sum_pi_psi (ψ₀ : AddChar (ZMod g) Circle) (hψ : ψ₀ ≠ 1) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → ZMod g) :
    ∑ f : ι → ZMod g, (ψ₀ (∑ i, f i * c i) : ℂ) = if c = 0 then (g : ℂ) ^ Fintype.card ι else 0 := by
  have h1 : ∀ f : ι → ZMod g, (ψ₀ (∑ i, f i * c i) : ℂ) = ∏ i, (ψ₀ (f i * c i) : ℂ) := fun f => by
    have hs : ∀ s : Finset ι, psiC ψ₀ (∑ i ∈ s, f i * c i) = ∏ i ∈ s, psiC ψ₀ (f i * c i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [AddChar.map_zero_eq_one]
      | insert a s ha ih => rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, ih, Finset.prod_insert ha]
    exact hs Finset.univ
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i t => (ψ₀ (t * c i) : ℂ))]
  simp_rw [sum_psi_mul ψ₀ hψ]
  split_ifs with hc
  · subst hc
    simp
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      push Not at h
      exact hc (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end DiscreteGroups.sglob.DzFe
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

abbrev SIdx (m : ℕ) := {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2}

abbrev JIdx (m j : ℕ) := {i : Fin (m + 1) // (i : ℕ) ≤ j}

def Um (N : SIdx m → ZMod g) : Mt g (m + 1) :=
  Matrix.of fun i k => if i = k then 1 else if h : i < k then N ⟨(i, k), h⟩ else 0

theorem um_upper (N : SIdx m → ZMod g) : (Um N : Mt g (m + 1)).BlockTriangular id := by
  intro i k hik
  have hik' : k < i := hik
  simp [Um, ne_of_gt hik', not_lt_of_gt hik']

theorem det_um (N : SIdx m → ZMod g) : (Um N : Mt g (m + 1)).det = 1 := by
  rw [Matrix.det_of_upperTriangular (um_upper N)]
  simp [Um]

def umGL (N : SIdx m → ZMod g) : Gn g (m + 1) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Um N) (by rw [det_um]; exact one_ne_zero)

theorem umGL_val (N : SIdx m → ZMod g) : ((umGL N : Gn g (m + 1)) : Mt g (m + 1)) = Um N := rfl

theorem umGL_mem (N : SIdx m → ZMod g) : umGL N ∈ unipB (ZMod g) (Fin (m + 1)) := by
  rw [mem_unipB, umGL_val]
  exact ⟨fun i k hki => um_upper N hki, fun i => by simp [Um]⟩

def bcol {j : ℕ} (b : JIdx m j → ZMod g) : Fin (m + 1) → ZMod g :=
  fun i => if h : (i : ℕ) ≤ j then b ⟨i, h⟩ else 0

def j0 (m j : ℕ) : JIdx m j := ⟨0, by simp⟩

theorem bcol_zero {j : ℕ} (b : JIdx m j → ZMod g) : bcol b 0 = b (j0 m j) := by
  simp [bcol, j0]

theorem isColFix_hm {j : ℕ} (b : JIdx m j → ZMod g) (hb : bcol b 0 ≠ 0) : IsColFix j (hmGL (bcol b) hb) := by
  refine ⟨fun i k hk => ?_, fun i k hk hi => ?_⟩
  · have : k ≠ 0 := fun h => hk (by simp [h])
    simp [hmGL_val, Hm, this, Matrix.one_apply]
  · have : k = 0 := Fin.ext hk
    subst this
    simp [hmGL_val, Hm, bcol, not_le.2 hi]

variable (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1)))

theorem psi_neg_mul (s : ZMod g) : (ψ₀ (-s) : ℂ) * (ψ₀ s : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

theorem psi_add (a b : ZMod g) : (ψ₀ (a + b) : ℂ) = (ψ₀ a : ℂ) * (ψ₀ b : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

theorem lhs_term {γ : ℂ}
    (hγ : ∀ v : τ, ∑ᶠ y : Gn g (m + 1), (ψ₀ (Matrix.trace (y : Mt g (m + 1))) : ℂ) • τ.ρ y⁻¹ v = γ • v)
    (hτ : IsCusp τ.character) (hm : 0 < m) (l : Module.Dual ℂ τ) (hl : IsFunctional ψ₀ τ.ρ l) {j : ℕ} (v : τ)
    (hA : ∀ h, IsColFix j h → τ.ρ h v = v) (N : SIdx m → ZMod g) (b : JIdx m j → ZMod g) :
    (ψ₀ (-superDiag (umGL N)) : ℂ) * l (sv ψ₀ τ (Um N * Hm (bcol b)) v) =
      if b (j0 m j) = 0 then 0 else γ * l v := by
  split_ifs with hb
  · rw [← umGL_val, sv_singular ψ₀ τ hτ hm _ _ (by rw [bcol_zero]; exact hb), map_zero, mul_zero]
  · have hb' : bcol b 0 ≠ 0 := by rwa [bcol_zero]
    have hx : Um N * Hm (bcol b) = ((umGL N * hmGL (bcol b) hb' : Gn g (m + 1)) : Mt g (m + 1)) := by
      rw [Units.val_mul, umGL_val, hmGL_val]
    rw [hx, sv_unit ψ₀ τ hγ, map_smul, map_mul, Module.End.mul_apply, hl _ (umGL_mem N),
      hA _ (isColFix_hm b hb'), smul_eq_mul]
    have h1 := psi_neg_mul ψ₀ (superDiag (umGL N))
    linear_combination (γ * l v) * h1

theorem trace_hm_mul (c : Fin (m + 1) → ZMod g) (M : Mt g (m + 1)) :
    trace (Hm c * M) = ∑ i, c i * M 0 i + (trace M - M 0 0) := by
  have hH : (Hm c : Mt g (m + 1)) =
      1 + Matrix.of (fun i l => if l = 0 then c i - (1 : Mt g (m + 1)) i 0 else 0) := by
    ext i l
    by_cases hl : l = 0
    · subst hl; simp [Hm]
    · simp [Hm, hl]
  have h2 : trace ((Matrix.of (fun i l => if l = 0 then c i - (1 : Mt g (m + 1)) i 0 else 0)) * M) =
      ∑ i, c i * M 0 i - M 0 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_eq_single (0 : Fin (m + 1))
      (fun l _ hl => by simp [hl]) (by simp))]
    simp [sub_mul, Finset.sum_sub_distrib, Matrix.one_apply]
  rw [hH, Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, h2]
  ring

theorem um_mul_apply_row (y : Mt g (m + 1)) (N : SIdx m → ZMod g) (i : Fin (m + 1))
    (h : ∀ l, l < i → y 0 l = 0) : (y * Um N) 0 i = y 0 i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [Um]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hlt | hgt
    · rw [h l hlt, zero_mul]
    · rw [um_upper N hgt, mul_zero]
  · simp

theorem row_cond (y : Mt g (m + 1)) (N : SIdx m → ZMod g) (j : ℕ) :
    (∀ i : JIdx m j, (y * Um N) 0 i.1 = 0) ↔ ∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0 := by
  constructor
  · intro h
    suffices H : ∀ k : ℕ, ∀ i : Fin (m + 1), (i : ℕ) = k → (i : ℕ) ≤ j → y 0 i = 0 from
      fun i hi => H _ i rfl hi
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hik hij
      have hl : ∀ l, l < i → y 0 l = 0 := fun l hl => by
        have hl' : (l : ℕ) < i := hl
        exact ih l.val (by omega) l rfl (by omega)
      rw [← um_mul_apply_row y N i hl]
      exact h ⟨i, hij⟩
  · intro h i
    have hl : ∀ l, l < i.1 → y 0 l = 0 := fun l hl => by
      have hl' : (l : ℕ) < i.1 := hl
      have := i.2
      exact h l (by omega)
    rw [um_mul_apply_row y N i.1 hl]
    exact h i.1 i.2

theorem sum_dite_zero {α β : Type} [Fintype α] [AddCommMonoid β] (p : α → Prop) [DecidablePred p]
    (f : (a : α) → p a → β) : ∑ a, (if h : p a then f a h else 0) = ∑ a : {a // p a}, f a.1 a.2 := by
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun a => if h : p a then f a h else 0)]
  have h1 : ∀ a : {a // p a}, (if h : p a.1 then f a.1 h else 0) = f a.1 a.2 := fun a => dif_pos a.2
  have h2 : ∀ a : {a // ¬ p a}, (if h : p a.1 then f a.1 h else 0) = 0 := fun a => dif_neg a.2
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

theorem sumS {β : Type} [AddCommMonoid β] (F : SIdx m → β) :
    ∑ i : Fin (m + 1), ∑ k : Fin (m + 1), (if h : i < k then F ⟨(i, k), h⟩ else 0) = ∑ p : SIdx m, F p := by
  rw [← Fintype.sum_prod_type' (fun i k => if h : i < k then F ⟨(i, k), h⟩ else 0)]
  rw [sum_dite_zero (fun x : Fin (m + 1) × Fin (m + 1) => x.1 < x.2)]

theorem trace_um (y : Mt g (m + 1)) (N : SIdx m → ZMod g) :
    trace (y * Um N) = trace y + ∑ p : SIdx m, N p * y p.1.2 p.1.1 := by
  have hU : (Um N : Mt g (m + 1)) = 1 + Matrix.of (fun l i => if h : l < i then N ⟨(l, i), h⟩ else 0) := by
    ext l i
    by_cases e : l = i
    · subst e; simp [Um]
    · simp [Um, e, Matrix.one_apply_ne e]
  rw [hU, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_comm, ← sumS]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun i _ => ?_))
  split_ifs <;> simp [mul_comm]

theorem sd_um (N : SIdx m → ZMod g) :
    superDiag (umGL N) = ∑ p : SIdx m, (if (p.1.2 : ℕ) = p.1.1 + 1 then N p else 0) := by
  simp only [superDiag, umGL_val]
  simp_rw [Finset.sum_filter]
  rw [← sumS]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  by_cases h : i < k
  · rw [dif_pos h]
    by_cases e : (k : ℕ) = i + 1
    · simp [e, Um, ne_of_lt h, h]
    · simp [e]
  · rw [dif_neg h]
    have : ¬ (k : ℕ) = i + 1 := fun e => h (by rw [Fin.lt_iff_val_lt_val]; omega)
    simp [this]

def IsY (j : ℕ) (y : Mt g (m + 1)) : Prop :=
  (∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0) ∧
    ∀ i k : Fin (m + 1), i < k → y k i = if (k : ℕ) = i + 1 then 1 else 0

theorem kern_inner (hψ : ψ₀ ≠ 1) (j : ℕ) (y : Mt g (m + 1)) (N : SIdx m → ZMod g) :
    ∑ b : JIdx m j → ZMod g, (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * y)) : ℂ) =
      (if ∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0 then (g : ℂ) ^ Fintype.card (JIdx m j) else 0) *
        ((ψ₀ (trace y - y 0 0) : ℂ) * (ψ₀ (-superDiag (umGL N) + ∑ p : SIdx m, N p * y p.1.2 p.1.1) : ℂ)) := by
  have step1 : ∀ b, trace (Um N * Hm (bcol b) * y) =
      (∑ i : JIdx m j, b i * (y * Um N) 0 i.1) + ((trace y - y 0 0) + ∑ p : SIdx m, N p * y p.1.2 p.1.1) := by
    intro b
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, trace_hm_mul, trace_um,
      um_mul_apply_row y N 0 (fun l hl => absurd hl (Fin.not_lt_zero l))]
    have hsum : ∑ i, bcol b i * (y * Um N) 0 i = ∑ i : JIdx m j, b i * (y * Um N) 0 i.1 := by
      simp only [bcol, dite_mul, zero_mul]
      rw [sum_dite_zero (fun i : Fin (m + 1) => (i : ℕ) ≤ j)]
    rw [hsum]
    ring
  have hb : ∀ b : JIdx m j → ZMod g,
      (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * y)) : ℂ) =
      (ψ₀ (∑ i : JIdx m j, b i * (y * Um N) 0 i.1) : ℂ) *
      ((ψ₀ (trace y - y 0 0) : ℂ) * (ψ₀ (-superDiag (umGL N) + ∑ p : SIdx m, N p * y p.1.2 p.1.1) : ℂ)) := by
    intro b
    rw [step1]
    simp only [psi_add]
    ring
  rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.sum_mul, sum_pi_psi ψ₀ hψ]
  congr 1
  have : ((fun i : JIdx m j => (y * Um N) 0 i.1) = 0) ↔ ∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0 := by
    rw [← row_cond y N j, funext_iff]
    rfl
  by_cases h : ∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun e => h (this.1 e)), if_neg h]

theorem kern_exp (y : Mt g (m + 1)) (N : SIdx m → ZMod g) :
    -superDiag (umGL N) + ∑ p : SIdx m, N p * y p.1.2 p.1.1 =
      ∑ p : SIdx m, N p * (y p.1.2 p.1.1 - if (p.1.2 : ℕ) = p.1.1 + 1 then 1 else 0) := by
  rw [sd_um, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> ring

theorem kern_hc (y : Mt g (m + 1)) :
    ((fun p : SIdx m => y p.1.2 p.1.1 - if (p.1.2 : ℕ) = p.1.1 + 1 then (1 : ZMod g) else 0) = 0) ↔
      ∀ i k : Fin (m + 1), i < k → y k i = if (k : ℕ) = i + 1 then 1 else 0 := by
  rw [funext_iff]
  constructor
  · intro h i k hik
    exact sub_eq_zero.1 (h ⟨(i, k), hik⟩)
  · intro h p
    exact sub_eq_zero.2 (h p.1.1 p.1.2 p.2)

theorem kern (hψ : ψ₀ ≠ 1) (j : ℕ) (y : Mt g (m + 1)) :
    ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
        (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * y)) : ℂ) =
      if IsY j y then (g : ℂ) ^ Fintype.card (JIdx m j) * (g : ℂ) ^ Fintype.card (SIdx m) *
        (ψ₀ (trace y - y 0 0) : ℂ) else 0 := by
  rw [Finset.sum_congr rfl (fun N _ => kern_inner ψ₀ hψ j y N), ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun N _ => by rw [kern_exp y N]), ← Finset.mul_sum, sum_pi_psi ψ₀ hψ]
  by_cases hR : ∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0
  · by_cases hc : (fun p : SIdx m => y p.1.2 p.1.1 - if (p.1.2 : ℕ) = p.1.1 + 1 then (1 : ZMod g) else 0) = 0
    · rw [if_pos hR, if_pos hc, if_pos (show IsY j y from ⟨hR, (kern_hc y).1 hc⟩)]
      ring
    · rw [if_neg hc, if_neg (show ¬ IsY j y from fun h => hc ((kern_hc y).2 h.2))]
      ring
  · rw [if_neg hR, if_neg (show ¬ IsY j y from fun h => hR h.1)]
    ring

end DiscreteGroups.sglob.DzFe
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

theorem rot_symm_zero : (finRotate (m + 1)).symm 0 = Fin.last m := by
  rw [Equiv.symm_apply_eq, finRotate_last]

theorem rot_castSucc (l : Fin m) : finRotate (m + 1) (Fin.castSucc l) = Fin.succ l := by
  ext
  rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last l).ne]
  simp

theorem rot_symm_val (i : Fin (m + 1)) (hi : i ≠ 0) : (((finRotate (m + 1)).symm i : Fin (m + 1)) : ℕ) + 1 = i := by
  obtain ⟨k, rfl⟩ := (finRotate (m + 1)).surjective i
  rw [Equiv.symm_apply_apply]
  have hk : k ≠ Fin.last m := fun h => hi (by rw [h, finRotate_last])
  rw [coe_finRotate_of_ne_last hk]

theorem rot_symm_ne_last (i : Fin (m + 1)) (hi : i ≠ 0) : (finRotate (m + 1)).symm i ≠ Fin.last m := fun h =>
  hi ((finRotate (m + 1)).symm.injective (h.trans rot_symm_zero.symm))

theorem cyc_val : ((cyc g (m + 1) : Gn g (m + 1)) : Mt g (m + 1)) =
    Matrix.of fun i k => if i = finRotate (m + 1) k then 1 else 0 := rfl

theorem cyc_inv_val : (((cyc g (m + 1))⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) =
    Matrix.of fun i k => if finRotate (m + 1) i = k then 1 else 0 := rfl

theorem cyc_mul_apply (Z : Mt g (m + 1)) (i k : Fin (m + 1)) :
    ((cyc g (m + 1) : Gn g (m + 1)) * Z : Mt g (m + 1)) i k = Z ((finRotate (m + 1)).symm i) k := by
  rw [cyc_val, Matrix.mul_apply, Finset.sum_eq_single ((finRotate (m + 1)).symm i)]
  · simp
  · intro l _ hl
    rw [Matrix.of_apply, if_neg (fun h => hl (by rw [h, Equiv.symm_apply_apply])), zero_mul]
  · simp

theorem mul_cycinv_apply (Z : Mt g (m + 1)) (i k : Fin (m + 1)) :
    (Z * (((cyc g (m + 1))⁻¹ : Gn g (m + 1)) : Mt g (m + 1))) i k = Z i ((finRotate (m + 1)).symm k) := by
  rw [cyc_inv_val, Matrix.mul_apply, Finset.sum_eq_single ((finRotate (m + 1)).symm k)]
  · simp
  · intro l _ hl
    rw [Matrix.of_apply, if_neg (fun h => hl (by rw [← h, Equiv.symm_apply_apply])), mul_zero]
  · simp

theorem cycinv_mul_apply (Z : Mt g (m + 1)) (l k : Fin (m + 1)) :
    ((((cyc g (m + 1))⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) * Z) l k = Z (finRotate (m + 1) l) k := by
  rw [cyc_inv_val, Matrix.mul_apply, Finset.sum_eq_single (finRotate (m + 1) l)]
  · simp
  · intro a _ ha
    rw [Matrix.of_apply, if_neg (Ne.symm ha), zero_mul]
  · simp

def Hp (r : Fin (m + 1) → ZMod g) : Mt g (m + 1) :=
  Matrix.of fun i k => if i = Fin.last m then r k else (1 : Mt g (m + 1)) i k

theorem hp_lower (r : Fin (m + 1) → ZMod g) : (Hp r : Mt g (m + 1)).BlockTriangular OrderDual.toDual := by
  intro i k hik
  have h : i < k := hik
  have hi : i ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le h (Fin.le_last k))
  simp [Hp, hi, Matrix.one_apply_ne (ne_of_lt h)]

theorem det_hp (r : Fin (m + 1) → ZMod g) : (Hp r : Mt g (m + 1)).det = r (Fin.last m) := by
  rw [Matrix.det_of_lowerTriangular _ (hp_lower r), Fin.prod_univ_castSucc]
  simp [Hp, (Fin.castSucc_lt_last _).ne]

def hpGL (r : Fin (m + 1) → ZMod g) (hr : r (Fin.last m) ≠ 0) : Gn g (m + 1) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Hp r) (by rw [det_hp]; exact hr)

theorem hpGL_val (r : Fin (m + 1) → ZMod g) (hr : r (Fin.last m) ≠ 0) :
    ((hpGL r hr : Gn g (m + 1)) : Mt g (m + 1)) = Hp r := rfl

abbrev WIdx (m j : ℕ) := {k : Fin (m + 1) // j < (k : ℕ) ∧ (k : ℕ) < m}

def rvec (j : ℕ) (t : (ZMod g)ˣ) (w : WIdx m j → ZMod g) : Fin (m + 1) → ZMod g :=
  fun k => if k = Fin.last m then (t : ZMod g) else if h : j < (k : ℕ) ∧ (k : ℕ) < m then w ⟨k, h⟩ else 0

theorem rvec_last (j : ℕ) (t : (ZMod g)ˣ) (w : WIdx m j → ZMod g) : rvec j t w (Fin.last m) = t := by
  simp [rvec]

theorem rvec_low {j : ℕ} (hj : j < m) (t : (ZMod g)ˣ) (w : WIdx m j → ZMod g) (k : Fin (m + 1))
    (hk : (k : ℕ) ≤ j) : rvec j t w k = 0 := by
  have hk' : k ≠ Fin.last m := fun h => by
    rw [h, Fin.val_last] at hk
    omega
  simp [rvec, hk', not_lt.2 hk]

def phi (j : ℕ) (p : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) : Gn g (m + 1) :=
  cyc g (m + 1) * hpGL (rvec j p.2.1 p.2.2) (by rw [rvec_last]; exact p.2.1.ne_zero) * umGL p.1

theorem hp_um_row (r : Fin (m + 1) → ZMod g) (N : SIdx m → ZMod g) (i : Fin (m + 1)) (hi : i ≠ Fin.last m)
    (k : Fin (m + 1)) : (Hp r * Um N : Mt g (m + 1)) i k = Um N i k := by
  rw [Matrix.mul_apply]
  simp only [Hp, Matrix.of_apply, if_neg hi]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem hp_um_last_low {j : ℕ} (r : Fin (m + 1) → ZMod g) (N : SIdx m → ZMod g)
    (hr : ∀ l : Fin (m + 1), (l : ℕ) ≤ j → r l = 0) (k : Fin (m + 1)) (hk : (k : ℕ) ≤ j) :
    (Hp r * Um N : Mt g (m + 1)) (Fin.last m) k = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  have hH : Hp r (Fin.last m) l = r l := by simp [Hp]
  rw [hH]
  by_cases hl : (l : ℕ) ≤ j
  · rw [hr l hl, zero_mul]
  · rw [um_upper N (show k < l by rw [Fin.lt_def]; omega), mul_zero]

theorem phi_val (j : ℕ) (p : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) :
    ((phi j p : Gn g (m + 1)) : Mt g (m + 1)) =
      ((cyc g (m + 1) : Gn g (m + 1)) : Mt g (m + 1)) * (Hp (rvec j p.2.1 p.2.2) * Um p.1) := by
  simp only [phi, Units.val_mul, hpGL_val, umGL_val, Matrix.mul_assoc]

theorem isY_phi {j : ℕ} (hj : j < m) (p : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) :
    IsY j ((phi j p : Gn g (m + 1)) : Mt g (m + 1)) := by
  rw [phi_val]
  constructor
  · intro i hi
    rw [cyc_mul_apply, rot_symm_zero]
    exact hp_um_last_low _ _ (fun l hl => rvec_low hj _ _ l hl) i hi
  · intro i k hik
    have hk : k ≠ 0 := by
      intro h
      subst h
      exact Fin.not_lt_zero i hik
    rw [cyc_mul_apply, hp_um_row _ _ _ (rot_symm_ne_last k hk)]
    have hv := rot_symm_val k hk
    have hik' : (i : ℕ) < k := hik
    simp only [Um, Matrix.of_apply]
    by_cases e : (k : ℕ) = i + 1
    · have : (finRotate (m + 1)).symm k = i := Fin.ext (by omega)
      rw [if_pos this, if_pos e]
    · have h1 : (finRotate (m + 1)).symm k ≠ i := fun h => e (by rw [← hv, h])
      have h2 : ¬ (finRotate (m + 1)).symm k < i := fun h => by
        have : (((finRotate (m + 1)).symm k : Fin (m + 1)) : ℕ) < i := h
        omega
      rw [if_neg h1, dif_neg h2, if_neg e]

end DiscreteGroups.sglob.DzFe
end
end
