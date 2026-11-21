import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SubsingletonIdxZero

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom

variable {k r : ℕ}

def Setup (k r : ℕ) (c Ch : ℝ) (P : Mat k r) (lam : Fin (2 * r + k + 1) → ℝ) (bv h q : ℝ)
    (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) : Prop :=
  IsCayleyU k r (sgnCN k r) P ∧ IsShape k r lam bv ∧ IsRange k r lam c h q ∧
    Ch * (2 * r + 2 : ℝ) ^ (9 / 2 : ℝ) *
      (3 * (r + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ≤ h ∧
    ∀ μ, InPP lam q μ → (R μ).IsDSAt P μ

def Standing (k r : ℕ) (c Ch Cg C₀ : ℝ) (P : Mat k r) (lam : Fin (2 * r + k + 1) → ℝ) (bv h q : ℝ)
    (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) : Prop :=
  1 ≤ k ∧ 0 < c ∧ 915 ≤ Ch ∧ 1 ≤ Cg ∧ 10 ^ 4 ≤ C₀ ∧ 0 ≤ q ∧ Setup k r c Ch P lam bv h q R ∧
    (∀ i j, i < j → Cg * (2 * r + 2 : ℝ) ^ 3 ≤ lam i - lam j) ∧ C₀ * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ bv ∧
    ∀ μ, InPP lam (q + r + 2) μ → (R μ).IsDSAt P μ

structure Flag (k r : ℕ) where
  z : Fin (2 * r + k + 1) → ℂ
  u : Fin k → ℝ
  W : Type
  [nG : NormedAddCommGroup W]
  [iP : InnerProductSpace ℂ W]
  π : Mat k r → (W →L[ℂ] W)
  cψ : ℂ
  μG : Measure (Mt k r)
  μS : Measure (Mt k r)
  ν : Measure (Mt k r)

attribute [instance] Flag.nG Flag.iP

def Flag.Ok (F : Flag k r) (κ : ℝ) : Prop :=
  inWb k r F.z ∧ 0 < Tz k r F.z ∧ IsHCTypeW k r F.z F.u F.π ∧ 0 < κ ∧ ‖F.cψ‖ = 2 * κ ∧ IsMeasSG F.z F.μG F.μS F.ν

def Flag.Size (F : Flag k r) (lam : Fin (2 * r + k + 1) → ℝ) (bv b : ℝ) : Prop :=
  InterlaceS (by omega) F.u lam ∧ (∀ s, |lam s| ≤ b) ∧ (∀ i, |F.u i| ≤ b) ∧ bv ≤ b

def Flag.Iso (F : Flag k r) (A : HRep k r) (B : A.H → F.W) : Prop := A.IsIsoB F.z F.cψ F.π F.ν B

def el (I : Idx k r 1) : Fin (2 * r + k + 1) := I.1.orderEmbOfFin I.2 0

def nrm2 {H : Type} [NormedAddCommGroup H] {l : ℕ} (x : Idx k r l → H) : ℝ := ∑ I, ‖x I‖ ^ 2

def HRep.EE (A : HRep k r) (P : Mat k r) (x : Idx k r 1 → A.H) : Idx k r 1 → A.H :=
  fun b => -∑ c, A.E P (el b) (el c) (x c)

def HRep.EEd (A : HRep k r) (P : Mat k r) (x : Idx k r 1 → A.H) : Idx k r 1 → A.H :=
  fun b => -A.E P (el b) (el b) (x b)

def HRep.EEo (A : HRep k r) (P : Mat k r) (x : Idx k r 1 → A.H) : Idx k r 1 → A.H :=
  fun b => -∑ c ∈ univ.erase b, A.E P (el b) (el c) (x c)


def xS (μ : Fin (2 * r + k + 1) → ℝ) (s : Idx k r 1) : ℝ := -μ (el s) + (1 - ((2 * r + k + 1 : ℕ) : ℝ)) / 2

def VV (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) (P : Mat k r) (μ : Fin (2 * r + k + 1) → ℝ)
    (p : ∀ I : Idx k r 1, (Idx k r 1 → (R μ).H) → (R (μ + wtI true I)).H) (j : ℕ) : Set (Idx k r 1 → (R μ).H) :=
  {x | (R μ).SmT x ∧ ∀ s, p s x ∈ (R (μ + wtI true s)).filt P μ (j + 1)}

section Proj

variable (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) (μ : Fin (2 * r + k + 1) → ℝ)
  (ι : ∀ I : Idx k r 1, (R (μ + wtI true I)).H → Idx k r 1 → (R μ).H)
  (p : ∀ I : Idx k r 1, (Idx k r 1 → (R μ).H) → (R (μ + wtI true I)).H)

def prS (s : Idx k r 1) (x : Idx k r 1 → (R μ).H) : Idx k r 1 → (R μ).H := ι s (p s x)

def prCloud (x : Idx k r 1 → (R μ).H) : Idx k r 1 → (R μ).H :=
  ∑ s ∈ univ.filter (fun s : Idx k r 1 => (el s).val < k - 1), prS R μ ι p s x

def prNode (x : Idx k r 1 → (R μ).H) : Idx k r 1 → (R μ).H :=
  ∑ s ∈ univ.filter (fun s : Idx k r 1 => ¬ (el s).val < k - 1), prS R μ ι p s x

variable {R μ ι p}


end Proj

def HypJ (k r : ℕ) (bv : ℝ) (j : ℕ) : Prop :=
  ((j : ℝ) + 2) * (8704 * ((2 * r + k + 1 : ℕ) : ℝ)) ≤ bv ∧ 8704 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ bv

def bStar {n : ℕ} (μ : Fin n → ℝ) : ℝ := ‖μ‖ + n

def offBound {n : ℕ} (μ : Fin n → ℝ) (j : ℕ) : ℝ := 8 * (bStar μ + j) * ((n : ℝ) ^ 2 + j)

def QQ (r : ℕ) (bv : ℝ) : ℝ := 4 + 9 * (2 * r + 2 : ℝ) * (6 * bv) ^ (2 * (2 * r + 2) - 2)

def HRep.expect (A : HRep k r) {W : Type} [NormedAddCommGroup W] (ν : Measure (Mt k r)) (B : A.H → W)
    (φ : Mat k r → ℝ) (w : A.H) : ℝ≥0∞ := A.mass ν B φ w / ‖w‖ₑ ^ 2



def MomFirst (A : HRep k r) (F : Flag k r) (B : A.H → F.W) (H : ℝ) (q : ℕ) (w : A.H) : Prop :=
  A.mass F.ν B (fun g => lA k r F.z g 0 ^ (2 * q)) w ≤ ENNReal.ofReal (H ^ (2 * q)) * ‖w‖ₑ ^ 2

def MomRatio (A : HRep k r) (F : Flag k r) (B : A.H → F.W) (μ : Fin (2 * r + k + 1) → ℝ) (κ : ℝ) (j q : ℕ)
    (w : A.H) : Prop :=
  ∀ a : Fin r, A.mass F.ν B (fun g => (lA k r F.z g a.succ / lA k r F.z g a.castSucc) ^ (2 * q)) w ≤
    ENNReal.ofReal ((3 * ((2 * r + k + 1 : ℕ) : ℝ) * (bStar μ + j + 2 * q) / κ) ^ (2 * q)) * ‖w‖ₑ ^ 2

def MomAll (A : HRep k r) (F : Flag k r) (B : A.H → F.W) (H : ℝ) (q : ℕ) (w : A.H) : Prop :=
  (∀ a, A.mass F.ν B (fun g => lA k r F.z g a ^ (2 * q)) w ≤ ENNReal.ofReal (H ^ (2 * q)) * ‖w‖ₑ ^ 2 ∧
    A.mass F.ν B (fun g => (lA k r F.z g a)⁻¹ ^ (2 * q)) w ≤ ENNReal.ofReal (H ^ (2 * q)) * ‖w‖ₑ ^ 2) ∧
  ∀ t : ℝ, 0 < t → A.mass F.ν B (Set.indicator {g | ∃ a, t * H ≤ max (lA k r F.z g a) (lA k r F.z g a)⁻¹} 1) w ≤
    ENNReal.ofReal ((2 * r + 2 : ℝ) * (t ^ (2 * q))⁻¹) * ‖w‖ₑ ^ 2

def MomProd (A : HRep k r) (F : Flag k r) (B : A.H → F.W) (H : ℝ) {l : ℕ} (hl : l ≤ r + 1) (q : ℕ) (w : A.H) : Prop :=
  A.mass F.ν B (fun g => (∏ a : Fin l, lA k r F.z g (Fin.castLE hl a)) ^ (2 * q)) w ≤
    ENNReal.ofReal (H ^ (2 * q * l)) * ‖w‖ₑ ^ 2

theorem InPP.mono {n : ℕ} {lam μ : Fin n → ℝ} {s t : ℝ} (h : InPP lam s μ) (hst : s ≤ t) : InPP lam t μ :=
  ⟨h.1, h.2.trans hst⟩


theorem InPP.abs_le {n : ℕ} {lam μ : Fin n → ℝ} {t : ℝ} (h : InPP lam t μ) (a : Fin n) : |μ a - lam a| ≤ t :=
  (single_le_sum (f := fun a => |μ a - lam a|) (fun _ _ => abs_nonneg _) (mem_univ a)).trans h.2

theorem InPP.gap {n : ℕ} {lam μ : Fin n → ℝ} {t : ℝ} (h : InPP lam t μ) {a b : Fin n} (hab : a ≠ b) :
    lam a - lam b - t ≤ μ a - μ b := by
  have h1 := abs_add_abs_le_dist1 μ lam hab
  linarith [h.2, neg_abs_le (μ a - lam a), le_abs_self (μ b - lam b)]



section Conseq

variable {c Ch Cg C₀ bv h q : ℝ} {P : Mat k r} {lam μ : Fin (2 * r + k + 1) → ℝ}
  {R : (Fin (2 * r + k + 1) → ℝ) → HRep k r}



theorem IsRange.radius_le (hr : IsRange k r lam c h q) (hq : 0 ≤ q) : 100 * q ≤ h := by
  obtain ⟨hc, -, h0, -⟩ := hr
  have h1 : (1 : ℝ) ≤ Real.sqrt (2 * r + 2) := Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) r])
  have h2 : c * (100 * q) ≤ 100 * max 1 c * q := by nlinarith [le_max_right 1 c]
  have h3 : 0 ≤ 100 * max 1 c * q := le_trans (by positivity) h2
  refine le_of_mul_le_mul_left ?_ hc
  nlinarith

theorem IsRange.mono {q' : ℝ} (hr : IsRange k r lam c h q') (hq : q ≤ q') : IsRange k r lam c h q := by
  have h0 : 100 * max 1 c * q ≤ 100 * max 1 c * q' :=
    mul_le_mul_of_nonneg_left hq (by linarith [le_max_left 1 c])
  exact ⟨hr.1, hr.2.1, (mul_le_mul_of_nonneg_right h0 (Real.sqrt_nonneg _)).trans hr.2.2.1,
    fun i j hij hj => h0.trans (hr.2.2.2 i j hij hj)⟩

theorem Setup.mono {q' : ℝ} (hS : Setup k r c Ch P lam bv h q' R) (hq : q ≤ q') : Setup k r c Ch P lam bv h q R :=
  ⟨hS.1, hS.2.1, hS.2.2.1.mono hq, hS.2.2.2.1, fun μ hμ => hS.2.2.2.2 μ (hμ.mono hq)⟩

theorem Setup.standing {q' : ℝ} (hS : Setup k r c Ch P lam bv h q' R) (hk : 1 ≤ k) (hCh : 915 ≤ Ch)
    (hCg : 1 ≤ Cg) (hC₀ : 10 ^ 4 ≤ C₀) (hq : 0 ≤ q) (h1 : q + r + 2 ≤ q') (h2 : Cg * (2 * r + 2 : ℝ) ^ 3 ≤ 100 * q')
    (h3 : C₀ * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ bv) : Standing k r c Ch Cg C₀ P lam bv h q R := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  exact ⟨hk, hS.2.2.1.1, hCh, hCg, hC₀, hq, hS.mono (by linarith),
    fun i j hij => h2.trans (hS.2.2.1.le_gap hS.2.1 hij), h3,
    fun μ hμ => hS.2.2.2.2 μ (hμ.mono h1)⟩

namespace Standing

theorem setup (H : Standing k r c Ch Cg C₀ P lam bv h q R) : Setup k r c Ch P lam bv h q R := H.2.2.2.2.2.2.1

theorem mono {q' : ℝ} (H : Standing k r c Ch Cg C₀ P lam bv h q' R) (h0 : 0 ≤ q) (hq : q ≤ q') :
    Standing k r c Ch Cg C₀ P lam bv h q R := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7, a8, a9, a10⟩ := H
  exact ⟨a1, a2, a3, a4, a5, h0, a7.mono hq, a8, a9, fun μ hμ => a10 μ (hμ.mono (by linarith))⟩


theorem radius_le_gap (H : Standing k r c Ch Cg C₀ P lam bv h q R) {i j : Fin (2 * r + k + 1)} (hij : i < j) :
    100 * q ≤ lam i - lam j :=
  H.setup.2.2.1.le_gap H.setup.2.1 hij



theorem gap_ge (H : Standing k r c Ch Cg C₀ P lam bv h q R) (hμ : InPP lam q μ) {i j : Fin (2 * r + k + 1)}
    (hij : i < j) : 0.98 * (lam i - lam j) ≤ μ i - μ j := by
  linarith [hμ.gap hij.ne, H.radius_le_gap hij, H.2.2.2.2.2.1]





theorem entries (H : Standing k r c Ch Cg C₀ P lam bv h q R) (hμ : InPP lam q μ) (i : Fin (2 * r + k + 1)) :
    (i.val < k - 1 → -q ≤ μ i ∧ μ i ≤ bv / 8 + q) ∧ (k - 1 ≤ i.val → -(2 * bv) - q ≤ μ i ∧ μ i ≤ -bv + q) := by
  have h1 := abs_le.1 (hμ.abs_le i)
  constructor
  · intro hi; have := H.setup.2.1.2.1 i hi; constructor <;> linarith
  · intro hi; have := H.setup.2.1.2.2 i hi; constructor <;> linarith


end Standing

theorem HypJ.QQ_le {j : ℕ} (hJ : HypJ k r bv j) : QQ r bv ≤ (6 * bv) ^ (2 * (2 * r + 2)) := by
  have h0 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := le_self_pow₀ h0 (by norm_num)
  have h3 : (2 * r + 1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h4 := hJ.2
  have h5 : (1 : ℝ) ≤ (6 * bv) ^ (2 * (2 * r + 2) - 2) := one_le_pow₀ (by linarith)
  have h6 : 4 + 9 * (2 * r + 2 : ℝ) ≤ (6 * bv) ^ 2 := by nlinarith
  rw [QQ, show 2 * (2 * r + 2) = 2 + (2 * (2 * r + 2) - 2) by omega, pow_add, Nat.add_sub_cancel_left]
  nlinarith

end Conseq

example : bStar ![(1 : ℝ), -3] = 5 := by
  have : ‖![(1 : ℝ), -3]‖ = 3 := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => by fin_cases i <;> simp) ?_
    simpa using norm_le_pi_norm ![(1 : ℝ), -3] 1
  rw [bStar, this]; norm_num

example : QQ 0 1 = 652 := by norm_num [QQ]

example : HypJ 1 0 (10 ^ 5) 3 ∧ ¬ HypJ 1 0 (10 ^ 5) 4 := by norm_num [HypJ]

example (μ : Fin (2 * 0 + 1 + 1) → ℝ) (s : Idx 1 0 1) : xS μ s = -μ (el s) - 1 / 2 := by
  unfold xS; norm_num; ring

end GlobalTheory.Mom
