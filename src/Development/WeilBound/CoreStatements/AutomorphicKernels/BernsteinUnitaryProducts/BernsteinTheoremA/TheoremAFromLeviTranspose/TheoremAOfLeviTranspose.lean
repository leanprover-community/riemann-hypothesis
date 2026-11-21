import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeInvariantOfConjInvariantDistributionGL

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.GelfandKazhdan

namespace PositivityTheory.PfBern.ThmA

section Gen

variable (k : Type) [Field k]

theorem trGL_one (n : ℕ) : trGL (1 : GL (Fin (n + 1)) k) = 1 :=
  Units.ext (by show ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ = 1; simp)

theorem trGL_inv {n : ℕ} (g : GL (Fin (n + 1)) k) : trGL g⁻¹ = (trGL g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← trGL_mul, mul_inv_cancel, trGL_one]

def MirT (n : ℕ) : Subgroup (GL (Fin (n + 1)) k) where
  carrier := {g | trGL g ∈ Mir k n}
  mul_mem' {a b} ha hb := by
    show trGL (a * b) ∈ Mir k n
    rw [trGL_mul]
    exact mul_mem hb ha
  one_mem' := by
    show trGL 1 ∈ Mir k n
    rw [trGL_one]
    exact one_mem _
  inv_mem' {a} ha := by
    show trGL a⁻¹ ∈ Mir k n
    rw [trGL_inv]
    exact inv_mem ha

variable {k}

def colVec {n : ℕ} (c : Fin n → k) : Fin (n + 1) → k := fun i => Fin.lastCases 0 c i

theorem unip_val {n : ℕ} (w : Multiplicative (Fin n → k)) :
    ((unip k n w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 + colMat k n w.toAdd := rfl

theorem vecMul_colMat {n : ℕ} (r : Fin (n + 1) → k) (w : Fin n → k) :
    vecMul r (colMat k n w) = Pi.single (Fin.last n) (∑ i : Fin n, r (Fin.castSucc i) * w i) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [vecMul, dotProduct, colMat, Fin.sum_univ_castSucc]
  | cast j => simp [vecMul, dotProduct, colMat, Fin.castSucc_ne_last, Pi.single_apply]

theorem colMat_mulVec {n : ℕ} (c : Fin n → k) (r : Fin (n + 1) → k) :
    colMat k n c *ᵥ r = r (Fin.last n) • colVec c := by
  funext i
  simp only [mulVec, dotProduct, colMat, Pi.smul_apply, smul_eq_mul, colVec]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp [mul_comm]
  · intro j _ hj
    simp [hj]
  · simp

theorem vecMul_unip {n : ℕ} (r : Fin (n + 1) → k) (w : Multiplicative (Fin n → k)) :
    vecMul r ((unip k n w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      r + Pi.single (Fin.last n) (∑ i : Fin n, r (Fin.castSucc i) * w.toAdd i) := by
  rw [unip_val, vecMul_add, vecMul_one, vecMul_colMat]

theorem vecMul_trGL_unip {n : ℕ} (r : Fin (n + 1) → k) (c : Multiplicative (Fin n → k)) :
    vecMul r ((trGL (unip k n c) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      r + r (Fin.last n) • colVec c.toAdd := by
  show vecMul r ((unip k n c : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ = _
  rw [vecMul_transpose, unip_val, add_mulVec, one_mulVec, colMat_mulVec]


theorem exists_row {n : ℕ} (hn : 0 < n) (H : Subgroup (GL (Fin (n + 1)) k)) (hP : Mir k n ≤ H) (hPT : MirT k n ≤ H)
    (r : Fin (n + 1) → k) (hr : r ≠ 0) :
    ∃ h ∈ H, vecMul (eLast k n) ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = r := by
  have hu : ∀ w, unip k n w ∈ H := fun w => hP (MirU_le_Mir k n ⟨w, rfl⟩)
  have ht : ∀ c, trGL (unip k n c) ∈ H := fun c => hPT (by
    show trGL (trGL (unip k n c)) ∈ Mir k n
    rw [trGL_trGL]
    exact MirU_le_Mir k n ⟨c, rfl⟩)
  set r' : Fin n → k := fun i => r (Fin.castSucc i) with hr'
  set t : k := r (Fin.last n) with ht'
  by_cases h0 : r' = 0
  ·
    have htne : t ≠ 0 := by
      intro htz
      apply hr
      funext j
      induction j using Fin.lastCases with
      | last => exact htz
      | cast j => exact congrFun h0 j
    let i0 : Fin n := ⟨0, hn⟩
    refine ⟨trGL (unip k n (Multiplicative.ofAdd (Pi.single i0 1))) *
      unip k n (Multiplicative.ofAdd (Pi.single i0 (t - 1))) *
      trGL (unip k n (Multiplicative.ofAdd (Pi.single i0 (-t⁻¹)))),
      mul_mem (mul_mem (ht _) (hu _)) (ht _), ?_⟩
    rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, vecMul_trGL_unip, vecMul_unip,
      vecMul_trGL_unip]
    funext j
    induction j using Fin.lastCases with
    | last =>
      simp [eLast, colVec, Pi.single_apply, Finset.sum_ite_eq', Fin.castSucc_ne_last] <;> rfl
    | cast j =>
      have hj : r (Fin.castSucc j) = 0 := congrFun h0 j
      simp [eLast, colVec, Fin.castSucc_ne_last, Pi.single_apply, hj, Finset.sum_ite_eq', htne]
      split_ifs <;> simp [htne]
  · obtain ⟨i, hi⟩ : ∃ i, r' i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h0 (funext hc)
    refine ⟨trGL (unip k n (Multiplicative.ofAdd r')) *
      unip k n (Multiplicative.ofAdd (Pi.single i ((t - 1) / r' i))), mul_mem (ht _) (hu _), ?_⟩
    rw [Units.val_mul, ← vecMul_vecMul, vecMul_trGL_unip, vecMul_unip]
    funext j
    induction j using Fin.lastCases with
    | last =>
      simp [eLast, colVec, Pi.single_apply, Fin.castSucc_ne_last, Finset.sum_ite_eq', hi]
      field_simp
      ring
    | cast j =>
      simp [eLast, colVec, Pi.single_apply, Fin.castSucc_ne_last, hr']


end Gen

section Dist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ConjInv {m : ℕ} (T : SB (GL (Fin m) k) →ₗ[ℂ] ℂ) (g : GL (Fin m) k) : Prop :=
  ∀ φ ψ : SB (GL (Fin m) k), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ

def TrInv {m : ℕ} (T : SB (GL (Fin m) k) →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ψ : SB (GL (Fin m) k), (∀ x y : GL (Fin m) k, y.val = x.val.transpose → ψ.1 x = φ.1 y) → T ψ = T φ

def conjHomeo {m : ℕ} (g : GL (Fin m) k) : GL (Fin m) k ≃ₜ GL (Fin m) k :=
  (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)

theorem conjHomeo_apply {m : ℕ} (g x : GL (Fin m) k) : conjHomeo g x = g * x * g⁻¹ := rfl

theorem conjInv_iff {m : ℕ} (T : SB (GL (Fin m) k) →ₗ[ℂ] ℂ) (g : GL (Fin m) k) :
    ConjInv T g ↔ ∀ φ, T (pull (conjHomeo g) φ) = T φ := by
  constructor
  · intro h φ
    exact h φ _ fun x => rfl
  · intro h φ ψ hψ
    have e : ψ = pull (conjHomeo g) φ := Subtype.ext (funext fun x => hψ x)
    rw [e]
    exact h φ

def conjInvSubgroup {m : ℕ} (T : SB (GL (Fin m) k) →ₗ[ℂ] ℂ) : Subgroup (GL (Fin m) k) where
  carrier := {g | ConjInv T g}
  one_mem' := by
    show ConjInv T 1
    rw [conjInv_iff]
    intro φ
    congr 1
    exact Subtype.ext (funext fun x => by simp [pull, conjHomeo_apply])
  mul_mem' {a b} ha hb := by
    show ConjInv T (a * b)
    have ha' := (conjInv_iff T a).1 ha
    have hb' := (conjInv_iff T b).1 hb
    rw [conjInv_iff]
    intro φ
    have e : pull (conjHomeo (a * b)) φ = pull (conjHomeo b) (pull (conjHomeo a) φ) :=
      Subtype.ext (funext fun x => by simp [pull, conjHomeo_apply, mul_assoc])
    rw [e, hb', ha']
  inv_mem' {a} ha := by
    show ConjInv T a⁻¹
    have ha' := (conjInv_iff T a).1 ha
    rw [conjInv_iff]
    intro φ
    have e : pull (conjHomeo a) (pull (conjHomeo a⁻¹) φ) = φ :=
      Subtype.ext (funext fun x => by simp [pull, conjHomeo_apply, mul_assoc])
    have := ha' (pull (conjHomeo a⁻¹) φ)
    rw [e] at this
    exact this.symm


def TheoremA (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ) (T : SB (GL (Fin (n + 1)) k) →ₗ[ℂ] ℂ), (∀ g ∈ Mir k n, ConjInv T g) → ∀ g, ConjInv T g

def MirTransposeInv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ T : SB (GL (Fin (n + 1)) k) →ₗ[ℂ] ℂ, (∀ g ∈ Mir k n, ConjInv T g) → TrInv T

def LeviTransposeInv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ T : SB (GL (Fin (n + 1)) k) →ₗ[ℂ] ℂ, (∀ g : GL (Fin n) k, ConjInv T (glEmb k n g)) → TrInv T




end Dist

end PositivityTheory.PfBern.ThmA

end
