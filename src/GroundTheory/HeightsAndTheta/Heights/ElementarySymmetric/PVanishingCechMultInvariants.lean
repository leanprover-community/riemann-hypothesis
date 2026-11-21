import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauIIsBasisOf
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.TorsionAverage

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

def VanishingCechMultInvariants.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a : ℕ), 3 ≤ a → ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ m : ℕ, 1 ≤ m → ∀ n q : ℕ,
      (∀ φ : Finset (Fin (r + 1)) → P.Fn,
        P.IsCocycle (a * m ^ 2) (n * m ^ 2) (q + 1) (fun j z => x j ((m : ℂ) • z)) φ →
        P.IsCoboundary (a * m ^ 2) (n * m ^ 2) q (fun j z => x j ((m : ℂ) • z)) φ) →
      ∀ φ : Finset (Fin (r + 1)) → P.Fn, P.IsCocycle a n (q + 1) x φ → P.IsCoboundary a n q x φ

end

end GroundTheory.Heights₂.Heights.KeyFormula
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

namespace RigSymForm

variable {K : Type} [Field K] [Algebra K ℂ] (P : RigSymForm K)

theorem thetaSec_add_latVec {N : ℕ} {f : P.Fn} (hf : f ∈ thetaSec P.pt P.ch N)
    (u v : Fin P.g → ℤ) (w : Fin P.g → ℂ) : f (w + P.latVec u v) = P.autL N u v w * f w := by
  obtain ⟨-, h1, h2⟩ := hf
  have : w + P.latVec u v = (w + P.pt.τ *ᵥ intVec u) + intVec v := by
    simp only [latVec]; abel
  rw [this, h1, h2, autL]; ring

theorem autL_ne_zero (N : ℕ) (u v : Fin P.g → ℤ) (w : Fin P.g → ℂ) : P.autL N u v w ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

theorem autL_add (N₁ N₂ : ℕ) (u v : Fin P.g → ℤ) (w : Fin P.g → ℂ) :
    P.autL (N₁ + N₂) u v w = P.autL N₁ u v w * P.autL N₂ u v w := by
  simp only [autL, ← perFactor_add, ← autFactor_add]; ring

theorem autL_mul (d k : ℕ) (u v : Fin P.g → ℤ) (w : Fin P.g → ℂ) :
    P.autL (d * k) u v w = P.autL d u v w ^ k := by
  induction k with
  | zero =>
    simp [autL, perFactor, autFactor]
  | succ k ih => rw [Nat.mul_succ, autL_add, ih, pow_succ]

theorem torsAvg_congr {N m : ℕ} {F₁ F₂ : P.Fn} {z : Fin P.g → ℂ}
    (h : ∀ u v : Fin P.g → Fin m, F₁ (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
      F₂ (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v))) :
    P.torsAvg N m F₁ z = P.torsAvg N m F₂ z := by
  simp only [torsAvg, h]

theorem torsAvg_cechD {N m r : ℕ} (ψ : Finset (Fin (r + 1)) → P.Fn) (J : Finset (Fin (r + 1)))
    (z : Fin P.g → ℂ) :
    cechD (fun I => P.torsAvg N m (ψ I)) J z = P.torsAvg N m (cechD ψ J) z := by
  simp only [cechD, torsAvg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun j _ => by ring

theorem torsAvg_div {n d k m : ℕ} {F G Y : P.Fn} {z : Fin P.g → ℂ}
    (hY : ∀ u v : Fin P.g → Fin m, Y (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
      P.autL d (torsIdx u) (torsIdx v) ((m : ℂ) • z) * Y z) (hY0 : Y z ≠ 0)
    (hG : ∀ u v : Fin P.g → Fin m, G (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
      F (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) /
        Y (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) ^ k) :
    P.torsAvg n m G z = P.torsAvg (n + d * k) m F z / Y z ^ k := by
  simp only [torsAvg, hG, hY, mul_div_assoc, Finset.sum_div]
  refine congrArg _ (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_)
  rw [autL_add, autL_mul]
  have h1 := P.autL_ne_zero n (torsIdx u) (torsIdx v) ((m : ℂ) • z)
  have h2 := P.autL_ne_zero d (torsIdx u) (torsIdx v) ((m : ℂ) • z)
  field_simp
  ring

theorem torsAvg_pullback {n m : ℕ} (hm : 1 ≤ m) {G : P.Fn} {w : Fin P.g → ℂ}
    (hG : ∀ u v : Fin P.g → Fin m, G (w + P.latVec (torsIdx u) (torsIdx v)) =
      P.autL n (torsIdx u) (torsIdx v) w * G w) :
    P.torsAvg n m (fun z => G ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w) = G w := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hmw : (m : ℂ) • ((m : ℂ)⁻¹ • w) = w := by rw [smul_smul, mul_inv_cancel₀ hm0, one_smul]
  have hterm : ∀ u v : Fin P.g → Fin m,
      (P.autL n (torsIdx u) (torsIdx v) ((m : ℂ) • ((m : ℂ)⁻¹ • w)))⁻¹ *
        G ((m : ℂ) • ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v))) = G w := by
    intro u v
    rw [← smul_add, hmw, smul_smul, mul_inv_cancel₀ hm0, one_smul, hG,
      ← mul_assoc, inv_mul_cancel₀ (P.autL_ne_zero _ _ _ _), one_mul]
  simp only [torsAvg, hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  have hg := pow_ne_zero P.g hm0
  rw [two_mul, pow_add]
  field_simp

end RigSymForm

end

end GroundTheory.Heights₂.Heights.KeyFormula
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

theorem VanishingCechMultInvariants.proof (hPB : PullbackMulMem.Statement)
    (hTA : TorsAvgDescends.Statement) : VanishingCechMultInvariants.Statement := by
  intro P a _ r x hx m hm n q hvan φ hφ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hmw : ∀ w : Fin P.g → ℂ, (m : ℂ) • ((m : ℂ)⁻¹ • w) = w := fun w => by
    rw [smul_smul, mul_inv_cancel₀ hm0, one_smul]

  have hprod : ∀ (J : Finset (Fin (r + 1))) u v w,
      ∏ i ∈ J, x i (w + P.latVec u v) = P.autL (a * J.card) u v w * ∏ i ∈ J, x i w := by
    intro J u v w
    rw [Finset.prod_congr rfl (fun i _ => P.thetaSec_add_latVec (P.S_le a _ (hx.1 i)) u v w),
      Finset.prod_mul_distrib, Finset.prod_const, P.autL_mul]
  have hprod0 : ∀ (J : Finset (Fin (r + 1))) w, w ∈ P.chartSet x J → ∏ i ∈ J, x i w ≠ 0 :=
    fun J w hw => Finset.prod_ne_zero_iff.mpr hw
  have hchart : ∀ (J : Finset (Fin (r + 1))) u v w, w ∈ P.chartSet x J →
      w + P.latVec u v ∈ P.chartSet x J := by
    intro J u v w hw i hi
    rw [P.thetaSec_add_latVec (P.S_le a _ (hx.1 i))]
    exact mul_ne_zero (P.autL_ne_zero _ _ _ _) (hw i hi)

  have hφt : ∀ J : Finset (Fin (r + 1)), J.card = q + 2 → ∀ w ∈ P.chartSet x J, ∀ u v,
      φ J (w + P.latVec u v) = P.autL n u v w * φ J w := by
    intro J hJ w hw u v
    obtain ⟨k, f, hf, hfe⟩ := hφ.1 J hJ
    rw [hfe _ (hchart J u v w hw), hfe _ hw, hprod, P.thetaSec_add_latVec (P.S_le _ _ hf),
      P.autL_add, P.autL_mul (a * J.card) k]
    have h1 := P.autL_ne_zero (a * J.card) u v w
    have h2 := hprod0 J w hw
    field_simp
    ring

  have hφ' : P.IsCocycle (a * m ^ 2) (n * m ^ 2) (q + 1) (fun j z => x j ((m : ℂ) • z))
      (fun J z => φ J ((m : ℂ) • z)) := by
    refine ⟨fun J hJ => ?_, fun J hJ z hz => hφ.2 J hJ _ hz⟩
    obtain ⟨k, f, hf, hfe⟩ := hφ.1 J hJ
    refine ⟨k, fun z => f ((m : ℂ) • z), ?_, fun z hz => hfe _ hz⟩
    rw [show n * m ^ 2 + a * m ^ 2 * J.card * k = (n + a * J.card * k) * m ^ 2 by ring]
    exact hPB P m _ f hf
  obtain ⟨ψ', hψ'c, hψ'd⟩ := hvan _ hφ'
  have hpt : ∀ (J : Finset (Fin (r + 1))) (w : Fin P.g → ℂ), w ∈ P.chartSet x J →
      ∀ u v : Fin P.g → Fin m, (m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v) ∈
        P.chartSet (fun j z => x j ((m : ℂ) • z)) J := by
    intro J w hw u v
    show ∀ i ∈ J, x i ((m : ℂ) • ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v))) ≠ 0
    rw [← smul_add, hmw]
    exact hchart J _ _ w hw

  refine ⟨fun J w => P.torsAvg n m (ψ' J) ((m : ℂ)⁻¹ • w), fun J hJ => ?_, fun J hJ w hw => ?_⟩
  · obtain ⟨k, F, hF, hFe⟩ := hψ'c J hJ
    have hF' : F ∈ P.S ((n + a * J.card * k) * m ^ 2) := by
      rw [show (n + a * J.card * k) * m ^ 2 = n * m ^ 2 + a * m ^ 2 * J.card * k by ring]; exact hF
    obtain ⟨f, hf, hfe⟩ := hTA P m hm _ F hF'
    refine ⟨k, f, hf, fun w hw => ?_⟩
    have hY : ∀ u v : Fin P.g → Fin m,
        (fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
          P.autL (a * J.card) (torsIdx u) (torsIdx v) ((m : ℂ) • ((m : ℂ)⁻¹ • w)) *
            (fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w) := by
      intro u v
      simp only [← smul_add, hmw]
      exact hprod J _ _ w
    have hY0 : (fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w) ≠ 0 := by
      simp only [hmw]; exact hprod0 J w hw
    have hG : ∀ u v : Fin P.g → Fin m,
        ψ' J ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
          F ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) /
            (fun z => ∏ i ∈ J, x i ((m : ℂ) • z))
              ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) ^ k := by
      intro u v
      exact hFe _ (hpt J w hw u v)
    have key := P.torsAvg_div (n := n) (d := a * J.card) (k := k) (m := m) (F := F) (G := ψ' J)
      (Y := fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) (z := (m : ℂ)⁻¹ • w) hY hY0 hG
    show P.torsAvg n m (ψ' J) ((m : ℂ)⁻¹ • w) = f w / (∏ i ∈ J, x i w) ^ k
    rw [key, hfe]
    simp only [hmw]
  · have h1 : cechD (fun J w => P.torsAvg n m (ψ' J) ((m : ℂ)⁻¹ • w)) J w =
        cechD (fun I => P.torsAvg n m (ψ' I)) J ((m : ℂ)⁻¹ • w) := by
      simp only [cechD]
    have h2 : P.torsAvg n m (cechD ψ' J) ((m : ℂ)⁻¹ • w) =
        P.torsAvg n m (fun z => φ J ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w) :=
      P.torsAvg_congr (fun u v => hψ'd J hJ _ (hpt J w hw u v))
    rw [h1, P.torsAvg_cechD, h2]
    exact P.torsAvg_pullback hm (fun u v => hφt J hJ w hw _ _)

end

end GroundTheory.Heights₂.Heights.KeyFormula
end
