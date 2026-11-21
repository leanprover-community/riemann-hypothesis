import CompanionTheory.AutomorphicTheory.BesselWaveGrids.AsmDiff
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.GridsText
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.LimBdSh
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.CoefFacts
import CompanionTheory.AutomorphicTheory.KFiniteVectors.KDecay

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants
open CompanionTheory.LimBd.Main (GfPoly SpanPow CoefSmooth CoefCC CoefEig PhZero BetaInfZero ZuckT ZuckDualT Box KDecay
  eigStr_of_steps)
open CompanionTheory.WaveGrid.Coef

def LimSteps : Prop := GfPoly ∧ SpanPow ∧ CoefSmooth ∧ CoefCC ∧ CoefEig ∧ PhZero ∧ BetaInfZero

theorem pStar_box {n : ℕ} {lam lam' : Fin n → ℝ} {e d c : ℝ} (h : lam' ∈ Box lam e) (hd : 0 ≤ d) (hc : e + d ≤ c)
    (y : ℝ) : CompanionTheory.LimBd.Main.PStar lam' d y ≤ PStar lam c y := by
  refine Finset.prod_le_prod (fun _ _ => add_nonneg (abs_nonneg _) hd) fun s _ => ?_
  have h1 := h s
  have h2 := abs_add_le (y + lam s) (lam' s - lam s)
  rw [show y + lam s + (lam' s - lam s) = y + lam' s by ring] at h2
  linarith

theorem kDecay_of_gap {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    {X d h : ℝ} (hX : 0 ≤ X) (hd : 0 ≤ d) (hh : t _ ε + X + 3 * d + 1 < h) : KDecay k r ε (X + d) (h - 2 * d) := by
  refine MainStatements.BetaInf.kDecay_of_zuckT hZ k r ε ⌈X + d⌉₊ _ _ (Nat.le_ceil _) ?_
  have := Nat.ceil_lt_add_one (show 0 ≤ X + d by linarith)
  linarith

theorem gap_mono {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h h' : ℝ} (hg : PI.ZuckTensor.GapAtLeast ε lam h)
    (hh : h' ≤ h) : PI.ZuckTensor.GapAtLeast ε lam h' := fun a b hab => hh.trans (hg a b hab)

def EndDiff (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ Cb C₃ CT C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CT → 1 / 2 ≤ C₀ →
    ∃ C₄ CA : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] [CompleteSpace Wp] (P : M.Par)
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (p₀ : ℕ)
      (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (ε : Fin (2 * P.r + P.k + 1) → Bool) (c g e h : ℝ),
      KFinDSCoef ε lam' f → lam' ∈ Box lam e → e + (((2 * P.r + 2) * p₀ : ℕ) : ℝ) ≤ c →
      PI.ZuckTensor.GapAtLeast ε lam' h → t _ ε + CA * thrX P.k P.r + 3 * (((2 * P.r + 2) * p₀ : ℕ) : ℝ) + 1 < h →
      HypLam P.k P.r lam c g b → HypType P.k P.r lam P.u b → HypType P.k P.r lam P.u' b →
      b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T' → 1 ≤ Tq p →
      30 * ((P.r : ℝ) + 1) ^ 2 + 6 ≤ |P.u p.l0 - P.u' p.l0| →
      3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) → ThmBpAt p f b C₄ 0 p₀

def EndEq (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ C₃ CT C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CT → 1 / 2 ≤ C₀ →
    ∃ C₄ CA : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] [CompleteSpace Wp] (P : M.Par)
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (p₀ n₀ l : ℕ)
      (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (ε : Fin (2 * P.r + P.k + 1) → Bool) (c g e h : ℝ),
      KFinDSCoef ε lam' f → lam' ∈ Box lam e → e + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c →
      PI.ZuckTensor.GapAtLeast ε lam' h →
      t _ ε + CA * thrX P.k P.r + 3 * (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) + 1 < h →
      HypLam P.k P.r lam c g b → HypType P.k P.r lam P.u b → P.u = P.u' →
      b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T' → 1 ≤ Tq p →
      n₀ = 30 * (P.r + 1) ^ 2 + 6 → 1 ≤ l → l < P.k → (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1) →
      3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) → ThmBpAt p f b C₄ n₀ p₀



end CompanionTheory.WaveGrid
