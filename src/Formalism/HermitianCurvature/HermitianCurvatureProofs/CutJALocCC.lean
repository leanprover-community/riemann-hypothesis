import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBesselFold

section
open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inCC_antiA {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {A A' : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : A' ≤ A) (hF : B.InCC A m F) : B.InCC A' m F := by
  obtain ⟨c, hc1, hc2⟩ := hF
  refine ⟨c, hc1, fun u w hu hw hl g hg => ?_⟩
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 h) (norm_nonneg _)).trans
    (hc2 u w hu hw hl g hg)

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem cCg_antiA {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {A A' Bg : ℝ} {F : GFn S v} (h : A' ≤ A)
    (hF : CCg S v A Bg F) : CCg S v A' Bg F :=
  fun m => inCC_antiA (by linarith) (hF m)

theorem locCC_antiA {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A A' Bg : ℝ} {J : GFn S v} (h : A' ≤ A) (hJ : LocCC S T v A Bg J) : LocCC S T v A' Bg J := by
  refine ⟨hJ.1, fun δ hδ => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := hJ.2 δ hδ
  exact ⟨F, h1, cCg_antiA h h2, h3⟩

theorem locCC_JF {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A Bg : ℝ} {F : GFn S v} (hF : B.CkOn ⊤ (B.GV S.G.k S.G.r) F) (hA : ∀ m : ℕ, B.InCC A m F)
    (hFF : B.JF (T v).base F ∈ smoothFormsPositiveCone S T v) (hBg : 0 ≤ Bg) : LocCC S T v A Bg (B.JF (T v).base F) :=
  ⟨hFF, fun _ _ => ⟨F, hF, fun m => inCC_antiA (sub_le_self _ (mul_nonneg hBg (Nat.cast_nonneg m))) (hA m),
    fun _ _ _ => rfl⟩⟩

theorem locCC_smul {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A Bg : ℝ} (c : ℂ) {J : GFn S v} (hJ : LocCC S T v A Bg J) : LocCC S T v A Bg (c • J) := by
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.FFl_smul hJ.1 c, fun δ hδ => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := hJ.2 δ hδ
  refine ⟨c • F, Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' c h1, fun m => ?_, fun x hx hG => ?_⟩
  · obtain ⟨c0, hc0⟩ := h2 m
    exact ⟨‖c‖ * c0, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul c hc0⟩
  · rw [Formalism.FourierDecayAlt.P.CutMP.En.JF_smul', Pi.smul_apply, h3 x hx hG]

end loc

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section
open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

def JALocOp : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opApply Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opApply Θ J)

def JALocAdj : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opAdj Θ J)

def JALocPhi : Prop :=
  ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (φ : ℝ → ℝ) (Bg A : ℝ) (J : GFn S v), LE.SmoothLog φ → (∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) →
        Cg * ((S.G.r : ℝ) + 1) ≤ Bg → LocCC S T v A Bg J → mulG S T v φ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v A Bg (mulG S T v φ J)

def JALocAdd : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Bg A : ℝ) (J J' : GFn S v), 0 ≤ Bg → Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 ≤ A →
        LocCC S T v A Bg J → LocCC S T v A Bg J' → LocCC S T v A Bg (J + J')

def LocalSquareIntegrableTransfer : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Bg A ε : ℝ) (J : GFn S v) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → 0 ≤ Bg → 0 < ε →
        Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r + 5 * Bg ≤ A → LocCC S T v A Bg J →
        ∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          {q | ε ≤ MA.Gq (D.parOf S v) q} (MA.mu0 (D.parOf S v).r (D.parOf S v).TT)

theorem nDim_nonneg (k r : ℕ) : 0 ≤ nDim k r := by unfold nDim; positivity

theorem mul_mul_le_mul_mul_of_nonneg {a b x y : ℝ} (h : a ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) : a * x * y ≤ b * x * y :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hx) hy

theorem mul_le_of_le_of_mul_le {a b x B : ℝ} (h : a ≤ b) (hx : 0 ≤ x) (hB : b * x ≤ B) : a * x ≤ B :=
  (mul_le_mul_of_nonneg_right h hx).trans hB

theorem jALocCC_of_leaves (h2 : JALocOp) (h3 : JALocAdj) (h4 : JALocPhi) (h5 : JALocAdd) (h8 : LocalSquareIntegrableTransfer) :
    JALocCC := by
  obtain ⟨C2, G2, -, H2⟩ := h2
  obtain ⟨C3, G3, -, H3⟩ := h3
  obtain ⟨G4, -, H4⟩ := h4
  obtain ⟨C5, H5⟩ := h5
  obtain ⟨C8, H8⟩ := h8
  refine ⟨max (max C2 C3) (max C5 C8), max (max G2 G3) (max G4 0), le_max_of_le_right (le_max_right _ _), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hr : (0 : ℝ) ≤ (S.G.r : ℝ) + 1 := by positivity
  have hn := nDim_nonneg S.G.k S.G.r
  have hn2 : 0 ≤ nDim S.G.k S.G.r ^ 2 := by positivity
  have hr2 : (0 : ℝ) ≤ ((S.G.r : ℝ) + 1) ^ 2 := by positivity
  have c2 : C2 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_left (le_max_left _ _)
  have c3 : C3 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_left (le_max_right _ _)
  have c5 : C5 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_right (le_max_left _ _)
  have c8 : C8 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_right (le_max_right _ _)
  have g2 : G2 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_left (le_max_left _ _)
  have g3 : G3 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_left (le_max_right _ _)
  have g4 : G4 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_right (le_max_left _ _)
  refine ⟨fun F A Bg h1 h2 h3 h4 => locCC_JF h1 h2 h3 h4, ?_, ?_, ?_, ?_, fun Bg A c J hJ => locCC_smul c hJ,
    fun Bg A A' J h hJ => locCC_antiA h hJ, ?_⟩
  · intro Θ d Bg A J hd hG hAA hCut hA hJ hFF
    exact H2 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Θ d Bg A J hd (mul_le_of_le_of_mul_le g2 hr hG) hAA hCut
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c2 hr hn2]) hA) hJ hFF
  · intro Θ d Bg A J hd hG hAA hCut hA hJ hFF
    exact H3 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Θ d Bg A J hd (mul_le_of_le_of_mul_le g3 hr hG) hAA hCut
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c3 hr hn2]) hA) hJ hFF
  · intro φ Bg A J hφ hld hG hJ hFF
    exact H4 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v φ Bg A J hφ hld (mul_le_of_le_of_mul_le g4 hr hG) hJ hFF
  · intro Bg A J J' hBg hA hJ hJ'
    exact H5 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Bg A J J' hBg (le_trans (mul_mul_le_mul_mul_of_nonneg c5 hr hn2) hA) hJ hJ'
  · intro Bg A ε J e hFr hBg hε hA hJ π
    exact H8 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Bg A ε J e hFr hBg hε
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c8 hr2 hn]) hA) hJ π

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end
