import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl

open Matrix MeasureTheory Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.RadialRuleConsequences

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (Jop scalMat mulAfter Op4 op4Mul tens1 tens2 RhOp thLog fsFun Umat modL JL TmatVStar ncGap
  IsPosDefZ zpt fhat headEl headLt levOf haarOf cutF energy Std lenI mid3 wnormSq IsKFinCoefT)

def adm1 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaB CB

def WittOrbitTheorem (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_gauge

def adm2b (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stA_herm C

def adm2c (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_capelli

def adm3a (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanTopCondition

def IntegralityRemainder (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_signs

def RTTRelation (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_rtt

def adm5 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_det

def HeckeCorrespondenceReflex (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_module C

def TelescopingFormStatement (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_tele

def ConjugateSelfDualCharacter (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_entry

def DualityInequality (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_dual C

def PlaneWaveIsometry (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanWaveCondition

def FrameIntegrationFormula (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stD C

def PositivityTheoremP (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stE C

def ArithmeticRiemannRochThetaCond (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stLetters

def LogThetaIdentity (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stThLog

def PlaneWaveLetters (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stWaveLetters

def CapelliEigenvalueAlt (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stCapEig

def adm2 (D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := WittOrbitTheorem D ∧ adm2b D CB ∧ adm2c D ∧ CapelliEigenvalueAlt D

def adm3b (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.DiagonalEntryIdentity

def adm3 (D : Formalism.BasicNotions.D7) : Prop := adm3a D ∧ adm3b D ∧ IntegralityRemainder D

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) : Prop := ArithmeticRiemannRochThetaCond D ∧ RTTRelation D

def TorsionSectionsReflex (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_rrherm C

def adm6 (D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := HeckeCorrespondenceReflex D CB ∧ TorsionSectionsReflex D CB

def adm7 (D : Formalism.BasicNotions.D7) : Prop := TelescopingFormStatement D ∧ ConjugateSelfDualCharacter D

def DualityForLists (_D : Formalism.BasicNotions.D7) (C Co Cd : ℝ) : Prop := 0 < Co ∧ S.UnitaryLevelOperators.stDualList C Co Cd

def adm8 (D : Formalism.BasicNotions.D7) (CB Co Cd : ℝ) : Prop := DualityInequality D CB ∧ DualityForLists D CB Co Cd

def IntegrationByPartsAlt (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stIBP

def adm9 (D : Formalism.BasicNotions.D7) : Prop := IntegrationByPartsAlt D ∧ LogThetaIdentity D

def adm10 (D : Formalism.BasicNotions.D7) : Prop := PlaneWaveLetters D ∧ PlaneWaveIsometry D

def adm11 (_D : Formalism.BasicNotions.D7) (CB Cv C1 C2 : ℝ) : Prop := 0 < C1 ∧ S.UnitaryLevelOperators.stLevel CB Cv C1 C2

def SliceBoundC (_D : Formalism.BasicNotions.D7) (Cs : ℝ) : Prop := S.UnitaryLevelOperators.stSlices Cs

def SmoothnessTheoremP (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := S.UnitaryLevelOperators.stSmooth CB

def SliceBoundE (_D : Formalism.BasicNotions.D7) (Cs : ℝ) : Prop := S.GramWordSpace.Slices Cs

def adm12 (D : Formalism.BasicNotions.D7) (CB Cs : ℝ) : Prop :=
  FrameIntegrationFormula D CB ∧ PositivityTheoremP D CB ∧ SliceBoundC D Cs ∧ SmoothnessTheoremP D CB ∧ SliceBoundE D Cs

def adm13 (D : Formalism.BasicNotions.D7) (c C₁ : ℝ) : Prop := S.UnitaryLevelOperators.stDecay D c C₁

def adm14 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stMarkov

def adm15 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stHerglotz

def adm16 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stPoisson

def adm17 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stStatPhase

def adm18 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stJSZ1

def Conclusion1 (D : Formalism.BasicNotions.D7) (Cg CI : ℝ) : Prop :=
  ∀ (k0 : ℕ) (hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS)
    (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) (I : Set ℝ) (N : ℕ)
    (f : Matrix (Fin (2 * D.R.rS + (k0 + 1) + 1)) (Fin (2 * D.R.rS + (k0 + 1) + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (χ : ℝ → ℝ) (w : Word),
    Std D hk L μsec I →
    InterlaceS (by omega : k0 + 1 ≤ 2 * D.R.rS + (k0 + 1) + 1) L.u L.lam →
    InterlaceS (by omega : k0 + 1 ≤ 2 * D.R.rS + (k0 + 1) + 1) L.u' L.lam →
    GapAtLeast L.ε L.lam (Cg * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * ((N : ℝ) * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3)) →
    D.R.rS + 1 ≤ N →
    CI * ((D.R.k : ℝ) * N * ((D.R.rS : ℝ) + 1) ^ 2 + (N : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2) ≤ sSup I - sInf I →
    IsKFinCoefT L.σ f → IsCutoff χ → Admissible I w → w.length ≤ N →
    Tendsto (fun ε : ℝ => energy L μsec I w (cutF L.z L.z' χ ε f)) (𝓝[>] 0)
      (𝓝 ((brkW L.lam (w.map Prod.snd) : ℂ) * L.beta μsec f f))

def Conclusion2 (D : Formalism.BasicNotions.D7) (C0 CA : ℝ) : Prop := S.UnitaryLevelOperators.stLemE' D C0 CA

def admitted (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) : Prop :=
  adm1 D CB ∧ adm2 D CB ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D CB ∧ adm7 D ∧ adm8 D CB Co Cd ∧ adm9 D ∧ adm10 D ∧
    adm11 D CB Cv C1 C2 ∧ adm12 D CB Cs ∧ adm13 D c C₁ ∧ adm14 D ∧ adm15 D ∧ adm16 D ∧ adm17 D ∧ adm18 D

def Stmt (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA : ℝ) : Prop :=
  admitted D CB Co Cd Cv C1 C2 Cs c C₁ → Conclusion1 D Cg CI ∧ Conclusion2 D C0 CA

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def admF1 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i) CB
def admF2 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i) CB
def admF3 : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)
def admF4 : Prop := ∀ x (i : Fm.Ix x), ArchimedeanSignatureMatching (Fm.D x i)
def admF5 : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i)
def admF6 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i) CB
def admF7 : Prop := ∀ x (i : Fm.Ix x), adm7 (Fm.D x i)
def admF8 (CB Co Cd : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm8 (Fm.D x i) CB Co Cd
def admF9 : Prop := ∀ x (i : Fm.Ix x), adm9 (Fm.D x i)
def FamilyRowsCountHypothesis : Prop := ∀ x (i : Fm.Ix x), adm10 (Fm.D x i)
def FamilyWeylAndVandermonde (CB Cv C1 C2 : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm11 (Fm.D x i) CB Cv C1 C2
def FamilyTwelfthHypothesis (CB Cs : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm12 (Fm.D x i) CB Cs
def FamilyThirteenthHypothesis (c C₁ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm13 (Fm.D x i) c C₁
def FamilyFourteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm14 (Fm.D x i)
def FamilyFifteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm15 (Fm.D x i)
def FamilySixteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm16 (Fm.D x i)
def FamilyStationaryPhase : Prop := ∀ x (i : Fm.Ix x), adm17 (Fm.D x i)
def FamilyBesselUniqueness : Prop := ∀ x (i : Fm.Ix x), adm18 (Fm.D x i)

def AdmF (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) : Prop :=
  admF1 Fm CB ∧ admF2 Fm CB ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm CB ∧ admF7 Fm ∧ admF8 Fm CB Co Cd ∧ admF9 Fm ∧
    FamilyRowsCountHypothesis Fm ∧ FamilyWeylAndVandermonde Fm CB Cv C1 C2 ∧ FamilyTwelfthHypothesis Fm CB Cs ∧ FamilyThirteenthHypothesis Fm c C₁ ∧ FamilyFourteenthHypothesis Fm ∧ FamilyFifteenthHypothesis Fm ∧ FamilySixteenthHypothesis Fm ∧
    FamilyStationaryPhase Fm ∧ FamilyBesselUniqueness Fm

def ConclusionF1 (Cg CI : ℝ) : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i) Cg CI

def ConclusionF2 (C0 CA : ℝ) : Prop := ∀ x (i : Fm.Ix x), Conclusion2 (Fm.D x i) C0 CA

def KudlaFamilyStatement (CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA : ℝ) : Prop :=
  AdmF Fm CB Co Cd Cv C1 C2 Cs c C₁ → ConclusionF1 Fm Cg CI ∧ ConclusionF2 Fm C0 CA

end Family

def UniformExportStatement : Prop :=
  ∀ CB Co Cd Cv C1 C2 Cs c C₁ : ℝ, ∃ Cg₀ CI₀ C0₀ CA₀ : ℝ, ∀ Cg ≥ Cg₀, ∀ CI ≥ CI₀, ∀ C0 ≥ C0₀, ∀ CA ≥ CA₀,
    ∀ D : Formalism.BasicNotions.D7, Stmt D CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA

theorem hsInner_smul_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (w : ℝ) (A B : Wq →L[ℂ] Wp) :
    hsInner ((w : ℂ) • A) ((w : ℂ) • B) = ((w ^ 2 : ℝ) : ℂ) * hsInner A B := by
  simp only [hsInner, _root_.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

theorem hsInner_zero_left {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (B : Wq →L[ℂ] Wp) : hsInner (0 : Wq →L[ℂ] Wp) B = 0 := by
  simp [hsInner]

theorem weight_eq (k0 r : ℕ) (T T' : ℝ) (x : Fin (r + 1) → ℂ) (hx : x ∈ OmX (r + 1))
    (hz : T * T' < Complex.normSq (zOf x)) :
    bcWeight (k0 + 1) r T T' (cOf x, zOf x) =
      (∏ a : Fin r, Complex.normSq (cOf x a))⁻¹ *
        ((∏ a : Fin r, ‖cOf x a‖ ^ (Mdim (k0 + 1) r a - 1)) *
          (Complex.normSq (zOf x) - T * T') ^ ((((k0 + 1 : ℕ) : ℝ) - 1) / 2)) ^ 2 := by
  have hG : 0 < Complex.normSq (zOf x) - T * T' := by linarith
  have h1 : ((Complex.normSq (zOf x) - T * T') ^ ((((k0 + 1 : ℕ) : ℝ) - 1) / 2)) ^ 2 =
      (Complex.normSq (zOf x) - T * T') ^ (k0 + 1 - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hG.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    simp
  have h2 : (∏ a : Fin r, Complex.normSq (cOf x a))⁻¹ * (∏ a : Fin r, ‖cOf x a‖ ^ (Mdim (k0 + 1) r a - 1)) ^ 2 =
      ∏ a : Fin r, ‖cOf x a‖ ^ (2 * (Mdim (k0 + 1) r a - 2)) := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hc : ‖cOf x a‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact hx _
    obtain ⟨n, hn⟩ : ∃ n, Mdim (k0 + 1) r a = n + 2 := ⟨2 * (r - a.val) + k0, by unfold Mdim; omega⟩
    rw [hn, Complex.normSq_eq_norm_sq]
    have e1 : n + 2 - 1 = n + 1 := by omega
    have e2 : n + 2 - 2 = n := by omega
    rw [e1, e2]
    field_simp
    ring
  unfold bcWeight
  rw [if_pos hz.le, mul_pow, h1, ← mul_assoc, h2]










theorem minWeight_pos (D : Formalism.BasicNotions.D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) : 0 < k0 := by
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  omega

end Formalism.MainNotions.RadialRuleConsequences
