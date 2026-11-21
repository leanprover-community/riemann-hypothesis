import Mathlib
import GroundTheory.PAdicHodge.WAFracLemmaO
import GroundTheory.PAdicHodge.AnnNormAcrisToAnnPosBig
import GroundTheory.PAdicHodge.ExtRobbaEigen
import GroundTheory.PAdicHodge.WAFracAnnPt
import GroundTheory.PAdicHodge.WAFracOrbit
import GroundTheory.PAdicHodge.WAKummer
import GroundTheory.PAdicHodge.ExistsFactorAnn
import GroundTheory.PAdicHodge.ExistsNormLeOfNormLtOneFinite

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable {F : T.TeichFrob} {n : ℕ}

theorem exists_fixed_of_approx (ha : 0 < F.a) {ρ : Set.Ioo (0 : ℝ) 1}
    (A : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (N : ℕ) (U : ℕ → Fin n → T.RobbaExt ρ)
    (hU1 : SeqCauchy U (topRad ρ)) (hU2 : SeqCauchy U (F.radPow ρ))
    (hsmall : SeqSmall (fun J => twistDiff (F := F) A N (U J)) (topRad (F.powRadius ρ))) :
    ∃ g : Fin n → T.RobbaExt ρ, (∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ i,
        T.extNorm ρ (topRad ρ) (g i - U J i) ≤ ε ∧ T.extNorm ρ (F.radPow ρ) (g i - U J i) ≤ ε) ∧
      twistDiff (F := F) A N g = 0 := by

  set x : (t : ℕ) → ℕ → Fin n → T.RobbaExt (F.radSeq ρ t) := fun t J => F.phiIter A N (U J) t
    with hxdef
  have hCt : ∀ t, SeqCauchy (x t) (topRad _) ∧
      SeqCauchy (x t) ⟨F.radSeq ρ (t + 1), (F.radSeq ρ (t + 1)).2.1, F.radSeq_succ_le ρ t⟩ := by
    intro t
    induction t with
    | zero => exact ⟨hU1, hU2⟩
    | succ t ih =>
      exact ⟨ih.1.twistFrob A N (F.radSeq_le ρ (t + 1)), ih.2.twistFrob A N (F.radSeq_le ρ (t + 1))⟩
  have hDt : ∀ t, SeqSmall (fun J => x (t + 1) J - fun i => T.res (F.radSeq_succ_le ρ t) (x t J i))
      (topRad (F.radSeq ρ (t + 1))) := by
    intro t
    induction t with
    | zero =>
      intro ε hε
      obtain ⟨J₀, hJ₀⟩ := hsmall ε hε
      refine ⟨J₀, fun J hJ i => ?_⟩
      change T.extNorm _ _ (twistDiff (F := F) A N (U J) i) ≤ ε
      exact hJ₀ J hJ i
    | succ t ih =>
      have h := SeqSmall.twistFrob A N (F.radSeq_le ρ (t + 2)) ih
      refine fun ε hε => (h ε hε).imp fun J₀ hJ₀ J hJ i => ?_
      have e1 : (x (t + 2) J - fun i => T.res (F.radSeq_succ_le ρ (t + 1)) (x (t + 1) J i)) =
          F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2))
            (x (t + 1) J - fun i => T.res (F.radSeq_succ_le ρ t) (x t J i)) := by
        have h2 := twistFrob_res A N (F.radSeq_succ_le ρ t) (F.radSeq_le ρ (t + 1))
          (F.radSeq_le ρ (t + 2)) (x t J)
        have h3 : F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2)) (x (t + 1) J) -
              F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2))
                (fun j => T.res (F.radSeq_succ_le ρ t) (x t J j)) =
            F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2))
              (x (t + 1) J - fun i => T.res (F.radSeq_succ_le ρ t) (x t J i)) :=
          (twistFrob_sub A N (F.radSeq_le ρ (t + 2)) _ _).symm
        rw [← h3]
        exact congrArg₂ (· - ·) rfl h2.symm
      show T.extNorm _ (topRad (F.radSeq ρ (t + 2)))
        ((x (t + 2) J - fun i => T.res (F.radSeq_succ_le ρ (t + 1)) (x (t + 1) J i)) i) ≤ ε
      rw [e1]
      exact hJ₀ J hJ i

  have hglue : ∀ i, ∃ g : T.RobbaExt ρ, ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀,
      T.extNorm ρ (topRad ρ) (g - U J i) ≤ ε ∧ T.extNorm ρ (F.radPow ρ) (g - U J i) ≤ ε := by
    intro i
    refine exists_glue (F.radSeq ρ) (F.radSeq_succ_le ρ) (F.tendsto_radSeq ha ρ)
      (fun t J => x t J i) (fun t ε hε => ?_) (fun t ε hε => ?_)
    · obtain ⟨J₁, h1⟩ := (hCt t).1 ε hε
      obtain ⟨J₂, h2⟩ := (hCt t).2 ε hε
      exact ⟨max J₁ J₂, fun J hJ K hK => ⟨h1 J (le_of_max_le_left hJ) K (le_of_max_le_left hK) i,
        h2 J (le_of_max_le_right hJ) K (le_of_max_le_right hK) i⟩⟩
    · obtain ⟨J₀, h⟩ := hDt t ε hε
      refine ⟨J₀, fun J hJ => ?_⟩
      have := h J hJ i
      rw [← extNorm_neg, neg_sub]
      exact this
  choose g hg using hglue
  refine ⟨g, fun ε hε => ?_, ?_⟩
  ·
    choose J₀ hJ₀ using fun i => hg i ε hε
    exact ⟨Finset.univ.sup J₀, fun J hJ i =>
      hJ₀ i J ((Finset.le_sup (Finset.mem_univ i)).trans hJ)⟩
  ·
    funext i
    rw [Pi.zero_apply]
    apply (T.extNorm_eq_zero_iff (topRad _)).1
    have key : ∀ ε > 0, T.extNorm _ (topRad _) (twistDiff (F := F) A N g i) ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hsm⟩ := twistFrob_small A N (F.powRadius_le_self ρ) (topRad ρ) hε
      have hev : ∀ j, ∀ᶠ J in atTop, T.extNorm ρ (topRad ρ) (g j - U J j) ≤ δ := fun j => by
        obtain ⟨J₀, h⟩ := hg j δ hδ
        exact eventually_atTop.2 ⟨J₀, fun J hJ => (h J hJ).1⟩
      have hev2 : ∀ᶠ J in atTop, T.extNorm ρ (F.radPow ρ) (g i - U J i) ≤ ε := by
        obtain ⟨J₀, h⟩ := hg i ε hε
        exact eventually_atTop.2 ⟨J₀, fun J hJ => (h J hJ).2⟩
      have hev3 : ∀ᶠ J in atTop, T.extNorm _ (topRad _) (twistDiff (F := F) A N (U J) i) ≤ ε := by
        obtain ⟨J₀, h⟩ := hsmall ε hε
        exact eventually_atTop.2 ⟨J₀, fun J hJ => h J hJ i⟩
      obtain ⟨J, hJ1, hJ2, hJ3⟩ := ((Filter.eventually_all.2 hev).and (hev2.and hev3)).exists
      have h1 : F.twistFrob A N ρ (F.powRadius_le_self ρ) g i =
          F.twistFrob A N ρ (F.powRadius_le_self ρ) (g - U J) i +
            F.twistFrob A N ρ (F.powRadius_le_self ρ) (U J) i := by
        rw [twistFrob_sub, Pi.sub_apply, sub_add_cancel]
      simp only [twistDiff, Pi.sub_apply] at hJ3 ⊢
      have e2 : F.twistFrob A N ρ (F.powRadius_le_self ρ) g i - T.res (F.powRadius_le_self ρ) (g i) =
          F.twistFrob A N ρ (F.powRadius_le_self ρ) (g - U J) i +
            (F.twistFrob A N ρ (F.powRadius_le_self ρ) (U J) i - T.res (F.powRadius_le_self ρ) (U J i)) +
            -T.res (F.powRadius_le_self ρ) (g i - U J i) := by
        rw [h1, map_sub]; ring
      rw [e2]
      refine (extNorm_add_add_le_max _ _ _ _).trans (max_le (hsm (g - U J) (fun j => hJ1 j) i)
        (max_le hJ3 ?_))
      rw [extNorm_neg, extNorm_res]
      exact hJ2
    have h0 := T.extNorm_nonneg (topRad (F.powRadius ρ)) (twistDiff (F := F) A N g i)
    by_contra hne
    have hpos : 0 < T.extNorm _ (topRad _) (twistDiff (F := F) A N g i) :=
      lt_of_le_of_ne h0 (Ne.symm hne)
    linarith [key _ (half_pos hpos)]

theorem twistDiff_one_apply {ρ : Set.Ioo (0 : ℝ) 1} (N : ℕ) (w : Fin 1 → T.RobbaExt ρ) :
    twistDiff (F := F) (1 : Matrix (Fin 1) (Fin 1) (T.RobbaExt ρ)) N w 0 =
      T.piInvE (F.powRadius ρ) ^ N * F.extFrob ρ (w 0) - T.res (F.powRadius_le_self ρ) (w 0) := by
  simp [twistDiff, twistFrob, Matrix.one_apply]

theorem extFrob_sub_eq_piE_pow_mul {ρ : Set.Ioo (0 : ℝ) 1} (N : ℕ) (w : T.RobbaExt ρ) :
    F.extFrob ρ w - T.piE (F.powRadius ρ) ^ N * T.res (F.powRadius_le_self ρ) w =
      T.piE (F.powRadius ρ) ^ N *
        (T.piInvE (F.powRadius ρ) ^ N * F.extFrob ρ w - T.res (F.powRadius_le_self ρ) w) := by
  have h := T.piE_mul_piInvE (F.powRadius ρ)
  have h' : T.piE (F.powRadius ρ) ^ N * T.piInvE (F.powRadius ρ) ^ N = 1 := by
    rw [← mul_pow, h, one_pow]
  linear_combination (F.extFrob ρ w) * h'.symm

theorem exists_eigen_of_approx (ha : 0 < F.a) {ρ : Set.Ioo (0 : ℝ) 1} (N : ℕ)
    (u : ℕ → T.RobbaExt ρ)
    (hu1 : ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀, T.extNorm ρ (topRad ρ) (u J - u K) ≤ ε)
    (hu2 : ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀, T.extNorm ρ (F.radPow ρ) (u J - u K) ≤ ε)
    (hsmall : ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, T.extNorm (F.powRadius ρ) (topRad _)
      (F.extFrob ρ (u J) - T.piE (F.powRadius ρ) ^ N * T.res (F.powRadius_le_self ρ) (u J)) ≤ ε) :
    ∃ g : T.RobbaExt ρ, (∀ ε > 0, ∃ J₀, ∀ J ≥ J₀,
        T.extNorm ρ (topRad ρ) (g - u J) ≤ ε ∧ T.extNorm ρ (F.radPow ρ) (g - u J) ≤ ε) ∧
      F.extFrob ρ g = T.piE (F.powRadius ρ) ^ N * T.res (F.powRadius_le_self ρ) g := by
  set U : ℕ → Fin 1 → T.RobbaExt ρ := fun J _ => u J with hUdef
  set σ := F.powRadius ρ with hσ
  have hσ0 : (0 : ℝ) < σ := σ.2.1

  have hinv : T.extNorm σ (topRad σ) (T.piInvE σ ^ N) = ((σ : ℝ) ^ N)⁻¹ := by
    rw [extNorm_pow', extNorm_piInvE]
    simp [topRad, inv_pow]
  have hsm : SeqSmall (fun J => twistDiff (F := F) (1 : Matrix (Fin 1) (Fin 1) (T.RobbaExt ρ)) N (U J))
      (topRad σ) := by
    intro ε hε
    obtain ⟨J₀, hJ₀⟩ := hsmall ((σ : ℝ) ^ N * ε) (mul_pos (pow_pos hσ0 N) hε)
    refine ⟨J₀, fun J hJ i => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    show T.extNorm σ (topRad σ)
      (twistDiff (F := F) (1 : Matrix (Fin 1) (Fin 1) (T.RobbaExt ρ)) N (U J) 0) ≤ ε
    rw [twistDiff_one_apply]
    have e : T.piInvE σ ^ N * F.extFrob ρ (u J) - T.res (F.powRadius_le_self ρ) (u J) =
        T.piInvE σ ^ N * (F.extFrob ρ (u J) - T.piE σ ^ N * T.res (F.powRadius_le_self ρ) (u J)) := by
      have h := T.piE_mul_piInvE σ
      have h' : T.piInvE σ ^ N * T.piE σ ^ N = 1 := by rw [← mul_pow, mul_comm, h, one_pow]
      linear_combination (T.res (F.powRadius_le_self ρ) (u J)) * h'
    show T.extNorm σ (topRad σ) (T.piInvE σ ^ N * F.extFrob ρ (u J) -
      T.res (F.powRadius_le_self ρ) (u J)) ≤ ε
    rw [e, extNorm_mul, hinv]
    have h1 := hJ₀ J hJ
    calc ((σ : ℝ) ^ N)⁻¹ * T.extNorm σ (topRad σ)
          (F.extFrob ρ (u J) - T.piE σ ^ N * T.res (F.powRadius_le_self ρ) (u J))
        ≤ ((σ : ℝ) ^ N)⁻¹ * ((σ : ℝ) ^ N * ε) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (pow_nonneg hσ0.le N))
      _ = ε := by field_simp
  obtain ⟨g, hg, hfix⟩ := exists_fixed_of_approx ha (1 : Matrix (Fin 1) (Fin 1) (T.RobbaExt ρ)) N U
    (fun ε hε => (hu1 ε hε).imp fun J₀ h J hJ K hK _ => h J hJ K hK)
    (fun ε hε => (hu2 ε hε).imp fun J₀ h J hJ K hK _ => h J hJ K hK) hsm
  refine ⟨g 0, fun ε hε => (hg ε hε).imp fun J₀ h J hJ => h J hJ 0, ?_⟩
  have h0 := congrFun hfix 0
  rw [twistDiff_one_apply, Pi.zero_apply] at h0
  have e := extFrob_sub_eq_piE_pow_mul (F := F) N (g 0)
  rw [h0, mul_zero] at e
  exact sub_eq_zero.1 e

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔽" => frob ℂ_[p] p

variable (p) (ρ1 : Set.Ioo (0 : ℝ) 1)

abbrev inRad : Set.Ioc (0 : ℝ) ρ1 := (𝔽).radPow ρ1

abbrev circ : Set.Ioo (0 : ℝ) 1 := (𝔽).powRadius ρ1

theorem coe_circ : ((circ p ρ1 : Set.Ioo (0 : ℝ) 1) : ℝ) = (ρ1 : ℝ) ^ p := by
  show (ρ1 : ℝ) ^ p ^ (𝔽).a = _; rw [frob_a, pow_one]

theorem coe_inRad : ((inRad p ρ1 : Set.Ioc (0 : ℝ) ρ1) : ℝ) = (ρ1 : ℝ) ^ p := coe_circ p ρ1

theorem coe_topRad_circ : ((topRad (circ p ρ1) : Set.Ioc (0 : ℝ) (circ p ρ1)) : ℝ) = (ρ1 : ℝ) ^ p :=
  coe_circ p ρ1

theorem inRad_le_circ : ((inRad p ρ1 : Set.Ioc (0 : ℝ) ρ1) : ℝ) ≤ (topRad (circ p ρ1) : ℝ) := by
  rw [coe_inRad, coe_topRad_circ]

theorem powRad_inRad_le :
    ((((𝔽).powRad (inRad p ρ1)) : Set.Ioc (0 : ℝ) (circ p ρ1)) : ℝ) ≤ (topRad (circ p ρ1) : ℝ) := by
  rw [TeichLift.TeichFrob.coe_powRad, frob_a, pow_one, coe_inRad, coe_topRad_circ, ← pow_mul]
  exact pow_le_pow_of_le_one ρ1.2.1.le ρ1.2.2.le (Nat.le_mul_of_pos_left p hp.out.pos)

theorem circ_le : ((circ p ρ1 : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ1 := (𝔽).powRadius_le_self ρ1

def resCirc : (𝓣).Ann ρ1 (inRad p ρ1) →+* (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1)) :=
  (𝓣).annRes (circ_le p ρ1) (inRad_le_circ p ρ1)

def frobCirc : (𝓣).Ann ρ1 (inRad p ρ1) →+* (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1)) :=
  ((𝓣).annRes (le_refl ((circ p ρ1 : Set.Ioo (0 : ℝ) 1) : ℝ)) (powRad_inRad_le p ρ1)).comp (𝔽).annFrob

abbrev circRad : AnnRad (circ p ρ1) (topRad (circ p ρ1)) := annIn (circ p ρ1) (topRad (circ p ρ1))

variable {p}

theorem annNorm_frobCirc (x : (𝓣).Ann ρ1 (inRad p ρ1)) :
    (𝓣).annNorm _ _ (circRad p ρ1) (frobCirc p ρ1 x) =
      (𝓣).annNorm ρ1 (inRad p ρ1) (annOut ρ1 (inRad p ρ1)) x ^ p := by
  rw [frobCirc, RingHom.comp_apply, (𝓣).annNorm_annRes]
  have e : annRadOf (le_refl ((circ p ρ1 : Set.Ioo (0 : ℝ) 1) : ℝ)) (powRad_inRad_le p ρ1) (circRad p ρ1) =
      (𝔽).annPowRad (annOut ρ1 (inRad p ρ1)) := by
    apply Subtype.ext
    rw [coe_annRadOf, TeichLift.TeichFrob.coe_annPowRad, frob_a, pow_one, coe_annOut, coe_annIn,
      coe_topRad_circ]
  rw [e, TeichLift.TeichFrob.annNorm_annFrob, frob_a, pow_one]

theorem annNorm_resCirc (x : (𝓣).Ann ρ1 (inRad p ρ1)) :
    (𝓣).annNorm _ _ (circRad p ρ1) (resCirc p ρ1 x) =
      (𝓣).annNorm ρ1 (inRad p ρ1) (annIn ρ1 (inRad p ρ1)) x := by
  rw [resCirc, (𝓣).annNorm_annRes]
  congr 1

theorem piE_eq_natCast (σ : Set.Ioo (0 : ℝ) 1) : (𝓣).piE σ = (p : (𝓣).RobbaExt σ) := by
  rw [TeichLift.piE, TeichLift.ofAll]
  rw [← map_natCast (Completion.coeRingHom : (𝓣).Econ σ →+* (𝓣).RobbaExt σ) p]
  congr 1
  apply Subtype.ext
  change algebraMap (WC p) (𝓣).B ((p : ℕ) : WC p) = (((p : ℕ) : (𝓣).Econ σ) : (𝓣).B)
  rw [map_natCast]
  simp

theorem annNorm_coeAnn_sub (r : AnnRad ρ1 (inRad p ρ1)) (a b : (𝓣).Econ ρ1) :
    (𝓣).annNorm ρ1 (inRad p ρ1) r ((𝓣).coeAnn a - (𝓣).coeAnn b) =
      (𝓣).extNorm ρ1 (annIoc r) ((a : (𝓣).RobbaExt ρ1) - b) := by
  rw [← (𝓣).toAnn_coe, ← (𝓣).toAnn_coe, ← map_sub, (𝓣).annNorm_toAnn]

theorem annIoc_annOut : annIoc (annOut ρ1 (inRad p ρ1)) = topRad ρ1 := rfl

theorem annIoc_annIn : annIoc (annIn ρ1 (inRad p ρ1)) = (𝔽).radPow ρ1 := rfl

theorem frobCirc_toAnn (w : (𝓣).RobbaExt ρ1) :
    frobCirc p ρ1 ((𝓣).toAnn ρ1 (inRad p ρ1) w) =
      (𝓣).toAnn (circ p ρ1) (topRad (circ p ρ1)) ((𝔽).extFrob ρ1 w) := by
  rw [frobCirc, RingHom.comp_apply, TeichLift.TeichFrob.annFrob_toAnn, (𝓣).annRes_toAnn, (𝓣).res_self]

theorem resCirc_toAnn (w : (𝓣).RobbaExt ρ1) :
    resCirc p ρ1 ((𝓣).toAnn ρ1 (inRad p ρ1) w) =
      (𝓣).toAnn (circ p ρ1) (topRad (circ p ρ1)) ((𝓣).res ((𝔽).powRadius_le_self ρ1) w) := by
  rw [resCirc, (𝓣).annRes_toAnn]

theorem annNorm_natCast_p_circ :
    (𝓣).annNorm _ _ (circRad p ρ1) (p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) = (ρ1 : ℝ) ^ p := by
  rw [annNorm_awayToAnn_natCast_p]; exact coe_circ p ρ1

set_option maxHeartbeats 3200000 in

theorem exists_eigen_of_ann (N : ℕ) (Y : (𝓣).Ann ρ1 (inRad p ρ1))
    (hY : (𝓣).annNorm _ _ (circRad p ρ1)
      (frobCirc p ρ1 Y - (p : (𝓣).Ann _ _) ^ N * resCirc p ρ1 Y) = 0) :
    ∃ g : (𝓣).RobbaExt ρ1, (𝔽).extFrob ρ1 g = (p : (𝓣).RobbaExt _) ^ N *
        (𝓣).res ((𝔽).powRadius_le_self ρ1) g ∧ (𝓣).toAnn ρ1 (inRad p ρ1) g = Y := by
  choose U hU using fun J : ℕ => (𝓣).exists_coeAnn_near Y (Nat.one_div_pos_of_nat (n := J))
  set u : ℕ → (𝓣).RobbaExt ρ1 := fun J => (U J : (𝓣).RobbaExt ρ1) with hudef
  have hdiff : ∀ (r : AnnRad ρ1 (inRad p ρ1)) (J K : ℕ), (𝓣).extNorm ρ1 (annIoc r) (u J - u K) ≤
      max (1 / ((J : ℝ) + 1)) (1 / ((K : ℝ) + 1)) := by
    intro r J K
    rw [hudef, ← annNorm_coeAnn_sub]
    have e : (𝓣).coeAnn (U J) - (𝓣).coeAnn (U K) = -(Y - (𝓣).coeAnn (U J)) + (Y - (𝓣).coeAnn (U K)) := by
      ring
    rw [e]
    refine ((𝓣).annNorm_add_le r _ _).trans (max_le_max ?_ (hU K r).le)
    rw [(𝓣).annNorm_neg]; exact (hU J r).le
  have hcau : ∀ r : AnnRad ρ1 (inRad p ρ1), ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀,
      (𝓣).extNorm ρ1 (annIoc r) (u J - u K) ≤ ε := by
    intro r ε hε
    obtain ⟨J₀, hJ₀⟩ := exists_nat_one_div_lt hε
    refine ⟨J₀, fun J hJ K hK => (hdiff r J K).trans (max_le ?_ ?_)⟩
    · exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hJ 1)).trans hJ₀.le
    · exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hK 1)).trans hJ₀.le

  have hD : ∀ J, (𝓣).extNorm (circ p ρ1) (topRad _)
      ((𝔽).extFrob ρ1 (u J) - (𝓣).piE ((𝔽).powRadius ρ1) ^ N * (𝓣).res ((𝔽).powRadius_le_self ρ1) (u J)) ≤
        1 / ((J : ℝ) + 1) := by
    intro J
    have hJ1 : 1 / ((J : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
    rw [piE_eq_natCast]
    have e1 := (𝓣).annNorm_toAnn (circRad p ρ1)
      ((𝔽).extFrob ρ1 (u J) - (p : (𝓣).RobbaExt _) ^ N * (𝓣).res ((𝔽).powRadius_le_self ρ1) (u J))
    have hioc : annIoc (circRad p ρ1) = topRad (circ p ρ1) := rfl
    rw [hioc] at e1
    rw [← e1, map_sub, map_mul, map_pow, map_natCast, ← frobCirc_toAnn, ← resCirc_toAnn, hudef,
      (𝓣).toAnn_coe]
    set c := (𝓣).coeAnn (σ0 := inRad p ρ1) (U J)
    have e2 : frobCirc p ρ1 c - (p : (𝓣).Ann _ _) ^ N * resCirc p ρ1 c =
        (frobCirc p ρ1 (c - Y) - (p : (𝓣).Ann _ _) ^ N * resCirc p ρ1 (c - Y)) +
          (frobCirc p ρ1 Y - (p : (𝓣).Ann _ _) ^ N * resCirc p ρ1 Y) := by
      rw [map_sub, map_sub]; ring
    rw [e2]
    refine ((𝓣).annNorm_add_le _ _ _).trans (max_le ?_ (by rw [hY]; positivity))
    refine ((𝓣).annNorm_sub_le _ _ _).trans (max_le ?_ ?_)
    · rw [annNorm_frobCirc, (𝓣).annNorm_sub_comm]
      exact (pow_le_of_le_one ((𝓣).annNorm_nonneg _ _) ((hU J _).le.trans hJ1) hp.out.ne_zero).trans
        (hU J _).le
    · rw [(𝓣).annNorm_mul, (𝓣).annNorm_pow, annNorm_natCast_p_circ, annNorm_resCirc, (𝓣).annNorm_sub_comm]
      refine (mul_le_of_le_one_left ((𝓣).annNorm_nonneg _ _) ?_).trans (hU J _).le
      exact pow_le_one₀ (pow_nonneg ρ1.2.1.le p) (pow_le_one₀ ρ1.2.1.le ρ1.2.2.le)
  have hsmall : ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, (𝓣).extNorm ((𝔽).powRadius ρ1) (topRad _)
      ((𝔽).extFrob ρ1 (u J) - (𝓣).piE ((𝔽).powRadius ρ1) ^ N * (𝓣).res ((𝔽).powRadius_le_self ρ1) (u J))
        ≤ ε := by
    intro ε hε
    obtain ⟨J₀, hJ₀⟩ := exists_nat_one_div_lt hε
    refine ⟨J₀, fun J hJ => (hD J).trans ?_⟩
    exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hJ 1)).trans hJ₀.le
  obtain ⟨g, hg, hgeq⟩ := TeichLift.TeichFrob.exists_eigen_of_approx (F := 𝔽) (by rw [frob_a]; exact one_pos)
    N u (hcau (annOut ρ1 (inRad p ρ1))) (hcau (annIn ρ1 (inRad p ρ1))) hsmall
  refine ⟨g, by rw [hgeq, piE_eq_natCast], ?_⟩
  refine (𝓣).eq_of_annNorm_sub ?_ ?_
  all_goals
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) ((𝓣).annNorm_nonneg _ _)
    rw [zero_add]
    obtain ⟨J₁, hJ₁⟩ := hg ε hε
    obtain ⟨J₂, hJ₂⟩ := exists_nat_one_div_lt hε
    set J := max J₁ J₂
    have e : (𝓣).toAnn ρ1 (inRad p ρ1) g - Y = ((𝓣).toAnn ρ1 (inRad p ρ1) g - (𝓣).coeAnn (U J)) +
        -(Y - (𝓣).coeAnn (U J)) := by ring
    rw [e]
    refine ((𝓣).annNorm_add_le _ _ _).trans (max_le ?_ ?_)
  · rw [← (𝓣).toAnn_coe, ← map_sub, (𝓣).annNorm_toAnn, annIoc_annIn]
    exact (hJ₁ J (le_max_left _ _)).2
  · rw [(𝓣).annNorm_neg]
    refine (hU J _).le.trans ((one_div_le_one_div_of_le (by positivity) ?_).trans hJ₂.le)
    exact_mod_cast Nat.add_le_add_right (le_max_right J₁ J₂) 1
  · rw [← (𝓣).toAnn_coe, ← map_sub, (𝓣).annNorm_toAnn, annIoc_annOut]
    exact (hJ₁ J (le_max_left _ _)).1
  · rw [(𝓣).annNorm_neg]
    refine (hU J _).le.trans ((one_div_le_one_div_of_le (by positivity) ?_).trans hJ₂.le)
    exact_mod_cast Nat.add_le_add_right (le_max_right J₁ J₂) 1

section Step3

variable (hσ : (p : ℝ)⁻¹ ≤ ((inRad p ρ1 : Set.Ioc (0 : ℝ) ρ1) : ℝ))

include hσ in
theorem inv_p_le_circ : (p : ℝ)⁻¹ ≤ ((topRad (circ p ρ1) : Set.Ioc (0 : ℝ) (circ p ρ1)) : ℝ) := by
  rw [coe_topRad_circ]; rw [coe_inRad] at hσ; exact hσ

set_option maxHeartbeats 1600000 in
theorem frobCirc_bcrisToAnn (x : BCrisPlus ℂ_[p] p) :
    frobCirc p ρ1 (bcrisToAnn hσ x) = bcrisToAnn (inv_p_le_circ ρ1 hσ) (phiPlus ℂ_[p] p x) := by
  have e : (frobCirc p ρ1).comp (bcrisToAnn hσ) = (bcrisToAnn (inv_p_le_circ ρ1 hσ)).comp (phiPlus ℂ_[p] p) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : ACris ℂ_[p] p)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, bcrisToAnn_algebraMap, phiPlus_algebraMap, frobCirc]
      exact annRes_annFrob_acrisToAnn _ _ hσ (inv_p_le_circ ρ1 hσ) a)
  exact congrArg (fun f : BCrisPlus ℂ_[p] p →+* (𝓣).Ann _ _ => f x) e

set_option maxHeartbeats 1600000 in
theorem resCirc_bcrisToAnn (x : BCrisPlus ℂ_[p] p) :
    resCirc p ρ1 (bcrisToAnn hσ x) = bcrisToAnn (inv_p_le_circ ρ1 hσ) x := by
  rw [resCirc, annRes_bcrisToAnn]

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hε hζ in
theorem frobCirc_tTilde :
    frobCirc p ρ1 ((𝓣).toAnn ρ1 (inRad p ρ1) (tTildeExt p ε ρ1)) =
      (p : (𝓣).Ann _ _) * (𝓣).toAnn (circ p ρ1) (topRad (circ p ρ1)) (tTildeExt p ε (circ p ρ1)) := by
  rw [frobCirc_toAnn, extFrob_tTildeExt hε hζ, map_mul, map_natCast]

include hε hζ in
theorem resCirc_tTilde :
    resCirc p ρ1 ((𝓣).toAnn ρ1 (inRad p ρ1) (tTildeExt p ε ρ1)) =
      (𝓣).toAnn (circ p ρ1) (topRad (circ p ρ1)) (tTildeExt p ε (circ p ρ1)) := by
  rw [resCirc_toAnn, res_tTildeExt hε hζ]

set_option maxHeartbeats 1600000 in
include hε hζ in

theorem annNorm_frobCirc_sub_eq_zero {a b : BCrisPlus ℂ_[p] p} (hb : b ≠ 0)
    (hφ : phiPlus ℂ_[p] p a * b = (p : BCrisPlus ℂ_[p] p) * a * phiPlus ℂ_[p] p b) {m : ℕ}
    {Y : (𝓣).Ann ρ1 (inRad p ρ1)}
    (hY : Y * bcrisToAnn hσ b = (𝓣).toAnn ρ1 (inRad p ρ1) (tTildeExt p ε ρ1) ^ m * bcrisToAnn hσ a) :
    (𝓣).annNorm (circ p ρ1) (topRad (circ p ρ1)) (circRad p ρ1)
      (frobCirc p ρ1 Y - (p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) ^ (m + 1) * resCirc p ρ1 Y) = 0 := by
  set hσ' := inv_p_le_circ ρ1 hσ
  set D := frobCirc p ρ1 Y - (p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) ^ (m + 1) * resCirc p ρ1 Y
  set t' := (𝓣).toAnn (circ p ρ1) (topRad (circ p ρ1)) (tTildeExt p ε (circ p ρ1))
  have h1 : frobCirc p ρ1 Y * bcrisToAnn hσ' (phiPlus ℂ_[p] p b) =
      ((p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) * t') ^ m * bcrisToAnn hσ' (phiPlus ℂ_[p] p a) := by
    rw [← frobCirc_bcrisToAnn ρ1 hσ, ← frobCirc_bcrisToAnn ρ1 hσ, ← map_mul, hY, map_mul, map_pow,
      frobCirc_tTilde ρ1 hε hζ]
  have h2 : resCirc p ρ1 Y * bcrisToAnn hσ' b = t' ^ m * bcrisToAnn hσ' a := by
    rw [← resCirc_bcrisToAnn ρ1 hσ, ← resCirc_bcrisToAnn ρ1 hσ, ← map_mul, hY, map_mul, map_pow,
      resCirc_tTilde ρ1 hε hζ]
  have h3 : bcrisToAnn hσ' (phiPlus ℂ_[p] p a) * bcrisToAnn hσ' b =
      (p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) * bcrisToAnn hσ' a * bcrisToAnn hσ' (phiPlus ℂ_[p] p b) := by
    rw [← map_mul, hφ, map_mul, map_mul, map_natCast]
  have key : D * bcrisToAnn hσ' (phiPlus ℂ_[p] p b) * bcrisToAnn hσ' b = 0 := by
    have e : D * bcrisToAnn hσ' (phiPlus ℂ_[p] p b) * bcrisToAnn hσ' b =
        (frobCirc p ρ1 Y * bcrisToAnn hσ' (phiPlus ℂ_[p] p b)) * bcrisToAnn hσ' b -
          (p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) ^ (m + 1) * (resCirc p ρ1 Y * bcrisToAnn hσ' b) *
            bcrisToAnn hσ' (phiPlus ℂ_[p] p b) := by ring
    rw [e, h1, h2]
    linear_combination ((p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) ^ m * t' ^ m) * h3
  have hpos1 : 0 < (𝓣).annNorm (circ p ρ1) (topRad (circ p ρ1)) (circRad p ρ1) (bcrisToAnn hσ' (phiPlus ℂ_[p] p b)) := by
    rw [← frobCirc_bcrisToAnn ρ1 hσ, annNorm_frobCirc]
    exact pow_pos (annNorm_bcrisToAnn_pos hσ hb _) p
  have hpos2 : 0 < (𝓣).annNorm (circ p ρ1) (topRad (circ p ρ1)) (circRad p ρ1) (bcrisToAnn hσ' b) :=
    annNorm_bcrisToAnn_pos hσ' hb _
  have h0 := congrArg ((𝓣).annNorm (circ p ρ1) (topRad (circ p ρ1)) (circRad p ρ1)) key
  rw [(𝓣).annNorm_mul, (𝓣).annNorm_mul, (𝓣).annNorm_zero] at h0
  have hD0 := (𝓣).annNorm_nonneg (circRad p ρ1) D
  by_contra hne
  have hDpos : 0 < (𝓣).annNorm (circ p ρ1) (topRad (circ p ρ1)) (circRad p ρ1) D :=
    lt_of_le_of_ne hD0 (Ne.symm hne)
  have := mul_pos (mul_pos hDpos hpos1) hpos2
  linarith

end Step3

end WAFrac

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔽" => frob ℂ_[p] p

theorem isDomain_bCrisPlus : IsDomain (BCrisPlus ℂ_[p] p) :=
  Function.Injective.isDomain (iotaPlus ℂ_[p] p) (iotaPlus_injective (K := ℂ_[p]))

abbrev radPhi : Set.Ioo (0 : ℝ) 1 := (𝔽).rootRadius (rhoMid p)

theorem inv_p_le_inRad_radPhi : (p : ℝ)⁻¹ ≤ ((inRad p (radPhi (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) := by
  have e : ((inRad p (radPhi (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) = rhoMid p :=
    congrArg Subtype.val ((𝔽).powRadius_rootRadius (rhoMid p))
  rw [e]; exact inv_p_lt_rhoMid.le

theorem phiPlus_injective : Function.Injective (phiPlus ℂ_[p] p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  have hσ := inv_p_le_inRad_radPhi (p := p)
  have h1 := annNorm_bcrisToAnn_pos hσ hx0 (annOut _ _)
  have h2 := annNorm_frobCirc (radPhi (p := p)) (bcrisToAnn hσ x)
  rw [frobCirc_bcrisToAnn _ hσ, hx, map_zero, (𝓣).annNorm_zero] at h2
  have := pow_pos h1 p
  linarith

section Points

variable {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0}

theorem annMap_ξAnn {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : Gal(PadicAlgCl p/K)) (P : (𝓣).Pt) :
    (galIso σ).annMap ((𝓣).ξAnn (ρ0 := ρ0) (σ0 := σ0) P.1) = (𝓣).ξAnn (galPt σ P).1 := by
  rw [TeichLift.ξAnn, TeichLift.TeichIso.annMap_coeAnn, TeichLift.ξAnn]
  congr 1
  apply Subtype.ext
  show (galIso σ).toB (algebraMap (WC p) (𝓣).B P.1) = algebraMap (WC p) (𝓣).B ((galIso σ).ψ P.1)
  rw [TeichLift.TeichIso.toB_algebraMap]

theorem annRes_ξAnn {ρ1 : Set.Ioo (0 : ℝ) 1} {σ1 : Set.Ioc (0 : ℝ) ρ1} (h : (ρ1 : ℝ) ≤ ρ0)
    (hs : (σ0 : ℝ) ≤ σ1) (ξ : (𝓣).int) :
    (𝓣).annRes h hs ((𝓣).ξAnn (ρ0 := ρ0) (σ0 := σ0) ξ) = (𝓣).ξAnn ξ := by
  rw [TeichLift.ξAnn, (𝓣).annRes_coeAnn]; rfl

theorem isUnit_of_eq_mul_of_ptRad_eq {P Q : (𝓣).Pt} {B : (𝓣).int} (h : P.1 = Q.1 * B)
    (hr : (𝓣).ptRad P.1 = (𝓣).ptRad Q.1) : IsUnit B := by
  rw [(𝓣).isUnit_int_iff]
  have h0 : (𝓣).red (P.1 : WC p) = (𝓣).red (Q.1 : WC p) * (𝓣).red (B : WC p) := by
    rw [h, Subring.coe_mul, map_mul]
  have hP : ‖(𝓣).red (P.1 : WC p)‖ = (𝓣).ptRad P.1 := by rw [← coeff_zero]; rfl
  have hQ : ‖(𝓣).red (Q.1 : WC p)‖ = (𝓣).ptRad Q.1 := by rw [← coeff_zero]; rfl
  have hQ0 : 0 < (𝓣).ptRad Q.1 := (𝓣).ptRad_pos' Q.2
  have := congrArg norm h0
  rw [norm_mul, hP, hQ, hr] at this
  have h1 : (𝓣).ptRad Q.1 * 1 = (𝓣).ptRad Q.1 * ‖(𝓣).red (B : WC p)‖ := by rw [mul_one]; exact this
  exact (mul_left_cancel₀ hQ0.ne' h1).symm

theorem annEval_ξAnn_ne_zero {P Q : (𝓣).Pt} (hQ : (𝓣).ptRad Q.1 ∈ Set.Icc (σ0 : ℝ) ρ0)
    (hr : (𝓣).ptRad P.1 = (𝓣).ptRad Q.1) (hPQ : ¬ ∃ u : (𝓣).int, IsUnit u ∧ P.1 = u * Q.1) :
    (𝓣).annEval Q.2 hQ ((𝓣).ξAnn (ρ0 := ρ0) (σ0 := σ0) P.1) ≠ 0 := by
  intro h0
  rw [ξAnn_eq_toAnn, annEval_toAnn, (𝓣).ptEval_ξExt_eq Q hQ.2, (𝓣).toUntiltField_eq_zero_iff] at h0
  obtain ⟨B, hB, hPB⟩ := ((𝓣).toUntilt_eq_zero_iff (ξ := Q.1)).1 h0
  have hPB' : P.1 = Q.1 * ⟨B, hB⟩ := Subtype.ext hPB
  exact hPQ ⟨⟨B, hB⟩, isUnit_of_eq_mul_of_ptRad_eq hPB' hr, by rw [hPB', mul_comm]⟩

end Points

end WAFrac

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

namespace WAFrac

theorem galois_mem_den {R : Type*} [CommRing R] [IsDomain R] (g : R →+* R) {a b β γ T : R}
    (hgb : g b ≠ 0) (hrel : g a * b - a * g b = T * g b * b) (h : β * a = γ * b) :
    g β * a = (g γ - T * g β) * b := by
  have hg := congrArg g h
  rw [map_mul, map_mul] at hg
  refine mul_right_cancel₀ hgb ?_
  linear_combination b * hg - g β * hrel

theorem galois_sub_of_mul_eq {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S)
    (gR : R →+* R) (gS : S →+* S) (hfg : ∀ x, gS (f x) = f (gR x)) {a b T : R} {u : S}
    (hb : f b ≠ 0) (hgb : gS (f b) ≠ 0) (hrel : gR a * b - a * gR b = T * gR b * b) (hu : u * f b = f a) :
    gS u - u = f T := by
  have h1 : gS u * gS (f b) = f (gR a) := by rw [← map_mul, hu, hfg]
  have h2 := congrArg f hrel
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, ← hfg, ← hfg] at h2
  refine mul_right_cancel₀ hb (mul_right_cancel₀ hgb ?_)
  linear_combination f b * h1 - gS (f b) * hu + h2 - f b * hfg a

end WAFrac

end GroundTheory.PAdicHodge
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WABridge WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔽" => frob ℂ_[p] p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)
  {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

include hε hζ in
theorem periodTPlus_ne_zero : periodTPlus hε ≠ 0 := fun h =>
  iotaPlus_periodTPlus_ne_zero hε hζ (by rw [h, map_zero])

include hε hζ in
theorem algebraMap_bCris_injective :
    Function.Injective (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) := by
  have := isDomain_bCrisPlus (p := p)
  exact IsLocalization.injective (M := Submonoid.powers (periodTPlus hε)) (BCris hε)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (periodTPlus_ne_zero hε hζ))

theorem galB_injective (σ : Gal(PadicAlgCl p/K)) : Function.Injective (galB hε σ) := by
  let := galBAction (K := K) hε
  exact MulAction.injective (α := Gal(PadicAlgCl p/K)) (β := BCris hε) σ

theorem exists_sub_eq_of_mul_eq {G R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    {t : R} [IsLocalization.Away t S] (hinj : Function.Injective (algebraMap R S))
    (gR : G → R →+* R) (gS : G → S →+* S) (hfg : ∀ σ x, gS σ (algebraMap R S x) = algebraMap R S (gR σ x))
    (hgS : ∀ σ, Function.Injective (gS σ)) {a b β : R} (hb : b ≠ 0) {m : ℕ} (hβ : β * b = t ^ m * a)
    (T : G → R) (hrel : ∀ σ, gR σ a * b - a * gR σ b = T σ * gR σ b * b) :
    ∃ u : S, ∀ σ, gS σ u - u = algebraMap R S (T σ) := by
  set f := algebraMap R S
  set v := IsLocalization.Away.invSelf t (S := S)
  have hvt : f t * v = 1 := IsLocalization.Away.mul_invSelf t
  refine ⟨f β * v ^ m, fun σ => ?_⟩
  have hu : f β * v ^ m * f b = f a := by
    have e : f β * v ^ m * f b = f (β * b) * v ^ m := by rw [map_mul]; ring
    rw [e, hβ, map_mul, map_pow]
    calc f t ^ m * f a * v ^ m = (f t * v) ^ m * f a := by ring
      _ = f a := by rw [hvt, one_pow, one_mul]
  have hfb : f b ≠ 0 := fun h0 => hb (hinj (by rw [h0, map_zero]))
  exact galois_sub_of_mul_eq f (gR σ) (gS σ) (hfg σ) hfb
    (fun h0 => hfb (hgS σ (by rw [h0, map_zero]))) (hrel σ) hu

set_option maxHeartbeats 1600000 in
theorem algebraMap_padic_mul_periodTPlus (q : ℚ_[p]) :
    algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * periodTPlus hε) =
      algebraMap ℚ_[p] (BCris hε) q * periodTCris hε := by
  rw [map_mul]; rfl

set_option maxHeartbeats 3200000 in
include hε hζ in

theorem exists_bCris_of_mul_eq {a b β : BCrisPlus ℂ_[p] p} (hb : b ≠ 0) {m : ℕ}
    (hβ : β * b = periodTPlus hε ^ m * a) (c : Gal(PadicAlgCl p/K) → ℚ_[p])
    (hrel : ∀ σ : Gal(PadicAlgCl p/K), σ • a * b - a * σ • b =
      algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (c σ) * periodTPlus hε * σ • b * b) :
    ∃ u : BCris hε, ∀ σ : Gal(PadicAlgCl p/K),
      galB hε σ u - u = algebraMap ℚ_[p] (BCris hε) (c σ) * periodTCris hε := by
  have := isDomain_bCris hε hζ
  obtain ⟨u, hu⟩ := exists_sub_eq_of_mul_eq (S := BCris hε) (t := periodTPlus hε)
    (algebraMap_bCris_injective hε hζ) (fun σ : Gal(PadicAlgCl p/K) => galPlus σ) (fun σ => galB hε σ)
    (fun σ x => galB_algebraMap hε σ x) (fun σ => galB_injective hε σ) hb hβ
    (fun σ => algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (c σ) * periodTPlus hε) hrel
  exact ⟨u, fun σ => (hu σ).trans (algebraMap_padic_mul_periodTPlus hε (c σ))⟩

variable (ρ1 : Set.Ioo (0 : ℝ) 1) (hσ : (p : ℝ)⁻¹ ≤ ((inRad p ρ1 : Set.Ioc (0 : ℝ) ρ1) : ℝ))
  (h1 : (ρ1 : ℝ) ≤ radTwo p)

set_option maxHeartbeats 3200000 in
include hε hζ h1 in

theorem false_of_mul_eq_tTilde_pow [FiniteDimensional ℚ_[p] K] {a b : BCrisPlus ℂ_[p] p} (hb : b ≠ 0)
    (hφ : phiPlus ℂ_[p] p a * b = (p : BCrisPlus ℂ_[p] p) * a * phiPlus ℂ_[p] p b)
    (hrel : ∀ σ : Gal(PadicAlgCl p/K), σ • a * b - a * σ • b =
      algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (kummerC hε hζ σ : ℚ_[p]) * periodTPlus hε * σ • b * b)
    {m : ℕ} {Y : (𝓣).Ann ρ1 (inRad p ρ1)}
    (hY : Y * bcrisToAnn hσ b = (𝓣).toAnn ρ1 (inRad p ρ1) (tTildeExt p ε ρ1) ^ m * bcrisToAnn hσ a) :
    False := by
  have := isDomain_bCrisPlus (p := p)

  have h3 := annNorm_frobCirc_sub_eq_zero ρ1 hσ hε hζ hb hφ hY

  obtain ⟨g, hg, hgY⟩ := exists_eigen_of_ann ρ1 (m + 1) Y h3
  have hY' : (𝔽).tildeFrob ((𝓣).ofRad ρ1 g) = (p : (𝓣).RobbaTilde) ^ (m + 1) * (𝓣).ofRad ρ1 g := by
    rw [TeichLift.TeichFrob.tildeFrob_ofRad, hg, map_mul, map_pow, map_natCast, (𝓣).ofRad_res]

  obtain ⟨-, β, -, -, hann⟩ := exists_bCrisPlus_ann m _ hY'
  have hβ : bcrisToAnn hσ β = Y := by
    rw [hann ρ1 (inRad p ρ1) hσ h1 ρ1 le_rfl g rfl, (𝓣).res_self, hgY]
  have ht := bcrisToAnn_periodTPlus hε hζ hσ h1 (le_refl (ρ1 : ℝ)) (tTildeExt p ε ρ1)
    (ofRad_tTildeExt hε hζ ρ1)
  rw [(𝓣).res_self] at ht
  have hβb : β * b = periodTPlus hε ^ m * a := by
    apply bcrisToAnn_injective hσ
    rw [map_mul, map_mul, map_pow, hβ, hY, ht]
  obtain ⟨u, hu⟩ := exists_bCris_of_mul_eq hε hζ hb hβb _ hrel
  exact not_forall_galB_sub_eq_kummerC hε hζ u hu

end WAFrac

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WABridge WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔽" => frob ℂ_[p] p

theorem list_prod_dvd_of_pairwise {α A : Type*} [CommRing A] (f : α → A) {w : A} :
    ∀ l : List α, (∀ x ∈ l, f x ∣ w) → l.Pairwise (fun x y => IsCoprime (f x) (f y)) →
      (l.map f).prod ∣ w
  | [], _, _ => by simp
  | x :: l, hd, hp' => by
    rw [List.pairwise_cons] at hp'
    rw [List.map_cons, List.prod_cons]
    have hc : IsCoprime (f x) (l.map f).prod := by
      clear hd
      induction l with
      | nil => simp [isCoprime_one_right]
      | cons y l ih =>
        rw [List.map_cons, List.prod_cons]
        exact (hp'.1 y List.mem_cons_self).mul_right
          (ih ⟨fun z hz => hp'.1 z (List.mem_cons_of_mem _ hz), (List.pairwise_cons.1 hp'.2).2⟩)
    exact hc.mul_dvd (hd x List.mem_cons_self)
      (list_prod_dvd_of_pairwise f l (fun y hy => hd y (List.mem_cons_of_mem _ hy)) hp'.2)

abbrev radBig : Set.Ioo (0 : ℝ) 1 := radTwo p

def radSmall : Set.Ioc (0 : ℝ) (radBig (p := p)) :=
  ⟨(p : ℝ)⁻¹, inv_pos.2 (Nat.cast_pos.2 hp.out.pos), inv_p_lt_radTwo.le⟩

theorem coe_radSmall : ((radSmall (p := p) : Set.Ioc (0 : ℝ) _) : ℝ) = (p : ℝ)⁻¹ := rfl

def radMid : Set.Ioo (0 : ℝ) 1 :=
  ⟨((p : ℝ)⁻¹ + rhoMid p) / 2, by have := WAEval.inv_p_pos (p := p); have := (rhoMid p).2.1; positivity,
    by have := (rhoMid p).2.2; have := inv_p_lt_rhoMid (p := p); linarith⟩

theorem inv_p_lt_radMid : (p : ℝ)⁻¹ < radMid (p := p) := by
  show (p : ℝ)⁻¹ < ((p : ℝ)⁻¹ + rhoMid p) / 2; have := inv_p_lt_rhoMid (p := p); linarith

theorem radMid_lt_rhoMid : (radMid (p := p) : ℝ) < rhoMid p := by
  show ((p : ℝ)⁻¹ + rhoMid p) / 2 < rhoMid p; have := inv_p_lt_rhoMid (p := p); linarith

abbrev radRho : Set.Ioo (0 : ℝ) 1 := (𝔽).rootRadius (radMid (p := p))

theorem coe_inRad_radRho : ((inRad p (radRho (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) = radMid (p := p) :=
  congrArg Subtype.val ((𝔽).powRadius_rootRadius (radMid (p := p)))

theorem inv_p_le_inRad : (p : ℝ)⁻¹ ≤ ((inRad p (radRho (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) := by
  rw [coe_inRad_radRho]; exact inv_p_lt_radMid.le

theorem radSmall_lt_inRad :
    ((radSmall (p := p) : Set.Ioc (0 : ℝ) _) : ℝ) < ((inRad p (radRho (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) := by
  rw [coe_inRad_radRho, coe_radSmall]; exact inv_p_lt_radMid

theorem radRho_lt_radBig : ((radRho (p := p) : Set.Ioo (0 : ℝ) 1) : ℝ) < (radBig (p := p) : ℝ) := by
  show (((𝔽).rootRadius (radMid (p := p)) : Set.Ioo (0 : ℝ) 1) : ℝ) < (((𝔽).rootRadius (rhoMid p) :
    Set.Ioo (0 : ℝ) 1) : ℝ)
  rw [rootRadius_coe, rootRadius_coe]
  exact Real.rpow_lt_rpow (radMid (p := p)).2.1.le radMid_lt_rhoMid
    (inv_pos.2 (Nat.cast_pos.2 hp.out.pos))

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

def ptStab (ξ : (𝓣).int) : Subgroup Gal(PadicAlgCl p/K) where
  carrier := {σ | ∃ u : (𝓣).int, IsUnit u ∧ ((galIso σ).ψ ξ : WC p) = u * ξ}
  one_mem' := ⟨1, isUnit_one, by rw [galIso_one]; simp⟩
  mul_mem' := by
    rintro σ τ ⟨u, hu, hσ⟩ ⟨v, hv, hτ⟩
    refine ⟨⟨(galIso σ).ψ v, galIso_mem_int σ v.2⟩ * u, ?_, ?_⟩
    · refine IsUnit.mul ?_ hu
      obtain ⟨w, hw⟩ := hv.exists_right_inv
      refine isUnit_iff_exists_inv.2 ⟨⟨(galIso σ).ψ w, galIso_mem_int σ w.2⟩, Subtype.ext ?_⟩
      have := congrArg (fun x : (𝓣).int => (galIso σ).ψ (x : WC p)) hw
      simp only [Subring.coe_mul, map_mul, Subring.coe_one, map_one] at this
      simpa using this
    · show (galIso (σ * τ)).ψ (ξ : WC p) = _
      rw [galIso_mul, TeichLift.TeichIso.comp_ψ, hτ, map_mul, hσ]
      simp only [Subring.coe_mul]; ring
  inv_mem' := by
    rintro σ ⟨u, hu, hσ⟩
    have h1 := congrArg (galIso σ⁻¹).ψ hσ
    rw [← TeichLift.TeichIso.comp_ψ, ← galIso_mul, inv_mul_cancel, galIso_one, map_mul] at h1
    simp only [TeichLift.TeichIso.refl_ψ] at h1
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    refine ⟨⟨(galIso σ⁻¹).ψ w, galIso_mem_int σ⁻¹ w.2⟩, ?_, ?_⟩
    · refine isUnit_iff_exists_inv.2 ⟨⟨(galIso σ⁻¹).ψ u, galIso_mem_int σ⁻¹ u.2⟩, Subtype.ext ?_⟩
      have := congrArg (fun x : (𝓣).int => (galIso σ⁻¹).ψ (x : WC p)) (show w * u = 1 by rw [mul_comm]; exact hw)
      simp only [Subring.coe_mul, map_mul, Subring.coe_one, map_one] at this
      simpa using this
    · have hwu : ((galIso σ⁻¹).ψ w : WC p) * (galIso σ⁻¹).ψ u = 1 := by
        rw [← map_mul]
        have := congrArg (fun x : (𝓣).int => (x : WC p)) (show w * u = 1 by rw [mul_comm]; exact hw)
        simp only [Subring.coe_mul, Subring.coe_one] at this
        rw [this, map_one]
      show ((galIso σ⁻¹).ψ ξ : WC p) = (galIso σ⁻¹).ψ w * ξ
      calc ((galIso σ⁻¹).ψ ξ : WC p) = (galIso σ⁻¹).ψ w * ((galIso σ⁻¹).ψ u * (galIso σ⁻¹).ψ ξ) := by
            rw [← mul_assoc, hwu, one_mul]
        _ = (galIso σ⁻¹).ψ w * ξ := by rw [← h1]

section Main

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

theorem hσSmall : (p : ℝ)⁻¹ ≤ ((radSmall (p := p) : Set.Ioc (0 : ℝ) _) : ℝ) := le_of_eq rfl

def denSet (a b : BCrisPlus ℂ_[p] p) : Set (BCrisPlus ℂ_[p] p) := {β | ∃ γ, β * a = γ * b}

def IsDenPt (a b : BCrisPlus ℂ_[p] p) (P : (𝓣).Pt) : Prop :=
  ∀ β ∈ denSet a b, (𝓣).ξAnn (ρ0 := radBig (p := p)) (σ0 := radSmall) P.1 ∣ bcrisToAnn hσSmall β

variable {a b : BCrisPlus ℂ_[p] p}
  (hrel : ∀ σ : Gal(PadicAlgCl p/K), σ • a * b - a * σ • b =
    algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (kummerC hε hζ σ : ℚ_[p]) * periodTPlus hε * σ • b * b)

include hrel in
theorem smul_mem_denSet (hb : b ≠ 0) (σ : Gal(PadicAlgCl p/K)) {β : BCrisPlus ℂ_[p] p}
    (hβ : β ∈ denSet a b) : σ • β ∈ denSet a b := by
  have := isDomain_bCrisPlus (p := p)
  obtain ⟨γ, hγ⟩ := hβ
  have hσb : σ • b ≠ 0 := fun h => hb (MulAction.injective σ (show σ • b = σ • (0 : BCrisPlus ℂ_[p] p) by
    rw [h, smul_zero]))
  exact ⟨_, galois_mem_den (MulSemiringAction.toRingHom _ _ σ) hσb (hrel σ) hγ⟩

include hrel in
theorem isDenPt_galPt (hb : b ≠ 0) {P : (𝓣).Pt} (hP : IsDenPt a b P) (σ : Gal(PadicAlgCl p/K)) :
    IsDenPt a b (galPt σ P) := by
  intro β hβ
  have h1 := hP _ (smul_mem_denSet hε hζ hrel hb σ⁻¹ hβ)
  have h2 := map_dvd (galIso σ).annMap h1
  rw [annMap_ξAnn, annMap_bcrisToAnn] at h2
  have e : galPlus σ (σ⁻¹ • β) = β := smul_inv_smul σ β
  rwa [e] at h2

theorem ptRadBig (P : (𝓣).Pt) (hr : (p : ℝ)⁻¹ < (𝓣).ptRad P.1 ∧ (𝓣).ptRad P.1 < radTwo p) :
    (𝓣).ptRad P.1 ∈ Set.Icc ((radSmall (p := p) : Set.Ioc (0 : ℝ) _) : ℝ) (radBig (p := p)) :=
  ⟨hr.1.le, hr.2.le⟩

set_option maxHeartbeats 3200000 in
include hrel in

theorem finiteIndex_ptStab (hb : b ≠ 0) {P : (𝓣).Pt} (hP : IsDenPt a b P)
    (hr : (p : ℝ)⁻¹ < (𝓣).ptRad P.1 ∧ (𝓣).ptRad P.1 < radTwo p) :
    (ptStab (K := K) P.1).FiniteIndex := by
  have := isDomain_bCrisPlus (p := p)
  set w := bcrisToAnn (ρ0 := radBig (p := p)) hσSmall b with hwdef
  have hw : ∀ r, 0 < (𝓣).annNorm _ _ r w := annNorm_bcrisToAnn_pos hσSmall hb
  set rr : AnnRad (radBig (p := p)) radSmall := ⟨(𝓣).ptRad P.1, ptRadBig P hr⟩
  have hab : ((annIn (radBig (p := p)) radSmall : AnnRad _ _) : ℝ) < rr := hr.1
  have hcd : (rr : ℝ) < (annOut (radBig (p := p)) radSmall : AnnRad _ _) := hr.2

  have hbI : b ∈ denSet a b := ⟨a, mul_comm b a⟩
  have key : ∀ (n : ℕ) (g : Fin n → Gal(PadicAlgCl p/K)),
      (∀ i j, i ≠ j → (g j)⁻¹ * g i ∉ ptStab (K := K) P.1) →
      ((List.finRange n).map fun i => galPt (g i) P).length ≤ ((List.finRange n).map fun i => galPt (g i) P).length
        ∧ (((List.finRange n).map fun i => galPt (g i) P).length : ℝ) ≤
        (Real.log ((𝓣).annNorm _ _ (annOut _ _) w) - Real.log ((𝓣).annNorm _ _ rr w)) /
          (Real.log (annOut (radBig (p := p)) radSmall : AnnRad _ _) - Real.log rr) -
        (Real.log ((𝓣).annNorm _ _ rr w) - Real.log ((𝓣).annNorm _ _ (annIn _ _) w)) /
          (Real.log rr - Real.log (annIn (radBig (p := p)) radSmall : AnnRad _ _)) := by
    intro n g hg
    refine ⟨le_rfl, (𝓣).length_le_of_prod_dvd w hw _ rr rr _ hab le_rfl hcd _ ?_ ?_⟩
    · intro Q hQ
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hQ
      rw [ptRad_galPt]; exact ⟨le_rfl, le_rfl⟩
    · rw [List.map_map]
      refine list_prod_dvd_of_pairwise _ _ (fun i _ => isDenPt_galPt hε hζ hrel hb hP (g i) b hbI) ?_
      refine (List.nodup_finRange n).pairwise_of_forall_ne fun i _ j _ hij => ?_
      set Qi := galPt (g i) P
      set Qj := galPt (g j) P
      have hri : (𝓣).ptRad Qi.1 ∈ Set.Icc ((radSmall (p := p) : Set.Ioc (0 : ℝ) _) : ℝ) (radBig (p := p)) := by
        rw [ptRad_galPt]; exact ptRadBig P hr
      have hne : (𝓣).annEval Qi.2 hri ((𝓣).ξAnn (ρ0 := radBig (p := p)) (σ0 := radSmall) Qj.1) ≠ 0 := by
        refine annEval_ξAnn_ne_zero hri (by rw [ptRad_galPt, ptRad_galPt]) ?_
        rintro ⟨u, hu, hQ⟩
        refine hg j i (Ne.symm hij) ⟨⟨(galIso (g i)⁻¹).ψ u, galIso_mem_int _ u.2⟩, ?_, ?_⟩
        · obtain ⟨w', hw'⟩ := hu.exists_right_inv
          refine isUnit_iff_exists_inv.2 ⟨⟨(galIso (g i)⁻¹).ψ w', galIso_mem_int _ w'.2⟩, Subtype.ext ?_⟩
          have := congrArg (fun x : (𝓣).int => (galIso (g i)⁻¹).ψ (x : WC p)) hw'
          simp only [Subring.coe_mul, map_mul, Subring.coe_one, map_one] at this
          simpa using this
        · have h1 := congrArg (fun x : (𝓣).int => (galIso (g i)⁻¹).ψ (x : WC p)) hQ
          simp only [Subring.coe_mul, map_mul] at h1
          show (galIso ((g i)⁻¹ * g j)).ψ (P.1 : WC p) = _
          rw [galIso_mul, TeichLift.TeichIso.comp_ψ]
          have e1 : (galIso (g i)⁻¹).ψ ((galIso (g i)).ψ (P.1 : WC p)) = P.1 := by
            rw [← TeichLift.TeichIso.comp_ψ, ← galIso_mul, inv_mul_cancel, galIso_one]; rfl
          change (galIso (g i)⁻¹).ψ ((galIso (g j)).ψ (P.1 : WC p)) =
            (galIso (g i)⁻¹).ψ (u : WC p) * (galIso (g i)⁻¹).ψ ((galIso (g i)).ψ (P.1 : WC p)) at h1
          rw [h1, e1]
      obtain ⟨α, β, hαβ⟩ := (𝓣).exists_bezout_ann Qi.2 hri hne
      exact ⟨α, β, hαβ⟩

  have hfin : Finite (Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1) := by
    by_contra hinf
    have : Infinite (Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1) := not_finite_iff_infinite.1 hinf
    set e := Infinite.natEmbedding (Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1)
    set Bd := (Real.log ((𝓣).annNorm _ _ (annOut _ _) w) - Real.log ((𝓣).annNorm _ _ rr w)) /
          (Real.log (annOut (radBig (p := p)) radSmall : AnnRad _ _) - Real.log rr) -
        (Real.log ((𝓣).annNorm _ _ rr w) - Real.log ((𝓣).annNorm _ _ (annIn _ _) w)) /
          (Real.log rr - Real.log (annIn (radBig (p := p)) radSmall : AnnRad _ _))
    set n := ⌈Bd⌉₊ + 1
    set g : Fin n → Gal(PadicAlgCl p/K) := fun i => Quotient.out (e i)
    have hg : ∀ i j, i ≠ j → (g j)⁻¹ * g i ∉ ptStab (K := K) P.1 := by
      intro i j hij hmem
      have h1 : (QuotientGroup.mk (g j) : Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1) = QuotientGroup.mk (g i) :=
        QuotientGroup.eq.2 hmem
      have h2 : e j = e i := by
        have hj : (QuotientGroup.mk (g j) : Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1) = e j :=
          Quotient.out_eq (e j)
        have hi : (QuotientGroup.mk (g i) : Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1) = e i :=
          Quotient.out_eq (e i)
        rw [← hj, ← hi, h1]
      exact hij (Fin.ext (e.injective h2).symm)
    have hk := (key n g hg).2
    rw [List.length_map, List.length_finRange] at hk
    have : (n : ℝ) > Bd := by
      have := Nat.le_ceil Bd
      push_cast [n]; linarith
    linarith
  exact Subgroup.finiteIndex_of_finite_quotient

set_option maxHeartbeats 3200000 in
include hrel in

theorem dvd_tTilde_of_isDenPt [FiniteDimensional ℚ_[p] K] (hb : b ≠ 0) {P : (𝓣).Pt}
    (hP : IsDenPt a b P) (hr : (p : ℝ)⁻¹ < (𝓣).ptRad P.1 ∧ (𝓣).ptRad P.1 < radTwo p) :
    (𝓣).ξAnn (ρ0 := radBig (p := p)) (σ0 := radSmall) P.1 ∣
      (𝓣).toAnn (radBig (p := p)) radSmall (tTildeExt p ε (radBig (p := p))) := by
  have := finiteIndex_ptStab hε hζ hrel hb hP hr
  have h0 := ptEval_tTilde_eq_zero_of_fixed hε hζ (ptStab (K := K) P.1) P.2 hr.1.le hr.2.le
    (fun σ hσ => hσ) (radBig (p := p)) hr.2 (tTildeExt p ε _) (ofRad_tTildeExt hε hζ _)
  rw [← (𝓣).annEval_toAnn P.2 (ptRadBig P hr)] at h0
  obtain ⟨y, hy⟩ := ((𝓣).annEval_eq_zero_iff P.2 (ptRadBig P hr) _).1 h0
  exact ⟨y, hy⟩

abbrev AnnS := (𝓣).Ann (radRho (p := p)) (inRad p (radRho (p := p)))

def resS : (𝓣).Ann (radBig (p := p)) radSmall →+* AnnS (p := p) :=
  (𝓣).annRes radRho_lt_radBig.le radSmall_lt_inRad.le

omit hε hζ in

def denIdealS (a b : BCrisPlus ℂ_[p] p) : Ideal (AnnS (p := p)) :=
  Ideal.span ((fun β => resS (bcrisToAnn hσSmall β)) '' denSet a b)

include hε hζ in
theorem resS_tTilde :
    resS ((𝓣).toAnn (radBig (p := p)) radSmall (tTildeExt p ε (radBig (p := p)))) =
      (𝓣).toAnn (radRho (p := p)) (inRad p (radRho (p := p))) (tTildeExt p ε (radRho (p := p))) := by
  rw [resS, (𝓣).annRes_toAnn, res_tTildeExt hε hζ]

theorem ptRad_bounds {P : (𝓣).Pt}
    (h : ((inRad p (radRho (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) ≤ (𝓣).ptRad P.1 ∧
      (𝓣).ptRad P.1 ≤ (radRho (p := p) : ℝ)) :
    (p : ℝ)⁻¹ < (𝓣).ptRad P.1 ∧ (𝓣).ptRad P.1 < radTwo p :=
  ⟨(show (p : ℝ)⁻¹ < _ from (coe_radSmall (p := p)) ▸ radSmall_lt_inRad).trans_le h.1,
    h.2.trans_lt radRho_lt_radBig⟩

set_option maxHeartbeats 3200000 in
include hrel in

theorem exists_pow_mem_span [FiniteDimensional ℚ_[p] K] (hb : b ≠ 0) :
    ∀ l : List (𝓣).Pt, (∀ P ∈ l, ((inRad p (radRho (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) ≤ (𝓣).ptRad P.1 ∧
      (𝓣).ptRad P.1 ≤ (radRho (p := p) : ℝ)) →
      ∃ (m : ℕ) (c : AnnS (p := p)),
        (𝓣).toAnn (radRho (p := p)) (inRad p (radRho (p := p))) (tTildeExt p ε (radRho (p := p))) ^ m -
          c * (l.map fun P => (𝓣).ξAnn P.1).prod ∈ denIdealS a b
  | [], _ => ⟨0, 1, by simp⟩
  | P :: l, hl => by
    obtain ⟨m, c, hmc⟩ := exists_pow_mem_span hb l fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)
    have hrP := ptRad_bounds (hl P List.mem_cons_self)
    set t' := (𝓣).toAnn (radRho (p := p)) (inRad p (radRho (p := p))) (tTildeExt p ε (radRho (p := p)))
    rw [List.map_cons, List.prod_cons]
    by_cases hS : IsDenPt a b P
    · obtain ⟨d, hd⟩ := dvd_tTilde_of_isDenPt hε hζ hrel hb hS hrP
      have hd' := congrArg resS hd
      rw [resS_tTilde hε hζ, map_mul, resS, annRes_ξAnn] at hd'
      refine ⟨m + 1, resS d * c, ?_⟩
      have e : t' ^ (m + 1) - resS d * c * ((𝓣).ξAnn P.1 * (l.map fun P => (𝓣).ξAnn P.1).prod) =
          t' * (t' ^ m - c * (l.map fun P => (𝓣).ξAnn P.1).prod) := by
        have hd'' : t' = (𝓣).ξAnn P.1 * resS d := hd'
        rw [hd'']; ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hmc
    · simp only [IsDenPt, not_forall] at hS
      obtain ⟨β, hβ, hnd⟩ := hS
      have hne : (𝓣).annEval P.2 (ptRadBig P hrP) (bcrisToAnn hσSmall β) ≠ 0 := fun h0 =>
        hnd (by obtain ⟨y, hy⟩ := ((𝓣).annEval_eq_zero_iff P.2 (ptRadBig P hrP) _).1 h0; exact ⟨y, hy⟩)
      obtain ⟨α, α', hαα'⟩ := (𝓣).exists_bezout_ann P.2 (ptRadBig P hrP) hne
      have h1 := congrArg resS hαα'
      rw [map_add, map_mul, map_mul, map_one, resS, annRes_ξAnn] at h1
      refine ⟨m, resS α * c, ?_⟩
      have e : t' ^ m - resS α * c * ((𝓣).ξAnn P.1 * (l.map fun P => (𝓣).ξAnn P.1).prod) =
          (t' ^ m - c * (l.map fun P => (𝓣).ξAnn P.1).prod) +
            (c * (l.map fun P => (𝓣).ξAnn P.1).prod * resS α') * resS (bcrisToAnn hσSmall β) := by
        rw [resS]; linear_combination (-(c * (l.map fun P => (𝓣).ξAnn P.1).prod)) * h1
      rw [e]
      exact add_mem hmc (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨β, hβ, rfl⟩))

set_option maxHeartbeats 3200000 in
include hrel in

theorem false_of_frac [FiniteDimensional ℚ_[p] K] (hb : b ≠ 0)
    (hφ : phiPlus ℂ_[p] p a * b = (p : BCrisPlus ℂ_[p] p) * a * phiPlus ℂ_[p] p b) : False := by
  have := isDomain_bCrisPlus (p := p)
  set w := bcrisToAnn (ρ0 := radBig (p := p)) hσSmall b with hwdef
  have hw : ∀ r, 0 < (𝓣).annNorm _ _ r w := annNorm_bcrisToAnn_pos hσSmall hb
  obtain ⟨l, u, hl, hu, hfac⟩ := (𝓣).exists_factor_ann w hw (ρ1 := radRho (p := p))
    (σ1 := inRad p (radRho (p := p))) radRho_lt_radBig radSmall_lt_inRad
  obtain ⟨m, c, hmc⟩ := exists_pow_mem_span hε hζ hrel hb l hl
  set J := denIdealS (p := p) a b
  have hbI : b ∈ denSet a b := ⟨a, mul_comm b a⟩
  have hwJ : resS w ∈ J := Ideal.subset_span ⟨b, hbI, rfl⟩
  have hprod : (l.map fun P => (𝓣).ξAnn P.1).prod ∈ J := by
    have e : (l.map fun P => (𝓣).ξAnn P.1).prod = resS w * ((hu.unit⁻¹ : (AnnS (p := p))ˣ) : AnnS (p := p)) := by
      rw [resS, hfac, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [e]; exact Ideal.mul_mem_right _ _ hwJ
  set t' := (𝓣).toAnn (radRho (p := p)) (inRad p (radRho (p := p))) (tTildeExt p ε (radRho (p := p)))
  have htJ : t' ^ m ∈ J := by
    have := add_mem hmc (Ideal.mul_mem_left J c hprod)
    rwa [sub_add_cancel] at this
  have hY : ∃ Y, Y * resS (bcrisToAnn hσSmall b) = t' ^ m * resS (bcrisToAnn hσSmall a) := by
    refine Submodule.span_induction (p := fun x _ => ∃ Y, Y * resS (bcrisToAnn hσSmall b) =
      x * resS (bcrisToAnn hσSmall a)) ?_ ?_ ?_ ?_ htJ
    · rintro x ⟨β, ⟨γ, hγ⟩, rfl⟩
      exact ⟨resS (bcrisToAnn hσSmall γ), by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hγ]⟩
    · exact ⟨0, by rw [zero_mul, zero_mul]⟩
    · rintro x y - - ⟨Y₁, h₁⟩ ⟨Y₂, h₂⟩
      exact ⟨Y₁ + Y₂, by rw [add_mul, h₁, h₂, add_mul]⟩
    · rintro c' x - ⟨Y, h⟩
      exact ⟨c' * Y, by rw [mul_assoc, h, smul_eq_mul, mul_assoc]⟩
  obtain ⟨Y, hY⟩ := hY
  rw [resS, annRes_bcrisToAnn, annRes_bcrisToAnn] at hY
  exact false_of_mul_eq_tTilde_pow hε hζ (radRho (p := p)) inv_p_le_inRad radRho_lt_radBig.le hb hφ hrel hY

end Main

end WAFrac

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open ACris

namespace WAFrac

variable {p : ℕ} [hp : Fact p.Prime]

section Frac

variable {G R : Type*} [CommRing R] [IsDomain R] [Algebra ℚ_[p] R]

theorem le_comap_of_injective (f : R →+* R) (hf : Function.Injective f) :
    nonZeroDivisors R ≤ (nonZeroDivisors R).comap f := fun x hx =>
  mem_nonZeroDivisors_of_ne_zero fun h : f x = 0 =>
    nonZeroDivisors.ne_zero hx (hf (show f x = f 0 by rw [h, map_zero]))

def fracMap (f : R →+* R) (hf : Function.Injective f) : FractionRing R →+* FractionRing R :=
  IsLocalization.map (S := FractionRing R) (FractionRing R) f (le_comap_of_injective f hf)

theorem fracMap_algebraMap (f : R →+* R) (hf : Function.Injective f) (x : R) :
    fracMap f hf (algebraMap R (FractionRing R) x) = algebraMap R (FractionRing R) (f x) :=
  IsLocalization.map_eq (S := FractionRing R) (le_comap_of_injective f hf) x

theorem fracMap_comp (f₁ f₂ : R →+* R) (h₁ : Function.Injective f₁) (h₂ : Function.Injective f₂)
    (h : ∀ x, f₁ (f₂ x) = f₂ (f₁ x)) (y : FractionRing R) :
    fracMap f₁ h₁ (fracMap f₂ h₂ y) = fracMap f₂ h₂ (fracMap f₁ h₁ y) := by
  have e : (fracMap f₁ h₁).comp (fracMap f₂ h₂) = (fracMap f₂ h₂).comp (fracMap f₁ h₁) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, fracMap_algebraMap, h])
  exact congrArg (fun F : FractionRing R →+* FractionRing R => F y) e

theorem fracMap_iterate (f : R →+* R) (hf : Function.Injective f) (n : ℕ) (x : R) :
    (fracMap f hf)^[n] (algebraMap R (FractionRing R) x) = algebraMap R (FractionRing R) (f^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, fracMap_algebraMap, Function.iterate_succ_apply']

theorem exists_pair_phi (φ : R →+* R) (hφ : Function.Injective φ)
    (hφq : ∀ q : ℚ_[p], φ (algebraMap ℚ_[p] R q) = algebraMap ℚ_[p] R q)
    (g : G → R →+* R) (hg : ∀ σ, Function.Injective (g σ))
    (hgq : ∀ σ (q : ℚ_[p]), g σ (algebraMap ℚ_[p] R q) = algebraMap ℚ_[p] R q)
    (hgφ : ∀ σ x, g σ (φ x) = φ (g σ x)) {t : R} (ht : φ t = (p : R) * t)
    (hper : ∀ x : R, (∀ σ, g σ x = x) → ∃ n d, 0 < d ∧ φ^[n + d] x = φ^[n] x)
    (hfix : ∀ x y : R, y ≠ 0 → (∀ σ, g σ x * y = x * g σ y) → ∃ z : R, (∀ σ, g σ z = z) ∧ x = z * y)
    (c : G → ℚ_[p]) {a b : R} (hb : b ≠ 0)
    (hrel : ∀ σ, g σ a * b - a * g σ b = algebraMap ℚ_[p] R (c σ) * t * g σ b * b) :
    ∃ a' b' : R, b' ≠ 0 ∧ φ a' * b' = (p : R) * a' * φ b' ∧
      ∀ σ, g σ a' * b' - a' * g σ b' = algebraMap ℚ_[p] R (c σ) * t * g σ b' * b' := by
  have hinj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hne : ∀ {x : R}, x ≠ 0 → algebraMap R (FractionRing R) x ≠ 0 := fun hx h =>
    hx (hinj (by rw [h, map_zero]))
  have hιq : ∀ q : ℚ_[p], algebraMap ℚ_[p] (FractionRing R) q =
      algebraMap R (FractionRing R) (algebraMap ℚ_[p] R q) := fun q =>
    IsScalarTower.algebraMap_apply ℚ_[p] R (FractionRing R) q
  have hgz : ∀ σ {z : R}, z ≠ 0 → g σ z ≠ 0 := fun σ z hz h => hz (hg σ (by rw [h, map_zero]))

  have hy : ∀ σ, fracMap (g σ) (hg σ) (algebraMap R _ a / algebraMap R _ b) -
      algebraMap R _ a / algebraMap R _ b = algebraMap ℚ_[p] (FractionRing R) (c σ) * algebraMap R _ t := by
    intro σ
    rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, hιq, div_sub_div _ _ (hne (hgz σ hb)) (hne hb),
      div_eq_iff (mul_ne_zero (hne (hgz σ hb)) (hne hb))]
    have h := congrArg (algebraMap R (FractionRing R)) (hrel σ)
    simp only [map_sub, map_mul] at h
    linear_combination h

  have hperF : ∀ μ : FractionRing R, (∀ σ, fracMap (g σ) (hg σ) μ = μ) →
      ∃ n d, 0 < d ∧ (fracMap φ hφ)^[n + d] μ = (fracMap φ hφ)^[n] μ := by
    intro μ hμ
    obtain ⟨x, z, hz, rfl⟩ := IsFractionRing.div_surjective (A := R) μ
    have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
    have hcross : ∀ σ, g σ x * z = x * g σ z := by
      intro σ
      have h1 := hμ σ
      rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, div_eq_div_iff (hne (hgz σ hz0)) (hne hz0)]
        at h1
      apply hinj
      simp only [map_mul]
      exact h1
    obtain ⟨w, hw, rfl⟩ := hfix x z hz0 hcross
    obtain ⟨n, d, hd, hnd⟩ := hper w hw
    refine ⟨n, d, hd, ?_⟩
    have e : algebraMap R (FractionRing R) (w * z) / algebraMap R _ z = algebraMap R _ w := by
      rw [map_mul, mul_div_assoc, div_self (hne hz0), mul_one]
    rw [e, fracMap_iterate, fracMap_iterate, hnd]
  obtain ⟨y', hφy', hgy'⟩ := exists_eq_p_mul_of_sub_eq (fracMap φ hφ)
    (fun q => by rw [hιq, fracMap_algebraMap, hφq]) (fun σ => fracMap (g σ) (hg σ))
    (fun σ q => by rw [hιq, fracMap_algebraMap, hgq])
    (fun σ x => fracMap_comp _ _ _ _ (fun x => hgφ σ x) x)
    (show fracMap φ hφ (algebraMap R _ t) = (p : FractionRing R) * algebraMap R _ t by
      rw [fracMap_algebraMap, ht, map_mul, map_natCast])
    hperF c hy

  obtain ⟨a', b', hb', rfl⟩ := IsFractionRing.div_surjective (A := R) y'
  have hb'0 : b' ≠ 0 := nonZeroDivisors.ne_zero hb'
  have hφb' : φ b' ≠ 0 := fun h => hb'0 (hφ (by rw [h, map_zero]))
  refine ⟨a', b', hb'0, ?_, fun σ => ?_⟩
  · rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, mul_div_assoc', div_eq_div_iff (hne hφb') (hne hb'0)]
      at hφy'
    apply hinj
    simp only [map_mul, map_natCast]
    linear_combination hφy'
  · have h1 := hgy' σ
    rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, hιq, div_sub_div _ _ (hne (hgz σ hb'0)) (hne hb'0),
      div_eq_iff (mul_ne_zero (hne (hgz σ hb'0)) (hne hb'0))] at h1
    apply hinj
    simp only [map_mul, map_sub]
    linear_combination h1

end Frac

section Away

variable {G R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem exists_common_den (t : R) [IsLocalization.Away t S] (x y : S) : ∃ (n : ℕ) (α β : R),
    x * algebraMap R S (t ^ n) = algebraMap R S α ∧ y * algebraMap R S (t ^ n) = algebraMap R S β := by
  obtain ⟨n₁, α₁, h₁⟩ := IsLocalization.Away.surj t x
  obtain ⟨n₂, β₂, h₂⟩ := IsLocalization.Away.surj t y
  refine ⟨n₁ + n₂, α₁ * t ^ n₂, β₂ * t ^ n₁, ?_, ?_⟩
  · rw [pow_add, map_mul, ← mul_assoc, map_pow, h₁, map_mul]
  · rw [pow_add, mul_comm (t ^ n₁), map_mul, ← mul_assoc, map_pow, h₂, map_mul]

theorem exists_pair_away (t : R) [IsLocalization.Away t S] (hinj : Function.Injective (algebraMap R S)) (φR : R →+* R) (φS : S →+* S)
    (hφ : ∀ x, φS (algebraMap R S x) = algebraMap R S (φR x)) (gR : G → R →+* R) (gS : G → S →+* S)
    (hg : ∀ σ x, gS σ (algebraMap R S x) = algebraMap R S (gR σ x)) (T : G → R) {a b : S}
    (hb : b ≠ 0) (hφab : φS a * b = (p : S) * a * φS b)
    (hgab : ∀ σ, gS σ a * b - a * gS σ b = algebraMap R S (T σ) * gS σ b * b) :
    ∃ α β : R, β ≠ 0 ∧ φR α * β = (p : R) * α * φR β ∧
      ∀ σ, gR σ α * β - α * gR σ β = T σ * gR σ β * β := by
  obtain ⟨n, α, β, ha, hb'⟩ := exists_common_den t a b
  have hu : IsUnit (algebraMap R S (t ^ n)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit t).pow n
  refine ⟨α, β, ?_, ?_, fun σ => ?_⟩
  · rintro rfl
    rw [map_zero] at hb'
    exact hb (hu.mul_left_eq_zero.1 hb')
  · apply hinj
    have hφa := congrArg φS ha
    have hφb := congrArg φS hb'
    simp only [map_mul, hφ] at hφa hφb
    simp only [map_mul, map_natCast]
    rw [← hφa, ← hb', ← ha, ← hφb]
    linear_combination (algebraMap R S (φR (t ^ n)) * algebraMap R S (t ^ n)) * hφab
  · apply hinj
    have hga := congrArg (gS σ) ha
    have hgb := congrArg (gS σ) hb'
    simp only [map_mul, hg] at hga hgb
    simp only [map_mul, map_sub]
    rw [← hga, ← hb', ← ha, ← hgb]
    linear_combination (algebraMap R S (gR σ (t ^ n)) * algebraMap R S (t ^ n)) * hgab σ

end Away

end WAFrac

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace WAFrac

open ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)
  {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem injective_of_away {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (t : R)
    [IsLocalization.Away t S] (hinj : Function.Injective (algebraMap R S)) (fR : R →+* R) (fS : S →+* S)
    (hf : ∀ x, fS (algebraMap R S x) = algebraMap R S (fR x)) (hfR : Function.Injective fR) :
    Function.Injective fS := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, y, hy⟩ := IsLocalization.Away.surj t x
  have h1 := congrArg fS hy
  rw [map_mul, hx, zero_mul, hf] at h1
  have hy0 : y = 0 := hfR (hinj (by rw [← h1, map_zero, map_zero]))
  rw [hy0, map_zero] at hy
  have hu : IsUnit (algebraMap R S t ^ n) := (IsLocalization.Away.algebraMap_isUnit t).pow n
  exact hu.mul_left_eq_zero.1 hy

theorem map_map_ne_zero {R E : Type*} [CommRing R] [CommRing E] (ι : R →+* E) (hι : Function.Injective ι)
    (g : R →+* R) (hg : Function.Injective g) {b : R} (hb : b ≠ 0) : ι (g b) ≠ 0 := fun h0 =>
  hb (hg (hι (by rw [h0, map_zero, map_zero])))

theorem map_zero_sub_zero_eq {S : Type*} [CommRing S] (g : S →+* S) {T : S} (hT : T = 0) :
    g 0 - 0 = T := by
  rw [hT, map_zero, sub_zero]

theorem smul_div_eq_of_cross {R E G : Type*} [CommRing R] [Field E] [Group G] [MulSemiringAction G E]
    (ι : R →+* E) (g : G → R →+* R) (hιg : ∀ σ x, ι (g σ x) = σ • ι x) {x y : R} (hy : ι y ≠ 0)
    (hgy : ∀ σ, ι (g σ y) ≠ 0) (h : ∀ σ, g σ x * y = x * g σ y) (σ : G) :
    σ • (ι x / ι y) = ι x / ι y := by
  rw [smul_div₀', ← hιg, ← hιg, div_eq_div_iff (hgy σ) hy, ← map_mul, ← map_mul, h σ]

theorem cross_of_smul_div_sub {R E G : Type*} [CommRing R] [Field E] [Group G] [MulSemiringAction G E]
    (ι : R →+* E) (hι : Function.Injective ι) (g : G → R →+* R) (hιg : ∀ σ x, ι (g σ x) = σ • ι x)
    {a b T : R} (σ : G) (hb : ι b ≠ 0) (hgb : ι (g σ b) ≠ 0) (h : σ • (ι a / ι b) - ι a / ι b = ι T) :
    g σ a * b - a * g σ b = T * g σ b * b := by
  rw [smul_div₀', ← hιg, ← hιg, div_sub_div _ _ hgb hb, div_eq_iff (mul_ne_zero hgb hb)] at h
  apply hι
  simp only [map_sub, map_mul] at h ⊢
  linear_combination h

set_option maxHeartbeats 3200000 in
include hζ in
theorem phiB_injective : Function.Injective (phiB hε) :=
  injective_of_away (periodTPlus hε) (algebraMap_bCris_injective hε hζ) (phiPlus ℂ_[p] p) (phiB hε)
    (fun x => phiB_algebraMap hε x) phiPlus_injective

set_option maxHeartbeats 4000000 in
include hζ in

theorem phiB_preperiodic_of_fixed [FiniteDimensional ℚ_[p] K] (μ : BCris hε) (hμ : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ μ = μ) :
    ∃ n d, 0 < d ∧ (phiB hε)^[n + d] μ = (phiB hε)^[n] μ := by
  obtain ⟨k, -, hk⟩ := bCris_fixed_mem_maxUnramified hε hζ μ hμ
  let ιA : BCris hε →ₐ[ℚ_[p]] 𝔹dR :=
    { toRingHom := iotaB hε hζ, commutes' := iotaB_algebraMap_padic hε hζ }
  let φA : BCris hε →ₐ[ℚ_[p]] BCris hε :=
    { toRingHom := phiB hε, commutes' := phiB_algebraMap_padic' hε }
  have halg : IsAlgebraic ℚ_[p] (ιA μ) := by
    change IsAlgebraic ℚ_[p] (iotaB hε hζ μ)
    rw [hk]
    exact (Algebra.IsAlgebraic.isAlgebraic k).algHom
      ((IsScalarTower.toAlgHom ℚ_[p] 𝔹 𝔹dR).comp (algClToBdR p))
  exact exists_iterate_eq_of_algebraic ιA (iotaB_injective hε hζ) φA halg

set_option maxHeartbeats 4000000 in
include hζ in

theorem exists_fixed_of_cross [FiniteDimensional ℚ_[p] K] (x y : BCris hε) (hy : y ≠ 0)
    (h : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x * y = x * galB hε σ y) :
    ∃ z : BCris hε, (∀ σ : Gal(PadicAlgCl p/K), galB hε σ z = z) ∧ x = z * y := by
  have hιy : iotaB hε hζ y ≠ 0 := fun h0 => hy (iotaB_injective hε hζ (by rw [h0, map_zero]))
  have hμF : iotaB hε hζ x / iotaB hε hζ y ∈ fracBCris hε hζ :=
    div_mem (iotaB_mem_fracBCris hε hζ x) (iotaB_mem_fracBCris hε hζ y)
  have hμfix : ∀ σ : Gal(PadicAlgCl p/K), σ • (iotaB hε hζ x / iotaB hε hζ y) = iotaB hε hζ x / iotaB hε hζ y :=
    smul_div_eq_of_cross (iotaB hε hζ) (fun σ : Gal(PadicAlgCl p/K) => galB hε σ)
      (fun σ z => iotaB_galB hε hζ σ z) hιy
      (fun σ h0 => hy (galB_injective hε σ (iotaB_injective hε hζ (by rw [h0, map_zero, map_zero])))) h
  obtain ⟨k, hk, hμk⟩ := fracBCris_fixed hε hζ hμF hμfix
  obtain ⟨z, hz, hzk⟩ := exists_bCris_fixed hε hζ hk
  refine ⟨z, hz, iotaB_injective hε hζ ?_⟩
  have e1 : iotaB hε hζ z = iotaB hε hζ x / iotaB hε hζ y :=
    hzk.trans ((algClToBdRField_apply k).symm.trans hμk.symm)
  rw [map_mul, e1, div_mul_cancel₀ _ hιy]

set_option maxHeartbeats 4000000 in

theorem false_of_bCris_pair [FiniteDimensional ℚ_[p] K] {a b : BCris hε} (hb : b ≠ 0)
    (hrel : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ a * b - a * galB hε σ b =
      algebraMap ℚ_[p] (BCris hε) (kummerC hε hζ σ : ℚ_[p]) * periodTCris hε * galB hε σ b * b) :
    False := by
  have := isDomain_bCris hε hζ
  obtain ⟨a', b', hb', hφ', hg'⟩ := exists_pair_phi (phiB hε) (phiB_injective hε hζ)
    (phiB_algebraMap_padic' hε) (fun σ : Gal(PadicAlgCl p/K) => galB hε σ) (fun σ => galB_injective hε σ)
    (fun σ q => galB_algebraMap_padic hε σ q) (fun σ x => (phiB_galB hε σ x).symm)
    (phiB_periodTCris hε) (phiB_preperiodic_of_fixed hε hζ) (exists_fixed_of_cross hε hζ)
    (fun σ => (kummerC hε hζ σ : ℚ_[p])) hb hrel
  have := isDomain_bCrisPlus (p := p)
  obtain ⟨α, β, hβ, hφ, hg⟩ := exists_pair_away (periodTPlus hε) (algebraMap_bCris_injective hε hζ)
    (phiPlus ℂ_[p] p) (phiB hε) (fun x => phiB_algebraMap hε x) (fun σ : Gal(PadicAlgCl p/K) => galPlus σ)
    (fun σ => galB hε σ) (fun σ x => galB_algebraMap hε σ x)
    (fun σ => algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (kummerC hε hζ σ : ℚ_[p]) * periodTPlus hε) hb' hφ'
    (fun σ => (hg' σ).trans (by rw [algebraMap_padic_mul_periodTPlus]))
  exact false_of_frac hε hζ (K := K) hg hβ hφ

set_option maxHeartbeats 4000000 in

theorem not_forall_gal_smul_sub_eq [FiniteDimensional ℚ_[p] K] {y : 𝔹dR} (hy : y ∈ fracBCris hε hζ) :
    ¬ ∀ σ : Gal(PadicAlgCl p/K), σ • y - y =
      iotaB hε hζ (algebraMap ℚ_[p] (BCris hε) (kummerC hε hζ σ : ℚ_[p]) * periodTCris hε) := by
  intro h
  obtain ⟨a, b, rfl⟩ := exists_eq_div_of_mem_closure_range (iotaB hε hζ) hy
  by_cases hb : b = 0
  · refine not_forall_galB_sub_eq_kummerC hε hζ (K := K) 0 fun σ => ?_
    have h1 := h σ
    have h0 : iotaB hε hζ a / iotaB hε hζ b = 0 := by rw [hb, map_zero, div_zero]
    rw [h0, smul_zero, sub_zero] at h1
    exact map_zero_sub_zero_eq (galB hε σ) (iotaB_injective hε hζ (h1.symm.trans (map_zero _).symm))
  have hιb : iotaB hε hζ b ≠ 0 := fun h0 => hb (iotaB_injective hε hζ (by rw [h0, map_zero]))
  refine false_of_bCris_pair hε hζ (K := K) (a := a) hb fun σ => ?_
  have hιgb : iotaB hε hζ (galB hε σ b) ≠ 0 :=
    map_map_ne_zero (iotaB hε hζ) (iotaB_injective hε hζ) (galB hε σ) (galB_injective hε σ) hb
  exact cross_of_smul_div_sub (iotaB hε hζ) (iotaB_injective hε hζ)
    (fun σ : Gal(PadicAlgCl p/K) => galB hε σ) (fun σ z => iotaB_galB hε hζ σ z) σ hιb hιgb (h σ)

end WAFrac

end GroundTheory.PAdicHodge
end
end
