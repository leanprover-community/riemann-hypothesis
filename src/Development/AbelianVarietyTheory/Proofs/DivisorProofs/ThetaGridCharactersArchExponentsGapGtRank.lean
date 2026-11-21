import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (a : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D c τ (a τ)) →
    ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ m : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) c m ∧ ∀ w, (m w : ℚ) = -2 * a (τf w) := by
  first | exact @GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp | exact GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp | (intros; apply GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ChiGrid

theorem rankV_add_lt_two_e_add_two_cen {D : D7} (C : ℝ) (τ : D.what₂.Tau) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) :
    ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) < 2 * (D.hc τ).e ⟨j, hj⟩ + 2 * (cen D C τ (D.R.m - i) : ℚ) := by
  set P := D.hc τ with hP
  set G := GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) 0 with hG
  obtain ⟨hv, hb, -⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) 0
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hGm : G.m = D.R.m := rfl
  have hGk : G.k = D.R.k := rfl
  have hGga : G.ga = gap D C := rfl

  have h1 := P.gap_be ⟨j, hj⟩

  have e0 : P.b ⟨0, by omega⟩ = (G.b 1 : ℚ) := hb ⟨0, by omega⟩
  have ej : P.b ⟨j, hj⟩ = (G.b (j + 1) : ℚ) := hb ⟨j, hj⟩
  have h2 : P.b ⟨0, by omega⟩ ≤ P.b ⟨j, hj⟩ := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact le_rfl
    · have := G.b_mono 1 (j + 1) le_rfl (by omega) (by rw [hGm]; omega)
      rw [e0, ej]; exact_mod_cast this.le

  have hu2 := P.u_last_gt (by omega) (by omega)
  have hu1 := P.v_gt_u ⟨D.R.k - 2, by omega⟩
  have hu : P.u ⟨D.R.k - 2 + 1, by omega⟩ = P.u ⟨D.R.k - 1, by omega⟩ :=
    congrArg P.u (Fin.ext (by dsimp only; omega))
  have ev0 : P.v ⟨0, by omega⟩ = (G.v 2 : ℚ) := hv ⟨0, by omega⟩
  have evl : P.v ⟨D.R.k - 2, by omega⟩ = (G.v D.R.k : ℚ) := by
    have := hv ⟨D.R.k - 2, by omega⟩
    dsimp only at this
    rwa [Nat.sub_add_cancel (by omega : 2 ≤ D.R.k)] at this
  have hvv : G.v D.R.k < G.v 2 := G.v_anti 2 D.R.k le_rfl (by omega) (by rw [hGk])
  have hvv' : (G.v D.R.k : ℚ) < G.v 2 := by exact_mod_cast hvv
  rw [hu] at hu1
  rw [evl] at hu1

  have hc : G.mid (D.R.m - i) < (cen D C τ (D.R.m - i) : ℚ) + 1 := Int.lt_floor_add_one _
  have hmid : G.mid (D.R.m - i) = G.a (D.R.m - i) + G.ga / 2 := G.mid_eq (by omega)
  have ha : G.a (D.R.m - i) = (G.v 2 : ℚ) + 1 / 2 + ((i : ℚ) + 1) * (gap D C : ℚ) := by
    simp only [GlobalTheory.SignedHC.GridData.a, hGm, hGga]
    rw [Nat.cast_sub hi.le]; ring
  rw [hmid, ha, hGga] at hc

  have hg := (isLeast_gap D C).1.2.1
  have hN : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Formalism.BasicNotions.Ranks.r; omega
  have m1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m2 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m3 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have m4 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have hrank : rankV D (i + 1) (j + 1) + rankV D i j ≤ 2 * bigN D := by
    unfold rankV bigN; nlinarith
  have hR : rankV D (i + 1) (j + 1) + rankV D i j + 1 ≤ gap D C := by omega
  have hR' : ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) + 1 ≤ (gap D C : ℚ) := by exact_mod_cast hR
  have hpos : (0 : ℚ) ≤ (i : ℚ) * (gap D C : ℚ) := by positivity
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have h0 : (0 : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by positivity
  nlinarith

end GlobalTheory.ChiGrid
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre : ∀ {D : D7} (C : ℝ) (τ : D.what₂.Tau) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m),
    ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) < 2 * (D.hc τ).e ⟨j, hj⟩ + 2 * (cen D C τ (D.R.m - i) : ℚ) := by
  first | exact @GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen | exact GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen | (intros; apply GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SquareExps

open GlobalTheory.Chain.StepVac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasInfExp_one_of (τ : D.what₂.Tau) (h : ∃ θ, IsInfFam (D := D) θ) : HasInfExp D (1 : (AE D)ˣ →* Circle) τ 0 :=
  ⟨0, by simp, h, fun θ _ x _ _ => by simp⟩

theorem hasInfExp_pow {η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {b : ℚ} (h : HasInfExp D η τ b) (n : ℕ) :
    HasInfExp D (η ^ n) τ (n * b) := by
  induction n with
  | zero =>
    obtain ⟨_, _, hθ, _⟩ := h
    simpa using hasInfExp_one_of τ hθ
  | succ n ih =>
    rw [pow_succ]
    have := hasInfExp_mul ih h
    convert this using 1
    push_cast; ring

theorem eta_exp {μ₀ : T} (hL : L.Is μ₀) (τ : D.what₂.Tau) : HasInfExp D L.eta τ (1 / 2) :=
  GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
    (hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ

theorem alpha_exp {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (alpha G t i j) τ (-(D.hc τ).e ⟨j, hj⟩ + (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j : ℚ) * (1 / 2)) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 ⟨j, hj⟩) (hasInfQ_tau (L.C.isMu0 ⟨j, hj⟩).inf) τ
  obtain ⟨θ, hθ⟩ : ∃ θ, IsInfFam (D := D) θ := by
    obtain ⟨_, _, hθ, _⟩ := h0
    exact hθ
  have h1 : HasInfExp D (L.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩) := by
    have := hasInfExp_mul h0 (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
    rw [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
    exact this
  exact hasInfExp_mul h1 (hasInfExp_pow (eta_exp hL τ) _)

theorem beta_exp {μ₀ : T} (hL : L.Is μ₀) (i j : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (beta G i j) τ ((cen D sc.cGap τ (D.R.m - i) : ℚ) + (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j : ℚ) * (1 / 2)) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  exact hasInfExp_mul h0 (hasInfExp_pow (eta_exp hL τ) _)

theorem exps : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ mα mβ : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (alpha G t i j) mα ∧
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (beta G i j) mβ ∧
      ∀ w, (((spW G i j).rank + (spW₁ G i j).rank : ℕ) : ℤ) < mα w - mβ w := by
  intro D T L sc G μ₀ hL t i j _ τf hτf
  obtain ⟨mα, hα, eα⟩ := GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => alpha_exp (G := G) hL t i j j.2 τ) τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => beta_exp (G := G) hL i j i.2 τ) τf hτf
  refine ⟨mα, mβ, hα, hβ, fun w => ?_⟩
  have hr : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have key := GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre sc.cGap (τf w) i j i.2 j.2
  have e1 : (spW G i j).rank = rankV D (i + 1) (j + 1) := hr _ _ (by omega) (by omega)
  have e2 : (spW₁ G i j).rank = rankV D i j := hr _ _ (by omega) (by omega)
  rw [e1, e2]
  have h1 := eα w
  have h2 := eβ w
  have : (((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ) := by
    push_cast at h1 h2 key ⊢
    rw [h1, h2]
    linarith
  exact_mod_cast this

end GlobalTheory.SquareExps

end
end
