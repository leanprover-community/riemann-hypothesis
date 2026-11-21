import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittedTiesBoundEventualStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ArchSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvHasInfinityTypeCmType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeightEqAbsInfType

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.BotSmall

theorem bottom_small : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (δ t0 : ℂ) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) (i j : Fin D.R.m) 𝔪, IsBottom G μ₀ i j 𝔪 P P' → P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap) := by
  intro D T L sc μ₀ hL G δ t0 Q P P' i j 𝔪 hB
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hB.rank
  have hd : P.d ≤ 2 * bigN D := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    have hj := j.2
    obtain ⟨e1, e2, -⟩ := ranks_exact D i j
    have h1 : rankV D (i + 1) (j + 1) ≤ bigN D - 1 := by
      simp only [rankV, bigN, Ranks.r]
      have : (↑i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
      have : (↑j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
      have : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
      omega
    have h2 : rankV D i j ≤ rankV D (i + 1) (j + 1) := by
      simp only [rankV]
      have : (↑i) * sLen D ≤ (↑i + 1) * sLen D := Nat.mul_le_mul_right _ (by omega)
      have : (↑j) * D.R.t ≤ (↑j + 1) * D.R.t := Nat.mul_le_mul_right _ (by omega)
      omega
    omega

  have key : ∀ (R : Pair D ⊤ δ t0 Q) (χ : Formalism.L2.Host.HChar D.host.E),
      HasChars R χ (nuH G μ₀ i j)⁻¹ → R.d = botBig D i j + botSmall D i j → ∀ τ, (R.n τ : ℝ) ≤ 2 * (maxWt D sc.cGap : ℝ) := by
    intro R χ hc hRd τ
    have habs := GlobalTheory.SplitWeight.abs_weight_eq_abs_infType R.W.chV' R.W.ep' (nuH G μ₀ i j)⁻¹ _ R.W.ep_pm.2 hc.2
      (nuH_inv_hasInf hL G i j) τ
    have hw := R.wt τ
    have hsub := two_mul_wtA_sub D sc.cGap i j τ
    set E := (num D sc.cGap τ).e (↑j + 1) + cen D sc.cGap τ (D.R.m - ↑i)
    have hA : (wtA D sc.cGap i j τ).natAbs ≤ maxWt D sc.cGap ∧ (wtA' D sc.cGap i j τ).natAbs ≤ maxWt D sc.cGap := by
      have := Finset.le_sup (f := fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
        max (wtA D sc.cGap x.1 x.2.1 x.2.2).natAbs (wtA' D sc.cGap x.1 x.2.1 x.2.2).natAbs) (Finset.mem_univ (i, j, τ))
      have h2 := le_max_right 1 (Finset.univ.sup fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
        max (wtA D sc.cGap x.1 x.2.1 x.2.2).natAbs (wtA' D sc.cGap x.1 x.2.1 x.2.2).natAbs)
      simp only at this
      exact ⟨le_trans (le_max_left _ _) (this.trans h2), le_trans (le_max_right _ _) (this.trans h2)⟩
    have hA1 : |wtA D sc.cGap i j τ| ≤ (maxWt D sc.cGap : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hA.1
    have hA2 : |wtA' D sc.cGap i j τ| ≤ (maxWt D sc.cGap : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hA.2
    have hep : |(R.W.ep' : ℤ) * R.W.chV'.n τ| = |2 * E| := by
      rw [abs_mul, ← habs]
      rcases R.W.ep_pm.2 with h | h <;> rw [h] <;> simp
    have hdz : (R.d : ℤ) = (botBig D i j : ℤ) + (botSmall D i j : ℤ) := by rw [hRd]; push_cast; ring
    have hn : (R.n τ : ℤ) ≤ 2 * (maxWt D sc.cGap : ℤ) := by
      have hnn : (0 : ℤ) ≤ R.n τ := Nat.cast_nonneg _
      have hpos : 0 ≤ (R.W.ep' : ℤ) * R.W.chV'.n τ := by push_cast at hw; omega
      rw [abs_of_nonneg hpos] at hep
      have h1 := abs_le.1 hA1
      have h2 := abs_le.1 hA2
      rcases le_or_gt 0 E with hE | hE
      · rw [abs_of_nonneg (by omega)] at hep
        push_cast at hw hsub; omega
      · rw [abs_of_neg (by omega)] at hep
        push_cast at hw hsub; omega
    exact_mod_cast hn
  exact ⟨⟨hd, key P _ hB.chars hr3⟩, ⟨hr4 ▸ hd, key P' _ hB.chars' (hr4.trans hr3)⟩⟩

end GlobalTheory.BotSmall
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareBottomPairs_small_reference_tuple : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (δ t0 : ℂ) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) (i j : Fin D.R.m) 𝔪, IsBottom G μ₀ i j 𝔪 P P' → P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap) := by
  atlas_forward_decl GlobalTheory.BotSmall.bottom_small
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.ArchGrid

theorem level_pos {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) : 0 < Q := by
  rcases Nat.eq_zero_or_pos Q with rfl | h
  · have h1 := P.idx_le
    rw [zero_pow (by positivity)] at h1
    exact absurd (Nat.le_zero.1 h1) P.idx_ne
  · exact h

theorem arch_grid : GlobalTheory.SqTop.GBig fun {D} _ _ {sc} G μ₀ C _ b => ∀ (zA zA' : Fin D.R.m × Fin D.R.m → D.what₂.LL), (∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : Pair D ⊤ δ t0 (levQ G.pl), IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P' ∧ D.what₂.embLL (zA ij) = (P.norm : ℂ) ∧ D.what₂.embLL (zA' ij) = (P'.norm : ℂ)) → ArchimedeanHeightBound zA zA' (C * D.R.f * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ) * (Real.log b + Real.log ((maxWt D sc.cGap : ℝ) * (2 * (bigN D : ℝ)))) + C * D.R.f * (bigN D : ℝ) ^ 2 * (Real.log b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ))) + C * (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl)) := by
  obtain ⟨C0, -, hA⟩ := GlobalTheory.ArchFree.st.archSt
  refine ⟨0, fun ε CF _ => ⟨C0, 0, fun C hC D large₂ _ _ hR T Lc μ₀ hμ G => ?_⟩⟩
  rintro zA zA' ⟨δ, t0, h⟩
  choose P P' hB hz hz' using h
  haveI := D.tcLL
  obtain ⟨-, -, hf4, hm44, -, -, -, -, -, hrd1, hrd2, -⟩ := hR.size
  have hLpos : 0 < large₂.sc.L := Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hL1 : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hlb : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hN : 1 ≤ bigN D := by have := D.R.m_add_three_le_k; unfold bigN; omega
  have hB1 : (1 : ℝ) ≤ (maxWt D 1 : ℝ) := by exact_mod_cast le_max_left _ _
  have hrd : Real.log D.host.rdE ≤ Real.log large₂.sc.b := by rw [hlb]; linarith
  have hdl : |TaylorLogMetric.logDerivativeAtOne D| ≤ Real.log large₂.sc.b := by
    rw [hlb]
    have e : TaylorLogMetric.logDerivativeAtOne D = large₂.logDerivativeAtOne := by rw [large₂.logDerivative_at_one_eq]; rfl
    rw [e]; exact hR.dlog
  intro ij
  have hQ : 0 < levQ G.pl := level_pos (P ij)
  have key := hA D ⊤ δ t0 (levQ G.pl) (P ij).crv (P ij).pt0 hQ D.what₂.LL D.what₂.embLL (Fin D.R.m × Fin D.R.m) (bigN D)
    (maxWt D 1 : ℝ) (Real.log large₂.sc.b) P P' zA zA' hN hB1 (by rw [hlb]; exact hL1) hrd hdl
    (fun k => GlobalTheory.T.squareBottomPairs_small_reference_tuple hμ G δ t0 _ (P k) (P' k) k.1 k.2 _ (hB k)) (fun k => ⟨hz k, hz' k⟩) ij
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hf4
    exact_mod_cast this
  have hN' : (1 : ℝ) ≤ (bigN D : ℝ) := by exact_mod_cast hN
  have hX : 0 ≤ (D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ) := by
    have h1 : 0 ≤ Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ))) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ)) := by
      apply Real.log_nonneg
      have : 1 ≤ (D.R.f : ℝ) * (2 * (bigN D : ℝ)) := by nlinarith
      nlinarith
    have h3 : 0 ≤ Real.log (levQ G.pl : ℝ) := Real.log_natCast_nonneg _
    have hl : 0 ≤ Real.log large₂.sc.b := by rw [hlb]; linarith
    positivity
  have hle : ∀ c : ℝ, c * (D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      c * (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      c * (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ) = c * ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ)) := fun c => by ring
  have hmono := mul_le_mul_of_nonneg_right hC hX
  show _ ∧ _
  constructor
  · refine le_trans key.1 (le_of_eq_of_le ?_ (le_of_le_of_eq hmono ?_))
    · exact (hle C0).symm ▸ rfl
    · exact (hle C).symm
  · refine le_trans key.2 (le_of_eq_of_le ?_ (le_of_le_of_eq hmono ?_))
    · exact (hle C0).symm ▸ rfl
    · exact (hle C).symm

end GlobalTheory.ArchGrid
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanBound_bottomPairs_norms_grid : GlobalTheory.SqTop.GBig fun {D} _ _ {sc} G μ₀ C _ b => ∀ (zA zA' : Fin D.R.m × Fin D.R.m → D.what₂.LL), (∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : Pair D ⊤ δ t0 (levQ G.pl), IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P' ∧ D.what₂.embLL (zA ij) = (P.norm : ℂ) ∧ D.what₂.embLL (zA' ij) = (P'.norm : ℂ)) → ArchimedeanHeightBound zA zA' (C * D.R.f * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ) * (Real.log b + Real.log ((maxWt D sc.cGap : ℝ) * (2 * (bigN D : ℝ)))) + C * D.R.f * (bigN D : ℝ) ^ 2 * (Real.log b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ))) + C * (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl)) := by
  atlas_forward_decl GlobalTheory.ArchGrid.arch_grid
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

theorem GlobalTheory.BigTop.Fun.arch_tie (hS : SetAt)
    (hd : Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (_hA : GlobalTheory.NormSum.ArchSt) (_hB : BotSmall) : Arch @Comparison₂ := by
  have hQ := GlobalTheory.T.fitted_ties_bound_eventual _ hS hd GlobalTheory.T.archimedeanBound_bottomPairs_norms_grid
  refine Lf.mono hQ ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH _ hd
  refine ⟨hd, fun hq => ?_⟩
  obtain ⟨a, ha⟩ := hd.2
  have hsq := ha.sq
  have hA := hq d.zA d.zA' hsq.norms
  show ArchimedeanHeightBound d.zA d.zA' (d.O.bArch C p.Z.b)
  have eN : (d.O.N : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ) := by
    have := D.R.m_add_three_le_k
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    norm_cast
    show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (GlobalTheory.ChiGrid.sLen D) + 1)
    unfold GlobalTheory.ChiGrid.sLen
    rw [hr]
    congr 3
    omega
  have eB : d.O.Bw = (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) := hsq.weight
  have eS : d.O.cS = Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := by
    rw [GlobalTheory.FunObj.SqNum.log_levQ]
    rfl
  have ef : (d.O.f : ℝ) = D.R.f := rfl
  have e1 : d.O.bArch C p.Z.b = C * D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) *
        (Real.log p.Z.b + Real.log ((GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)))) +
      C * D.R.f * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 *
        (Real.log p.Z.b + Real.log ((D.R.f : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ))) +
      C * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := by
    unfold FunData.bArch
    rw [eN, eB, eS, ef]
  rw [e1]
  exact hA
end
end
