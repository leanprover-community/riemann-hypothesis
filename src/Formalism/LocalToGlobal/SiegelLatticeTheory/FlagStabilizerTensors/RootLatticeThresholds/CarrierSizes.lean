import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.HermitianCurvature.StatementJCT
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupremumAIsMajorant

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.CarrierSz

theorem unram_host (D : D7) :
    haveI : IsCMField D.host.E := D.host.isCMField_hostE
    Formalism.FourierDecayAlt.S6.Unram D.host.E := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  exact Formalism.MainNotions.LocalModelPeriodLattices.unramE D

theorem g_pos (D : D7) : 0 < D.host.g 0 ∧ 0 < D.host.g 1 :=
  ⟨(D.host.g_prime 0).pos, (D.host.g_prime 1).pos⟩

section Cut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem cut_len (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq) (v : Fin S.f) :
    S.cutHi v - S.cutLo v = S.G.Del / 2 - 5 / 2 := by
  unfold Formalism.FourierDecayAlt.C.HidaSetting.cutHi Formalism.FourierDecayAlt.C.HidaSetting.cutLo
  simp only [Formalism.FourierDecayAlt.Sz.Glob.place]
  ring


end Cut

theorem rpow_ge_mul {x t : ℝ} (hx : 3 ≤ x) (ht : 1 ≤ t) : t * x ≤ x ^ t := by
  have hx0 : 0 < x := by linarith
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have h1 : x ^ t = x * x ^ (t - 1) := by
    conv_lhs => rw [show t = 1 + (t - 1) by ring]
    rw [Real.rpow_add hx0, Real.rpow_one]
  have h2 : t ≤ x ^ (t - 1) := by
    rw [Real.rpow_def_of_pos hx0]
    have := Real.add_one_le_exp (Real.log x * (t - 1))
    nlinarith
  rw [h1]
  nlinarith

theorem del_ge (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT : ℝ} (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCl : 1 ≤ Cl) : Cl * ((D.R.k : ℝ) * D.R.f) ≤ (D.s.Del : ℝ) := by
  obtain ⟨-, -, hmf, hfk, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hDel, -, -, -, -, -⟩ := h
  have hm := D.R.two_le_m
  have hf16 : 16 ≤ D.R.f := le_trans (by have := Nat.pow_le_pow_left hm 4; norm_num at this ⊢; omega) hmf
  have hk16 : 16 ≤ D.R.k := le_trans hf16 hfk
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hf : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf16
  have hk : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk16
  have hkf : (D.R.k : ℝ) * D.R.f ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := by
    have : 0 ≤ (D.R.k : ℝ) * D.R.f := by positivity
    nlinarith
  have h3 : (3 : ℝ) ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := by nlinarith
  have := rpow_ge_mul h3 hCl
  calc Cl * ((D.R.k : ℝ) * D.R.f) ≤ Cl * ((D.R.k : ℝ) * D.R.f * large₂.sc.L) :=
        mul_le_mul_of_nonneg_left hkf (by linarith)
    _ ≤ ((D.R.k : ℝ) * D.R.f * large₂.sc.L) ^ Cl := this
    _ ≤ (D.s.Del : ℝ) := hDel

def ClCut (C₆ : ℝ) : ℝ := max 1 ((420 * C₆ + 48125) / 8)

theorem long_cut_num (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT : ℝ} (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (C₆ : ℝ) (hC6 : 0 ≤ C₆) (hCl : ClCut C₆ ≤ Cl) :
    6 * (20 * ((D.R.rS : ℝ) + 1)) ^ 3 + 6 * (20 * ((D.R.rS : ℝ) + 1)) ≤ (D.s.Del : ℝ) / 2 - 5 / 2 ∧
    C₆ * ((D.R.k : ℝ) * (20 * ((D.R.rS : ℝ) + 1)) * ((D.R.rS : ℝ) + 1) ^ 2 +
      (20 * ((D.R.rS : ℝ) + 1)) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2) ≤ (D.s.Del : ℝ) / 2 - 5 / 2 := by
  have hCl1 : 1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl2 : (420 * C₆ + 48125) / 8 ≤ Cl := le_trans (le_max_right _ _) hCl
  have hD := del_ge D large₂ h hCl1
  obtain ⟨-, -, hmf, hfk, -⟩ := h
  have hmR : (D.R.m : ℝ) = 2 * ((D.R.rS : ℝ) + 1) := by
    have h2 : D.R.m = 2 * D.R.rS + 2 := by
      unfold Formalism.BasicNotions.Ranks.rS; obtain ⟨a, ha⟩ := D.R.m_even; have := D.R.two_le_m; omega
    have : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by exact_mod_cast h2
    linarith
  have hf : (D.R.m : ℝ) ^ 4 ≤ D.R.f := by exact_mod_cast hmf
  have hk1 : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  generalize hR : (D.R.rS : ℝ) + 1 = R at hmR ⊢
  generalize hk : (D.R.k : ℝ) = k at hk1 hD ⊢
  have hR1 : 1 ≤ R := by nlinarith
  have hR3 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ hR1 (by norm_num)
  have hRR : R ≤ R ^ 4 := by
    calc R = R ^ 1 := (pow_one R).symm
      _ ≤ R ^ 4 := pow_le_pow_right₀ hR1 (by norm_num)
  have hR4 : 1 ≤ R ^ 4 := one_le_pow₀ hR1
  have hm4 : (16 : ℝ) ≤ (D.R.m : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hm2 4
    norm_num at this ⊢; linarith
  have hk1' : 1 ≤ k := by linarith
  have hP1 : R ^ 4 ≤ k * R ^ 4 := by nlinarith
  have hPk : k * R ^ 3 ≤ k * R ^ 4 := by nlinarith
  have hkf : 16 * (k * R ^ 4) ≤ k * (D.R.f : ℝ) := by
    have h16 : 16 * R ^ 4 = (D.R.m : ℝ) ^ 4 := by rw [hmR]; ring
    nlinarith
  have hDel : 16 * Cl * (k * R ^ 4) ≤ (D.s.Del : ℝ) := by
    have := mul_le_mul_of_nonneg_left hkf (by linarith : (0 : ℝ) ≤ Cl)
    linarith
  have hbig : (420 * C₆ + 48125) * (k * R ^ 4) ≤ 8 * Cl * (k * R ^ 4) := by
    have hP0 : 0 ≤ k * R ^ 4 := by nlinarith
    nlinarith
  refine ⟨?_, ?_⟩
  · nlinarith
  · have : C₆ * (k * (20 * R) * R ^ 2 + (20 * R) ^ 2 * R ^ 2) ≤ C₆ * (420 * (k * R ^ 4)) := by
      apply mul_le_mul_of_nonneg_left _ hC6
      nlinarith
    nlinarith


section Grids

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Sz

def GridsAt (c : Cfg) (l N : ℕ) (grid : ℕ → Finset ℝ) (grid1 : Finset ℝ) : Prop :=
  6 * (N : ℝ) ^ 3 + 6 * N ≤ (c.Del / 2 - c.v l) - (5 / 2 - c.v l) ∧
  (∀ a, ∀ y ∈ grid a, 1 ≤ a ∧ a ≤ N ∧ C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a ≤ y ∧
      y ≤ C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a +
        ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) / (6 * N) - 1) ∧
  (∀ y ∈ grid1, y ∈ c.cutIntervalLong l N ∧ y + 1 ∈ c.cutIntervalLong l N) ∧
  (∀ y ∈ grid1, ∀ y' ∈ grid1, y ≠ y' → ∀ e ∈ ({0, 1} : Finset ℝ), ∀ e' ∈ ({0, 1} : Finset ℝ),
      (N : ℝ) ^ 2 / 8 ≤ |(y + e) - (y' + e')|) ∧
  (∀ y ∈ grid1, ∀ a, ∀ y' ∈ grid a, ∀ e ∈ ({0, 1} : Finset ℝ), ∀ e' ∈ ({0, 1} : Finset ℝ),
      (N : ℝ) ^ 2 + 1 ≤ |(y + e) - (y' + e')|) ∧
  (∀ y, ((∃ a, y ∈ grid a) ∨ y ∈ grid1) →
      y ∈ c.cutI l ∧ y + 1 ∈ c.cutI l ∧ c.P y ≠ 0 ∧ c.P (y + 1) ≠ 0)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem gridsOK_iff (S : C.HidaSetting E Wp Wq) :
    C.GridsOK S ↔ ∀ v, GridsAt (S.G.place (S.pl v)) S.l S.Ntop (S.grid v) (S.grid1 v) := Iff.rfl

theorem exists_good (c : Cfg) {A B : ℝ} (h : A < B) :
    ∃ y, A ≤ y ∧ y ≤ B ∧ c.P y ≠ 0 ∧ c.P (y + 1) ≠ 0 := by
  classical
  let bad : Finset ℝ := (Finset.Icc 1 (c.k + c.m - 1)).image (fun s => -c.lam s) ∪
    (Finset.Icc 1 (c.k + c.m - 1)).image (fun s => -c.lam s - 1)
  obtain ⟨y, hy, hyb⟩ := (Set.Icc_infinite h).exists_notMem_finset bad
  refine ⟨y, hy.1, hy.2, ?_, ?_⟩
  · intro h0
    unfold Cfg.P at h0
    obtain ⟨s, hs, hs0⟩ := Finset.prod_eq_zero_iff.mp h0
    exact hyb (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hs, by linarith⟩))
  · intro h0
    unfold Cfg.P at h0
    obtain ⟨s, hs, hs0⟩ := Finset.prod_eq_zero_iff.mp h0
    exact hyb (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hs, by linarith⟩))

def pickIn (c : Cfg) (A B : ℝ) : ℝ :=
  Classical.epsilon (fun y => A ≤ y ∧ y ≤ B ∧ c.P y ≠ 0 ∧ c.P (y + 1) ≠ 0)

theorem pickIn_spec (c : Cfg) {A B : ℝ} (h : A < B) :
    A ≤ pickIn c A B ∧ pickIn c A B ≤ B ∧ c.P (pickIn c A B) ≠ 0 ∧ c.P (pickIn c A B + 1) ≠ 0 :=
  Classical.epsilon_spec (exists_good c h)

def gridOf (c : Cfg) (l N : ℕ) (a : ℕ) : Finset ℝ :=
  if 1 ≤ a ∧ a ≤ N then
    {pickIn c (C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a)
      (C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a + ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) / (6 * N) - 1)}
  else ∅

def node1 (c : Cfg) (l N j : ℕ) : ℝ :=
  pickIn c (5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2) (5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2 + 1 / 2)

def grid1Of (c : Cfg) (l N : ℕ) : Finset ℝ := (Finset.range N).image (node1 c l N)

theorem first_level_node_spec (c : Cfg) (l N j : ℕ) :
    5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2 ≤ node1 c l N j ∧
      node1 c l N j ≤ 5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2 + 1 / 2 ∧
      c.P (node1 c l N j) ≠ 0 ∧ c.P (node1 c l N j + 1) ≠ 0 :=
  pickIn_spec c (by linarith)

theorem first_level_nodes_separated (c : Cfg) (l N : ℕ) {j j' : ℕ} (h : j < j') :
    (N : ℝ) ^ 2 - 1 / 2 ≤ node1 c l N j' - node1 c l N j := by
  have h1 := first_level_node_spec c l N j
  have h2 := first_level_node_spec c l N j'
  have hj : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
  have hN : 0 ≤ (N : ℝ) ^ 2 := by positivity
  nlinarith [h1.2.1, h2.1]


theorem grids_card (c : Cfg) (l N : ℕ) (hN : 1 ≤ N) :
    (grid1Of c l N).card = N ∧ ∀ a, 1 ≤ a → a ≤ N → (gridOf c l N a).card = 1 := by
  refine ⟨?_, fun a h1 h2 => by simp [gridOf, h1, h2]⟩
  unfold grid1Of
  rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro j j' h
  by_contra hne
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · have := first_level_nodes_separated c l N hl; rw [h] at this; nlinarith
  · have := first_level_nodes_separated c l N hl; rw [h] at this; nlinarith



end Grids

section TransportedAlt

open Formalism.FourierDecayAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]




theorem glob_pos (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT : ℝ} (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCl : ClCut 0 ≤ Cl) (S : C.HidaSetting E Wp Wq) (hr : S.G.r = D.R.rS) (hDel : S.G.Del = (D.s.Del : ℝ))
    (hv : S.G.v = D.host.v) (hg1 : S.G.g1 = D.host.g 0) (hg2 : S.G.g2 = D.host.g 1) :
    0 < S.G.g ∧ 0 < S.G.v ∧ 0 < S.G.lenI := by
  have hc := (long_cut_num D large₂ h 0 le_rfl hCl).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv1, -⟩ := h
  have hp := g_pos D
  refine ⟨?_, ?_, ?_⟩
  · unfold Sz.Glob.g
    rw [hg1, hg2]
    exact mul_pos (by exact_mod_cast hp.1) (by exact_mod_cast hp.2)
  · rw [hv]; linarith
  · unfold Sz.Glob.lenI
    rw [hDel]
    have : (0 : ℝ) < 6 * (20 * ((D.R.rS : ℝ) + 1)) ^ 3 + 6 * (20 * ((D.R.rS : ℝ) + 1)) := by positivity
    linarith


end TransportedAlt

end Formalism.L2.SG.Pf.CarrierSz
