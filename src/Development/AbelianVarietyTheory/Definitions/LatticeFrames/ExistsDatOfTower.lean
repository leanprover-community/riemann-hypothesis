import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignature
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TowerIsChain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Model

variable {D : D7}

def reOm {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (h : IsWeilDatumO ψ S T χS χT om) (π : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (h₁ : ∀ f, IsThetaFunO ψ S T (π f)) (h₂ : ∀ f, IsThetaFunO ψ S T f → π f = f) : Om S T where
  toFun p := (om p) ∘ₗ π + (LinearMap.id - π)
  map_one' := by ext f w; simp
  map_mul' p q := by
    refine LinearMap.ext fun f => ?_
    have e1 : π (om q (π f)) = om q (π f) := h₂ _ (h.om_pres q _ (h₁ f))
    have e2 : π (π f) = π f := h₂ _ (h₁ f)
    simp [map_mul, e1, e2]





theorem exists_congr (S V : HSp D) (hS : S.SigOK) (hV : V.SigOK) (hr : S.rank = V.rank) (hs : ∀ τ, S.sig τ = V.sig τ) :
    ∃ M : Matrix (Fin V.rank) (Fin S.rank) D.host.E, Mᴴ * V.gram * M = S.gram := by
  obtain ⟨φ, hφ⟩ := GlobalTheory.RationalIsometry.rationalSt D S V hS hV hr hs
  refine ⟨Matrix.of fun a k => V.frame.repr (φ (S.frame k)) a, ?_⟩
  refine Matrix.ext fun k l => ?_
  have h : V.hT (φ (S.frame k)) (φ (S.frame l)) = S.gram k l := hφ _ _
  rw [← h]
  conv_rhs => rw [← V.frame.sum_repr (φ (S.frame k)), ← V.frame.sum_repr (φ (S.frame l))]
  simp only [Matrix.mul_apply, conjTranspose_apply, of_apply, HSpace.gram, map_sum,
    LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem block_frame_conjugation_identity {n k a b : Type} [Fintype n] [Fintype k] {E : Type} [CommRing E] [StarRing E] (M : Matrix n k E)
    (G : Matrix n n E) (x : Matrix k a E) (y : Matrix k b E) : (M * x)ᴴ * G * (M * y) = xᴴ * (Mᴴ * G * M) * y := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem nonempty_orthDec (V A B : HSp D) (hV : V.SigOK) (hA : A.SigOK) (hB : B.SigOK) (hr : A.rank + B.rank = V.rank)
    (hs : ∀ τ, A.sig τ + B.sig τ = V.sig τ) : Nonempty (OrthDec V A B) := by
  obtain ⟨M, hM⟩ := exists_congr (GlobalTheory.Doubling.hsum A B) V (GlobalTheory.Doubling.sigOK_hsum hA hB) hV hr hs
  let o := GlobalTheory.OrthSumExists.orthDecHsum D A B
  exact ⟨⟨M * o.iA, M * o.iB, by rw [block_frame_conjugation_identity, hM, o.isoA], by rw [block_frame_conjugation_identity, hM, o.isoB], by rw [block_frame_conjugation_identity, hM, o.orth], hr⟩⟩

theorem nonempty_hypDec (V A : HSp D) (ρ : ℕ) (hV : V.SigOK) (hA : A.SigOK) (hr : A.rank + 2 * ρ = V.rank)
    (hs : ∀ τ, A.sig τ + (ρ, ρ) = V.sig τ) : Nonempty (HypDec V A ρ) := by
  let P : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral ρ
  have hP : P.SigOK := Examples₂.posSpace_sigOK _ _
  obtain ⟨o⟩ := nonempty_orthDec V A (GlobalTheory.Doubling.dblSp P) hV hA (GlobalTheory.Doubling.sigOK_hdbl hP)
    (by rw [← hr]; show A.rank + (ρ + ρ) = _; omega)
    (fun τ => by rw [← hs τ]; show A.sig τ + ((ρ, 0) + (0, ρ)) = _; simp)
  let d : HypDec (GlobalTheory.Doubling.dblSp P) _ ρ := GlobalTheory.Core.Rk.SWLaw.dblDec P
  refine ⟨⟨o.iB * d.e, o.iB * d.e', o.iA, by rw [block_frame_conjugation_identity, o.isoB, d.ee], by rw [block_frame_conjugation_identity, o.isoB, d.e'e'],
    by rw [block_frame_conjugation_identity, o.isoB, d.e'e], o.isoA, ?_, ?_, hr⟩⟩
  · rw [← Matrix.mul_assoc, o.orth', Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, o.orth', Matrix.zero_mul]

theorem sigOK_negLine : (GlobalTheory.Doubling.hneg (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1)).SigOK :=
  GlobalTheory.Doubling.sigOK_hneg (Examples₂.posSpace_sigOK _ _)

abbrev nLine (D : D7) : HSp D := GlobalTheory.Doubling.hneg (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1)

theorem isLineVec_nLine {c : D.host.E} (hc : c ≠ 0) : IsLineVec (nLine D) (fun _ => c) := by
  refine ⟨rfl, ?_⟩
  have h : ∀ i j : Fin 1, (nLine D).gram i j = -1 := fun i j => by
    show -((Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0).gram i j) = -1
    rw [Examples₂.stdSpace_gram_apply, Subsingleton.elim i j]
    simp [Examples₂.sgn]
  change ∑ i : Fin 1, star c * ∑ j : Fin 1, (nLine D).gram i j * c ≠ 0
  simp [h, hc]

theorem rank_arith (R : Ranks) {j : ℕ} (h : j < R.m) : R.rankY j = R.N j + (R.m - 1 - j) := by
  have h4 : j * (R.t + 1) = j * R.t + j := by ring
  simp only [Ranks.N, Ranks.rankY, Ranks.r]
  omega

open GlobalTheory.ChainOnto (Com PiLocalization₂)

theorem exists_besAt {c : Com D} {s : PiLocalization₂ D} {j ρ : ℕ} (h : j + 2 * ρ + 2 = D.R.m) (hs : s.Is c j) :
    ∃ (d : HypDec s.V (GlobalTheory.Doubling.hsum (D.sp.X j) (nLine D)) ρ), Nonempty (VolN d) := by
  have h1 := D.sp.X_rank j (by omega)
  have h2 := hs.rank
  have h3 := rank_arith D.R (j := j) (by omega)
  obtain ⟨d⟩ := nonempty_hypDec s.V (GlobalTheory.Doubling.hsum (D.sp.X j) (nLine D)) ρ hs.sigOK
    (GlobalTheory.Doubling.sigOK_hsum (D.sp.X_sig j) sigOK_negLine) (by show (D.sp.X j).rank + 1 + 2 * ρ = _; omega) (fun τ => by
      show (D.sp.X j).sig τ + (0, 1) + (ρ, ρ) = _
      rw [hs.sig τ, D.X_posDef j (by omega) τ, sigYD]
      refine Prod.ext ?_ ?_ <;> simp <;> omega)
  exact ⟨d, GlobalTheory.Unf.Inhab.nonempty_volN d⟩

theorem nonempty_jacAt {c : Com D} {s : PiLocalization₂ D} {j ρ : ℕ} (h : j + 2 * ρ + 2 = D.R.m) (hs : s.Is c (j + 1)) :
    Nonempty (JacAt s.V (D.sp.X (j + 1)) ρ) := by
  have h1 := D.sp.X_rank (j + 1) (by omega)
  have h2 := hs.rank
  have h3 := rank_arith D.R (j := j + 1) (by omega)
  obtain ⟨d⟩ := nonempty_hypDec s.V (D.sp.X (j + 1)) ρ hs.sigOK (D.sp.X_sig _) (by omega) (fun τ => by
      rw [hs.sig τ, D.X_posDef (j + 1) (by omega) τ, sigYD]
      refine Prod.ext ?_ ?_ <;> simp <;> omega)
  exact ⟨⟨d, Inh.coCpt_of_isDefinite (D.sp.X_sig _) (D.sp.X_def _ (by omega)), (GlobalTheory.Unf.Inhab.nonempty_volN d).some⟩⟩

theorem nonempty_top (D : D7) (n : ℕ) (h : n = D.R.m) :
    Nonempty (OrthDec (D.sp.X n) D.sp.X' (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1)) := by
  subst h
  have h1 := D.sp.X_rank _ le_rfl
  have h2 := D.sp.X'_rank
  have h3 : D.R.N D.R.m = D.R.rankX' + 1 := by
    have h4 : D.R.m * (D.R.t + 1) = D.R.m * D.R.t + D.R.m := by ring
    have := D.R.two_le_m
    simp only [Ranks.N, Ranks.rankX', Ranks.r]
    omega
  refine nonempty_orthDec _ _ _ (D.sp.X_sig _) D.sp.X'_sig (Examples₂.posSpace_sigOK _ _) (by show _ + 1 = _; omega) fun τ => ?_
  show D.sp.X'.sig τ + (1, 0) = _
  rw [D.X'_posDef τ, D.X_posDef _ le_rfl τ]
  refine Prod.ext ?_ ?_ <;> simp <;> omega

theorem exists_step {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {a b : ℕ} (dV : HypDec V V₀ a) (dW : HypDec W W₀ b) (ρ σ : ℕ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) (vW : Vol W) :
    ∃ s : GlobalTheory.Unf.Step ψ V V₀ W W₀ ρ σ, s.om = om ∧ s.vW.μ = vW.μ ∧ s.vW.𝓕 = vW.𝓕 := by
  obtain ⟨om₀, h₀⟩ := GlobalTheory.Unf.Inhab.exists_weil h.std V₀ W₀ h.hecS h.hecT (resEta_parity h.resS (GlobalTheory.Unf.Inhab.even_im_hermitian_sub dV))
    (resEta_parity h.resT (GlobalTheory.Unf.Inhab.even_im_hermitian_sub dW))
  exact ⟨⟨χV, χW, om, om₀, h, h₀, vW, (GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some, (GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some,
    (GlobalTheory.Unf.Inhab.nonempty_volU D _).some⟩, rfl, rfl, rfl⟩

theorem exists_dat (g : Geo D) (u : D.what₂.Word) (p : ∀ j, GlobalTheory.ChainOnto.Step g.c (g.st j) (g.st (j + 1)))
    (pT : ∀ j, j + 2 * 0 + 2 = D.R.m → GlobalTheory.ChainOnto.Step g.c (g.st (j + 1)) g.top.st)
    (hc : g.c.Is) (hst : ∀ j, j < D.R.m → (g.st j).Is g.c j) (htop : g.top.st.Is g.c D.R.m)
    (hp : ∀ j, j + 1 < D.R.m → (p j).Is (j + 1)) (hpT : ∀ j h, (pT j h).Is D.R.m)
    (t : ∀ j, GA D (g.st j).V) (ht : ∀ j, t j ∈ GfC (g.st j).V) (Ram : ∀ j, Submodule ℂ (Col D u j))
    (S : ∀ j, Col D u j →ₗ[ℂ] Col D u j) (rd : ∀ j, Col D u j → (D.mem u).C.Y j → GA D (D.sp.X j) → ℂ)
    (eT : (D.mem u).P.Mt → g.top.st.CC g.c) :
    ∃ d : Dat D u, d.Base ∧ d.toGeo = g ∧ d.Ram = Ram ∧ d.S = S ∧ d.rd = rd ∧ HEq d.t t ∧ HEq d.eT eT ∧
      ∀ j, j < D.R.m → (d.k j).vac ≠ 0 ∧ (d.k j).c ≠ 0 := by
  have hx : ∀ j, ∃ x : DefSp (D.sp.X j), j ≤ D.R.m → x.Is := fun j => by
    by_cases hj : j ≤ D.R.m
    · exact (Inh.exists_defSp_X D j hj).imp fun _ h _ => h
    · exact ⟨⟨0, 0, ⊥, (GlobalTheory.Unf.Inhab.nonempty_vol _).some⟩, fun h => absurd h hj⟩
  choose x hx using hx
  have hk : ∀ j, ∃ k : KerDat (D.sp.X j) (D.sp.X (j + 1)), j < D.R.m →
      k.Is g.c.ψ g.c.θ (x j) (x (j + 1)) ∧ k.vac ≠ 0 ∧ k.c ≠ 0 := fun j => by
    by_cases hj : j < D.R.m
    · obtain ⟨k, h1, h2, h3⟩ := Inh.exists_kerDat hc.std hc.inf (hx j hj.le) (hx (j + 1) hj)
      exact ⟨k, fun _ => ⟨h1, h2, h3 ▸ Finsupp.single_ne_zero.2 one_ne_zero⟩⟩
    · exact ⟨⟨1, 0, 0⟩, fun h => absurd h hj⟩
  choose k hk using hk
  have hξ := GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D
  choose dB vB using fun j ρ (h : j + 2 * ρ + 2 = D.R.m) => exists_besAt h (hst j (by omega))
  let bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (g.st j).V (D.sp.X j) ρ := fun j ρ h =>
    ⟨_, nLine D, dB j ρ h, GlobalTheory.OrthSumExists.orthDecHsum D _ _, fun _ => D.host.xi0 ^ ρ, isLineVec_nLine (pow_ne_zero _ hξ),
      (hx j (by omega)).cpt, (vB j ρ h).some⟩
  let jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt (g.st (j + 1)).V (D.sp.X (j + 1)) ρ := fun j ρ h =>
    (nonempty_jacAt h (hst (j + 1) (by omega))).some
  choose sBF hBF using fun j ρ (h : j + 2 * ρ + 2 = D.R.m) => exists_step (bes j ρ h).d (jac j ρ h).d ρ ρ (hp j (by omega)).weil
    ⟨_, _, (hst (j + 1) (by omega)).haar, (hst (j + 1) (by omega)).fund⟩
  choose sFB hFB using fun j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) => exists_step (jac j (σ + 1) h).d
    (bes (j + 1 + 1) σ (idx_step h)).d (σ + 1) σ (hp (j + 1) (by omega)).weil
    ⟨_, _, (hst (j + 1 + 1) (by omega)).haar, (hst (j + 1 + 1) (by omega)).fund⟩
  have lnk : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), Link ((bes j (σ + 1) h).lev (x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L
      (bes (j + 1 + 1) σ (idx_step h)).ζ := fun j σ h => by
    have e : D.host.xi0⁻¹ • ((bes j (σ + 1) h).lev (x j).vol).ζ = (bes (j + 1 + 1) σ (idx_step h)).ζ :=
      funext fun _ => by
        show D.host.xi0⁻¹ * D.host.xi0 ^ (σ + 1) = D.host.xi0 ^ σ
        rw [pow_succ', inv_mul_cancel_left₀ hξ]
    exact e ▸ GlobalTheory.Unf.Inhab.selfLink _
  exact ⟨{ toGeo := g, p := p, pT := pT, t := t, x := x, k := k, bes := bes, jac := jac, sBF := sBF, sFB := sFB, lnk := lnk,
           vL := fun _ _ _ => (GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some, Lz := _, oT := fun n h => (nonempty_top D n h).some,
           Ram := Ram, S := S, rd := rd, eT := eT },
    ⟨hc, hst, htop, hp, hpT, ht, hx, fun j hj => (hk j hj).1, hBF, hFB⟩, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl,
    fun j hj => (hk j hj).2⟩

theorem exists_stAt (s : PiLocalization₂ D) (V : HSp D) (h : s.V = V) : ∃ a : StAt V, a.st = s := by
  subst h; exact ⟨Inh.stOf s, rfl⟩

theorem step_cast {c : Com D} {s₁ s₂ s₁' s₂' : PiLocalization₂ D} (h₁ : s₁ = s₁') (h₂ : s₂ = s₂') (p : GlobalTheory.ChainOnto.Step c s₁ s₂) :
    ∃ p' : GlobalTheory.ChainOnto.Step c s₁' s₂', ∀ j, p.Is j → p'.Is j := by
  subst h₁ h₂; exact ⟨p, fun _ h => h⟩

open GlobalTheory.ChainOnto in

theorem exists_dat_of_tower (W : GlobalTheory.Core.Rk.Tower D) (hW : W.Is) (u : D.what₂.Word) (Ram : ∀ j, Submodule ℂ (Col D u j))
    (S : ∀ j, Col D u j →ₗ[ℂ] Col D u j) (rd : ∀ j, Col D u j → (D.mem u).C.Y j → GA D (D.sp.X j) → ℂ) :
    ∃ d : Dat D u, d.Base ∧ d.c = comOf W ∧ (∀ j, d.st j = stageY W j) ∧ d.top.st = stageX W ∧ d.Ram = Ram ∧ d.S = S ∧ d.rd = rd ∧
      ∀ j, j < D.R.m → (d.k j).vac ≠ 0 ∧ (d.k j).c ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.TowerChain.tower_isChain D W hW
  obtain ⟨bot, hb⟩ := exists_stAt (stageY W 0) (D.sp.Y 0) (congrArg D.sp.Y (Nat.zero_min _))
  let g : Geo D := ⟨comOf W, bot, fun j => stageY W (j + 1), Inh.stOf (stageX W)⟩
  have hg : ∀ j, stageY W j = g.st j := fun j => by
    cases j with
    | zero => exact hb.symm
    | succ j => rfl
  choose p hp using fun j => step_cast (hg j) (hg (j + 1)) (stepY W j)
  choose pT hpT using fun j (h : j + 2 * 0 + 2 = D.R.m) =>
    step_cast ((congrArg (stageY W) (by omega : D.R.m - 1 = j + 1)).trans (hg (j + 1))) (rfl : stageX W = g.top.st) (stepX W)
  obtain ⟨d, hd, e, a1, a2, a3, -, -, a4⟩ := exists_dat g u p pT h1 (fun j hj => hg j ▸ h2 j hj) h3
    (fun j hj => hp j _ (h4 j hj)) (fun j h => hpT j h _ h5) (fun _ => 1) (fun _ => one_mem _) Ram S rd (fun _ => 0)
  refine ⟨d, hd, ?_, fun j => ?_, ?_, a1, a2, a3, a4⟩
  · show d.toGeo.c = _; rw [e]
  · show d.toGeo.st j = _; rw [e, hg]
  · show d.toGeo.top.st = _; rw [e]; rfl



end GlobalTheory.SeeSaw.Model

end
