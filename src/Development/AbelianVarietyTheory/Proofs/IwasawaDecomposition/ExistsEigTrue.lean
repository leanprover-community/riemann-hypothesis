import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotExistsExponentConditionCard
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GalPolLiftsOfSplit

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspFrobSplit

theorem esymm_map_mul_const (s : Multiset ℂ) (c : ℂ) (k : ℕ) :
    (s.map (fun x => x * c)).esymm k = c ^ k * s.esymm k := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  congr 1
  refine Multiset.map_congr rfl fun t ht => ?_
  have hk : Multiset.card t = k := (Multiset.mem_powersetCard.1 ht).2
  simp only [Function.comp_apply, Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const',
    Multiset.prod_replicate, hk]
  ring

theorem galPol_lifts_ae : ∀ (D : D7) (cf : CharFrame D) (Rw : GlobalTheory.HeightCounting.RowSide D) (Sb : Finset (PlE D.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0), ValLL0 D cf → GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∀ π : D.naut.CG D.R.r, D.naut.csd π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w) → ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D) := by
  intro D cf Rw Sb eig hV hE j hj1 hj2 σ hiso hgood π hcsd hloc
  obtain ⟨bar, hinj, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  let j' : Fin D.R.m := ⟨j - 1, by omega⟩
  have hjj : (j' : ℕ) + 1 = j := by simp only [j']; omega
  have hfin : (bar ⁻¹' ((Sb : Set (PlE D.host)) ∪ {v | ¬ (cf.mu0 j').UnrAt v})).Finite :=
    (Sb.finite_toSet.union (GlobalTheory.Mem.UnrAe.finite_ramified _)).preimage hinj.injOn
  refine Filter.eventually_cofinite.2 (hfin.subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  by_contra hw'
  apply hw
  intro hsplit
  simp only [Set.mem_preimage, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hw'
  obtain ⟨hSb, hunrμ⟩ := hw'
  obtain ⟨hc, -, hsp⟩ := hbar w
  have hPs : IsSplitPl D.host (bar w) := hsp hsplit
  have hE' := hE j' σ (by rw [hjj]; exact hiso) hgood (bar w) hPs hSb
  rw [hjj] at hE'
  obtain ⟨hunrP, heig⟩ := hE'
  rw [← hloc (bar w) hPs] at hunrP heig
  obtain ⟨hunrw, hfw⟩ := D.naut.csd_unr π (bar w) w hcsd (GlobalTheory.ToricDenomCheck.isConj_symm hc) hunrP
  have hfP : D.naut.frobEig (D.naut.locG π (bar w)) =
      (D.naut.frobEig (D.naut.locG π w)).map (fun x => x⁻¹) := by
    rw [hfw, Multiset.map_map]; simp
  have hcard : (D.naut.frobEig (D.naut.locG π w)).card = D.R.r := by
    rw [D.naut.frobEig_card _ hunrw, D.naut.locG_dim]
  have hmemS : ∀ x, x ∈ (embLL0 D).fieldRange → x ∈ Set.range (embLL0 D) :=
    fun x h => (RingHom.mem_fieldRange).1 h
  have hNS : ∀ n : ℕ, (n : ℂ) ∈ (embLL0 D).fieldRange := fun n => natCast_mem _ n
  have hN0 : (Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ≠ 0 := by exact_mod_cast GlobalTheory.ConjPoly.normV_ne_zero (bar w)
  have hμ0 : (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  obtain ⟨yμ, hyμ⟩ := hV.mu0 j' (bar w) hunrμ
  have hμS : (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ) ∈ (embLL0 D).fieldRange :=
    ⟨yμ, by rw [hyμ]; simp [Formalism.L2.Host.HChar.valTw]⟩
  have hAk : ∀ k, 1 ≤ k → k ≤ D.R.r →
      (D.naut.frobEig (D.naut.locG π w)).esymm k ∈ (embLL0 D).fieldRange := by
    intro k hk1 hk2
    have h := heig k hk1 hk2
    rw [hfP, Multiset.map_map] at h
    have hfun : (fun a : ℂ => a⁻¹ * (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
          ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ∘ (fun x : ℂ => x⁻¹) =
        fun x => x * ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
          ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) := by
      funext x; simp [mul_assoc]
    rw [hfun, esymm_map_mul_const] at h
    have hd : ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
        ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ≠ 0 := by
      simp [hμ0, hN0]
    have hdS : ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
        ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ∈ (embLL0 D).fieldRange :=
      Subfield.mul_mem _ (Subfield.inv_mem _ hμS) (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _))
    have hpow : ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (k * (D.R.r - k) / 2)) ≠ 0 := pow_ne_zero _ hN0
    have heq : (D.naut.frobEig (D.naut.locG π w)).esymm k =
        D.what₂.embLL ↑(eig j σ k (bar w)) * ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (k * (D.R.r - k) / 2))⁻¹ *
          (((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
            ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ^ k)⁻¹ := by
      rw [h]; field_simp
    rw [heq]
    refine Subfield.mul_mem _ (Subfield.mul_mem _ ⟨eig j σ k (bar w), rfl⟩
      (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _))) (Subfield.inv_mem _ (Subfield.pow_mem _ hdS _))
  have hr : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by simp only [Formalism.BasicNotions.Ranks.r]; omega⟩
  obtain ⟨q, hq⟩ := hr
  have hs : ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ^ ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) =
      ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹ := by
    have : ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) = -(q : ℂ) := by
      rw [hq]; push_cast; ring
    rw [this, Complex.cpow_neg, Complex.cpow_natCast]
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  unfold Formalism.MainNotions.N.galPol
  rw [D.naut.frobEig_tw _ _ hunrw, hs]
  have hBk : ∀ k, k ≤ D.R.r →
      ((D.naut.frobEig (D.naut.locG π w)).map (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)).esymm k ∈
        (embLL0 D).fieldRange := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have : Multiset.esymm ((D.naut.frobEig (D.naut.locG π w)).map (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)) 0 = 1 := by
        simp [Multiset.esymm, Multiset.powersetCard_zero_left]
      rw [this]; exact Subfield.one_mem _
    rw [esymm_map_mul_const]
    exact Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _)) _)
      (hAk k hk1 hk)
  have hBc : ((D.naut.frobEig (D.naut.locG π w)).map
      (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)).card = D.R.r := by
    rw [Multiset.card_map, hcard]
  rcases le_or_gt n D.R.r with hn | hn
  · rw [Multiset.prod_X_sub_C_coeff _ (hBc.symm ▸ hn), hBc]
    exact hmemS _ (Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.neg_mem _ (Subfield.one_mem _)) _)
      (hBk _ (by omega)))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hBc]; exact hn)]
    exact ⟨0, map_zero _⟩

end GlobalTheory.CuspFrobSplit
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistLift

open Polynomial

theorem prod_X_sub_C_scale_mem_lifts {K : Type} [Field K] (f : K →+* ℂ) (M : Multiset ℂ) (y : K)
    (hy : f y ≠ 0) (h : (M.map (fun α => X - C α)).prod ∈ Polynomial.lifts f) :
    ((M.map (fun x => x * f y)).map (fun α => X - C α)).prod ∈ Polynomial.lifts f := by
  set q : ℂ[X] := C (f y)⁻¹ * X with hq
  have key : ((M.map (fun x => x * f y)).map (fun α => X - C α)).prod =
      C (f y) ^ Multiset.card M * ((M.map (fun α => X - C α)).prod).comp q := by
    clear h
    induction M using Multiset.induction_on with
    | empty => simp
    | cons a M ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, ih, mul_comp]
      have e1 : (X - C a).comp q = C (f y)⁻¹ * X - C a := by simp [hq]
      have e2 : X - C (a * f y) = C (f y) * (C (f y)⁻¹ * X - C a) := by
        rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hy, C_1, one_mul, ← C_mul, mul_comm (f y) a]
      rw [e1, e2]; ring
  rw [key]
  refine mul_mem (pow_mem (Polynomial.C_mem_lifts f y) _) ?_
  rw [Polynomial.lifts_iff_set_range] at h ⊢
  obtain ⟨p, hp⟩ := h
  refine ⟨p.comp (C y⁻¹ * X), ?_⟩
  rw [Polynomial.map_comp, hp, hq]
  simp [map_inv₀]

end GlobalTheory.TwistLift

namespace GlobalTheory.TwistLift

open Polynomial

theorem galPol_lifts_tw_etaTinv : ∀ (D : D7) (cf : CharFrame D), GlobalTheory.HeightCounting.CharSide D cf → ValLL0 D cf → ∀ π : D.naut.CG D.R.r, (∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D)) → ∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D) := by
  intro D cf hC hV π hπ
  obtain ⟨k, hk⟩ := D.R.t_odd
  filter_upwards [hπ, D.naut.locG_unr_ae π] with w hw hu
  have hUe : cf.eta.UnrAt w := by
    have h1 := (hC.unr_iff D.naut.etaT w).1 (D.naut.etaT_unr w)
    rwa [hC.etaT] at h1
  have hFe : D.naut.frobEig (D.naut.locG D.naut.etaT w) = {((cf.eta.val w : ℂ))⁻¹} := by
    have h1 := hC.frob D.naut.etaT w (by rw [hC.etaT]; exact hUe)
    rw [h1, hC.etaT]; simp
  have hFi : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {(cf.eta.val w : ℂ)} := by
    rw [(D.naut.etaTinv_def w).2, hFe]; simp
  have hUi : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hD1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  obtain ⟨y, hy⟩ := hV.eta w hUe
  have hNv : Formalism.ConjugateSelfDual.normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hN : ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ≠ 0 := by
    rw [hNv, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  set N : ℂ := ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) with hNdef
  set lam : D.LL0 := y * (((Formalism.ConjugateSelfDual.normV w : ℕ) : D.LL0) ^ k)⁻¹ with hlamdef
  have hlam : embLL0 D lam = (cf.eta.val w : ℂ) * N ^ (-(1 / 2 : ℂ)) * (N ^ k)⁻¹ := by
    rw [hlamdef, map_mul, map_inv₀, map_pow, map_natCast, hy, Formalism.L2.Host.HChar.valTw, hNdef, hNv]
    push_cast; ring
  have hlam0 : embLL0 D lam ≠ 0 := by
    rw [hlam]
    refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) (inv_ne_zero (pow_ne_zero _ hN))
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hmul : D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2)) =
      (D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map (fun x => x * embLL0 D lam) := by
    rw [D.naut.locG_tw, D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hD1 hu hUi),
      D.naut.frobEig_char _ _ _ hu hUi hD1 hFi, D.naut.frobEig_tw _ _ hu, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun x _ => ?_)
    simp only [Function.comp_apply]
    have hs : (((1 - (D.R.nV : ℝ)) / 2 : ℝ) : ℂ) = (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) + (-(1 / 2 : ℂ)) + (-(k : ℂ)) := by
      have e : D.R.nV = D.R.r + D.R.t := rfl
      rw [e, hk]; push_cast; ring
    rw [hlam, ← hNdef, hs, Complex.cpow_add _ _ hN, Complex.cpow_add _ _ hN, Complex.cpow_neg (x := N) (y := (k : ℂ)),
      Complex.cpow_natCast]
    ring
  have hw' := hw
  simp only [galPol] at hw' ⊢
  rw [hmul]
  exact prod_X_sub_C_scale_mem_lifts (embLL0 D) _ lam hlam0 hw'

end GlobalTheory.TwistLift
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SCuspRows

theorem allSt_and' {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h1 : AllSt p) (h2 : AllSt q) : AllSt fun K B f T w P x => p K B f T w P x ∧ q K B f T w P x :=
  EvG.imp (Step.and h1 h2) fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => ⟨(G a b c).1 w hw P x, (G a b c).2 w hw P x⟩

theorem allSt_mono' {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h : AllSt p) (hq : ∀ K B f T w P x, p K B f T w P x → q K B f T w P x) : AllSt q :=
  EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => hq _ _ _ _ _ _ _ (G a b c w hw P x)

set_option maxHeartbeats 1000000 in

theorem exists_eigTrue {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (l : LA hL x) (n : InRat x.r.Y x.m.z.cG) :
    ∃ Sb, GlobalTheory.TwInputs.EigTrue (Dof x) (cfOf x) l.a.A.row Sb n.In.eig := by
  obtain ⟨Sb, h1, h2, -⟩ := GlobalTheory.TwInputs.Eig.exists_low (ι := Empty) n.In.Sb (fun i => i.elim) (fun i => i.elim) fun i => i.elim
  have h := GlobalTheory.TwInputs.Eig.eigTrue hL x.r.Y x.m.z.lev.is l.a.A.wdT l.a.A.row l.a.row n.rat.eig h1 h2
  have hC : x.m.z.R.C = cfOf x := x.m.z.lev.C
  exact ⟨Sb, (congrArg (fun c : CharFrame (Dof x) => GlobalTheory.TwInputs.EigTrue (Dof x) c l.a.A.row Sb n.In.eig) hC).mp h⟩

theorem sCusp_of_parSt : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ParSt hL → SRat hL → SCusp hL := by
  intro hP hL hPar hRat
  refine allSt_mono' (allSt_and' (allSt_and' hPar hRat) (valLL0_allSt hP)) ?_
  rintro K B f T w P x ⟨⟨hp, he⟩, hv⟩ l j hj1 hj2 σ hσ hg
  obtain ⟨π, hc, hr, hs, -, -, -⟩ := hp l j hj1 hj2 σ hσ hg
  obtain ⟨n⟩ := he l
  obtain ⟨Sb, hn⟩ := exists_eigTrue l n
  refine ⟨π, hc, hr, hs, ?_⟩
  have h2 := GlobalTheory.CuspFrobSplit.galPol_lifts_ae (Dof x) (cfOf x) l.a.A.row Sb n.In.eig hv hn j hj1 hj2 σ hσ hg π hc hs
  have h4 := GlobalTheory.GalAllPlaces.galPol_lifts_of_split hL hP.what₂.fin hP.what₂.gal hP.what₂.cheb (Dof x) l.a.A.wdT l.a.cg _ (embLL0 (Dof x)) π hc hr h2
  exact (GlobalTheory.TwistLift.galPol_lifts_tw_etaTinv (Dof x) (cfOf x) l.a.A.chr hv π h4).mono fun w hw => (Polynomial.mem_lifts _).1 hw

end GlobalTheory.SCuspRows
end
