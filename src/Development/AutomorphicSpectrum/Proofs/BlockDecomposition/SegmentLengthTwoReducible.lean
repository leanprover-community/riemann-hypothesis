import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingTwistedModulus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMirabolicInvariantPairingScalar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgCommutationHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgRankZeroHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGenericStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivariantFunctionalsEqDualAnnihilator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipBEqUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFilterSuperdiag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedEqFixedVectors
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import GroundTheory.AutomorphicForms.ContragredientTranspose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairIterPhiMir
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestDerivativeOfProduct
import BuildAid.D3

section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_pg_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG k := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.phiPG | exact GlobalTheory.CompanionTheory.BZPhiPG.phiPG | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.phiPG <;> assumption)
end

section
section
noncomputable section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZShellOpen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.CompanionTheory.LeibOrd.Main in

theorem gp_iter (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) :
    ∀ (j n m : ℕ) (ρ : GRep k m) (τ : MRep k (n + j)) (N : ℕ) (hN : m + n = N) (h : m + (n + j) = N + j),
      IsSmooth ρ.ρ → IsSmooth τ.ρ →
        MIso (iterN ψ j (mcast h (prodGPn ρ τ))) (mcast hN (prodGPn ρ (iterN ψ j τ))) := by
  intro j
  induction j with
  | zero =>
    intro n m ρ τ N hN h hρ hτ
    subst hN
    exact miso_refl _
  | succ j ih =>
    intro n m ρ τ N hN h hρ hτ
    subst hN
    have h2 : m + (n + (j + 1)) = (m + (n + j)) + 1 := by omega
    have e : m + (n + j) = (m + n) + j := by omega
    have s1 := GlobalTheory.CompanionTheory.LeibPhi.phiGP k ψ hc h1 m (n + j) ρ τ hρ hτ
    have s2 : MIso (phiN ψ (mcast h (prodGPn ρ τ))) (mcast e (prodGPn ρ (phiN ψ τ))) := by
      rw [phiN_mcast ψ _ h h2 e]
      exact miso_mcast e s1
    exact miso_trans (miso_iterN ψ j s2) (ih n m ρ (phiN ψ τ) _ rfl e hρ (isSmooth_phiN ψ hτ))

theorem subsingleton_cInd {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) [Subsingleton W] : Subsingleton (cIndSpace H σ) := by
  refine ⟨fun f f' => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact Subsingleton.elim _ _

theorem subsingleton_prodGPn {m j : ℕ} (ρ : GRep k m) (τ : MRep k j) (h : Subsingleton ρ.V) :
    Subsingleton (prodGPn ρ τ).V := by
  haveI : Subsingleton ((ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).V ⊗[ℂ] (mtw τ (-((m : ℕ) : ℝ) / 2)).V) := by
    haveI : Subsingleton (ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).V := h
    refine ⟨fun x y => ?_⟩
    have key : ∀ z : (ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).V ⊗[ℂ] (mtw τ (-((m : ℕ) : ℝ) / 2)).V, z = 0 := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
      | add a b ha hb => rw [ha, hb, add_zero]
    rw [key x, key y]
  exact subsingleton_cInd _ _

open GlobalTheory.CompanionTheory.LeibOrd.Main in

theorem pg_iter (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) :
    ∀ (j n t : ℕ) (τ : MRep k (n + j)) (σ : GRep k (t + 1)) (N : ℕ) (hN : n + (t + 1) = N)
      (h : (n + j) + (t + 1) = N + j), IsSmooth τ.ρ → IsSmooth σ.ρ →
      (∀ (i n' : ℕ) (e : n + j = n' + i), i < j → Subsingleton (dN ψ i (mcast e τ)).V) →
        MIso (iterN ψ j (mcast h (prodPGn τ σ))) (mcast hN (prodPGn (iterN ψ j τ) σ)) := by
  intro j
  induction j with
  | zero =>
    intro n t τ σ N hN h hτ hσ _
    subst hN
    exact miso_refl _
  | succ j ih =>
    intro n t τ σ N hN h hτ hσ hv
    subst hN
    have e : (n + j) + (t + 1) = (n + (t + 1)) + j := by omega
    have h2 : (n + j + 1) + (t + 1) = ((n + j) + t + 1) + 1 := by omega
    have e0 : (n + j) + t + 1 = (n + (t + 1)) + j := by omega
    have hext := GlobalTheory.T.phi_pg_commutation_holds k ψ hc h1 (n + j) t τ σ hτ hσ
    have hz : Subsingleton (psiN τ).V := hv 0 (n + (j + 1)) rfl (by omega)
    haveI : Subsingleton (mcast (by omega : (n + j + 1) + t = (n + j) + t + 1) (prodGPn (psiN τ) (gres σ))).V :=
      subsingleton_mcast _ (subsingleton_prodGPn _ _ hz)
    obtain ⟨q⟩ := equiv_of_ses_zero (ses_of_mext hext)
    have s2 : MIso (phiN ψ (mcast h (prodPGn τ σ))) (mcast e (prodPGn (phiN ψ τ) σ)) := by
      rw [phiN_mcast ψ _ h h2 e0]
      have := miso_mcast e0 (miso_symm (⟨q⟩ : MIso _ _))
      rwa [mcast_mcast] at this
    refine miso_trans (miso_iterN ψ j s2) (ih n t (phiN ψ τ) σ _ rfl e (isSmooth_phiN ψ hτ) hσ ?_)
    intro i n' e' hi
    have e'' : n + (j + 1) = n' + (i + 1) := by omega
    have h3 : Subsingleton (dN ψ i (phiN ψ (mcast e'' τ))).V := hv (i + 1) n' e'' (by omega)
    rwa [phiN_mcast ψ τ e'' rfl e'] at h3

open GlobalTheory.CompanionTheory.LeibOrd.DerivTw in

theorem dN_equiv (ψ : AddChar k Circle) {n : ℕ} (j : ℕ) (τ : MRep k (n + j)) :
    Nonempty ((dN ψ j τ).V ≃ₗ[ℂ] TwJacquet τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)) := by
  obtain ⟨e1⟩ := giso_psiG (iterN_iso ψ j τ)
  obtain ⟨e2⟩ := psiG_mtw (iterPhi k ψ j τ) (-(j : ℝ) / 2)
  obtain ⟨e3⟩ := GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv k ψ n j τ
  exact ⟨(e1.toLinearEquiv.trans e2.toLinearEquiv).trans e3⟩

theorem dN_gres_vanish (ψ : AddChar k Circle) {p : ℕ} (π : GRep k (p + 1)) (hcu : IsCuspidal π.ρ) (i n' : ℕ)
    (e : p = n' + i) (hn : 0 < n') : Subsingleton (dN ψ i (mcast e (gres π))).V := by
  subst e
  obtain ⟨q⟩ := dN_equiv ψ i (gres π)
  have h : twKer (gres π).ρ (derUnipM k (n' + i) n') (derCharM k ψ (n' + i) n') = ⊤ :=
    (GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM k ψ (n' + i) n' π.V π.ρ).trans
      (GlobalTheory.T.cuspidal_twisted_kernel_top k ψ _ _ _ π.ρ hcu hn (by omega))
  haveI : Subsingleton (TwJacquet (gres π).ρ (derUnipM k (n' + i) n') (derCharM k ψ (n' + i) n')) :=
    Submodule.Quotient.subsingleton_iff.2 h
  exact q.toEquiv.subsingleton

theorem subsingleton_mir_zero : Subsingleton (Mir k 0) := by
  refine ⟨fun a b => Subtype.ext (Units.ext ?_)⟩
  have ha := (mem_Mir_iff k _).1 a.2
  have hb := (mem_Mir_iff k _).1 b.2
  ext i j
  obtain rfl : i = Fin.last 0 := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
  exact congrFun (ha.trans hb.symm) j

open GlobalTheory.LocGL GlobalTheory.BZSeg

theorem rank_functionals_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {N N' : Subgroup G} (h : N = N') (χ : N → ℂ) (χ' : N' → ℂ)
    (hχ : ∀ u : N, χ u = χ' ⟨u, h ▸ u.2⟩) :
    Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ χ) =
      Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ χ') := by
  subst h
  have : χ = χ' := funext fun u => hχ u
  rw [this]

theorem whit_rank_le (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (N : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  have hadm : GroundTheory.Automorphic.IsAdmissible π :=
    (GlobalTheory.CompanionTheory.AdmDict.isAdmissible_iff π).1 (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k N V π hs hi)
  have hc0 : Continuous (Circle.coeHom.compAddChar ψ) := continuous_subtype_val.comp hc
  have h10 : Circle.coeHom.compAddChar ψ ≠ 1 := by
    intro h
    apply h1
    ext x
    have h2 : Circle.coeHom (ψ x) = 1 := by simpa using DFunLike.congr_fun h x
    have h3 : ((ψ x : Circle) : ℂ) = 1 := h2
    simpa using h3
  haveI := hi
  have hle := GroundTheory.Automorphic.ContragredientTranspose.rank_whittaker_le_one
    (Circle.coeHom.compAddChar ψ) hc0 h10 π hadm
  rw [GlobalTheory.CompanionTheory.TwistedDual.rank_twJacquet_le_one_iff]
  rw [rank_functionals_congr π (GlobalTheory.CompanionTheory.IwasawaDict.unipB_eq_unipotent k N) _
    (fun u => GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin N) k))
    (fun u => GlobalTheory.CompanionTheory.WhitDict.whitChar_eq_psiN k ψ N u)]
  exact hle

theorem finrank_whit (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {p : ℕ} (π : GRep k (p + 1))
    (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) (hcu : IsCuspidal π.ρ) :
    Module.finrank ℂ (TwJacquet π.ρ (unipB k (Fin (p + 1))) (whitChar ψ (p + 1))) = 1 := by
  have hV : Nontrivial π.V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    obtain ⟨a, b, hab⟩ := hi.toNontrivial.exists_pair_ne
    apply hab
    ext x
    simp [Subsingleton.elim x 0]
  have hg : IsGenericFor ψ π.ρ := GlobalTheory.T.cuspidal_is_generic k ψ hc h1 p _ π.ρ hcu hV
  have hle := whit_rank_le ψ hc h1 (p + 1) π.ρ hs hi
  haveI : Nontrivial (TwJacquet π.ρ (unipB k (Fin (p + 1))) (whitChar ψ (p + 1))) := hg
  exact Module.finrank_eq_of_rank_eq (le_antisymm hle (Cardinal.one_le_iff_pos.2 rank_pos))

theorem finrank_iterN (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {m : ℕ} (π : GRep k (0 + m + 1))
    (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) (hcu : IsCuspidal π.ρ) :
    Module.finrank ℂ (iterN ψ m (gres π)).V = 1 := by
  obtain ⟨q⟩ := dN_equiv ψ m (gres π)
  have hb : twKer (iterN ψ m (gres π)).ρ (MirUin k 0) 1 = ⊥ := by
    haveI := subsingleton_mir_zero (k := k)
    unfold twKer
    rw [Submodule.span_eq_bot]
    rintro w ⟨u, v, rfl⟩
    have hu : (u : Mir k 0) = 1 := Subsingleton.elim _ _
    have hu' : u = 1 := Subtype.ext hu
    subst hu'
    simp
  have hk : twKer (gres π).ρ (derUnipM k (0 + m) 0) (derCharM k ψ (0 + m) 0) =
      twKer π.ρ (unipB k (Fin (0 + m + 1))) (whitChar ψ (0 + m + 1)) :=
    (GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM k ψ (0 + m) 0 π.V π.ρ).trans
      (GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero (k := k) ψ (0 + m + 1) π.V π.ρ)
  have e1 : (iterN ψ m (gres π)).V ≃ₗ[ℂ] (dN ψ m (gres π)).V := (Submodule.quotEquivOfEqBot _ hb).symm
  have e3 : TwJacquet (gres π).ρ (derUnipM k (0 + m) 0) (derCharM k ψ (0 + m) 0) ≃ₗ[ℂ]
      TwJacquet π.ρ (unipB k (Fin (0 + m + 1))) (whitChar ψ (0 + m + 1)) := Submodule.quotEquivOfEq (M := π.V) _ _ hk
  rw [e1.finrank_eq, q.finrank_eq, e3.finrank_eq]
  exact finrank_whit ψ hc h1 π hs hi hcu

def glCast {a b : ℕ} (c : a = b) (g : GL (Fin a) k) : GL (Fin b) k := c ▸ g

theorem glCast_apply {a b : ℕ} (c : a = b) (g : GL (Fin a) k) (i j : Fin b) :
    (glCast c g : GL (Fin b) k).val i j = g.val (Fin.cast c.symm i) (Fin.cast c.symm j) := by
  subst c; rfl

theorem glCast_glCast {a b : ℕ} (c : a = b) (g : GL (Fin b) k) : glCast c (glCast c.symm g) = g := by
  subst c; rfl

open GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi GlobalTheory.CompanionTheory.BZOnto.PerpSmall

theorem isOpen_shiftBall (n : ℕ) (s : kˣ) (p : Fin n → k) :
    IsOpen {v : Fin n → k | Multiplicative.ofAdd (v - p) ∈ polyBall (k := k) n s} :=
  (isOpen_polyBall n s).preimage (continuous_ofAdd.comp (continuous_id.sub continuous_const))

theorem exists_period {n : ℕ} {E : Type} [AddCommGroup E] (φ : (Fin n → k) → E) (hl : IsLocallyConstant φ)
    (hK : HasCompactSupport φ) :
    ∃ s : kˣ, ∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v := by
  have hloc : ∀ p : Fin n → k, ∃ s : kˣ, ∀ a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s →
      φ (p + a) = φ p := by
    intro p
    have hU : (fun x : Multiplicative (Fin n → k) => p + Multiplicative.toAdd x) ⁻¹' (φ ⁻¹' {φ p}) ∈
        nhds (1 : Multiplicative (Fin n → k)) := by
      refine ((hl.isOpen_fiber (φ p)).preimage
        (continuous_const.add continuous_toAdd)).mem_nhds ?_
      simp
    obtain ⟨s, hs⟩ := exists_polyBall_subset hU
    exact ⟨s, fun a ha => hs ha⟩
  choose sp hsp using hloc
  obtain ⟨t, ht⟩ := hK.isCompact.elim_finite_subcover
    (fun p : Fin n → k => {v : Fin n → k | Multiplicative.ofAdd (v - p) ∈ polyBall (k := k) n (sp p)})
    (fun p => isOpen_shiftBall n (sp p) p)
    (fun v _ => Set.mem_iUnion.2 ⟨v, by simp [sub_self, one_mem]⟩)
  have hcom : ∀ t : Finset (Fin n → k), ∃ s : kˣ, ∀ p ∈ t, polyBall (k := k) n s ≤ polyBall n (sp p) := by
    intro t
    classical
    induction t using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | insert a t _ ih =>
      obtain ⟨S, hS⟩ := ih
      obtain ⟨s, h1, h2⟩ := exists_common n S (sp a)
      refine ⟨s, fun p hp => ?_⟩
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact h2
      · exact h1.trans (hS p hp)
  obtain ⟨s, hs⟩ := hcom t
  have key : ∀ v ∈ tsupport φ, ∀ a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v := by
    intro v hv a ha
    obtain ⟨p, hp, hvp⟩ : ∃ p ∈ t, Multiplicative.ofAdd (v - p) ∈ polyBall (k := k) n (sp p) := by
      have := ht hv
      simp only [Set.mem_iUnion] at this
      obtain ⟨p, hp, h⟩ := this
      exact ⟨p, hp, h⟩
    have h2 : Multiplicative.ofAdd (v + a - p) ∈ polyBall (k := k) n (sp p) := by
      have := mul_mem hvp (hs p hp ha)
      rw [← ofAdd_add] at this
      rwa [show v - p + a = v + a - p by abel] at this
    have e1 := hsp p _ hvp
    have e2 := hsp p _ h2
    rw [show p + (v - p) = v by abel] at e1
    rw [show p + (v + a - p) = v + a by abel] at e2
    rw [e1, e2]
  refine ⟨s, fun v a ha => ?_⟩
  by_cases hv : v ∈ tsupport φ
  · exact key v hv a ha
  · by_cases hv' : v + a ∈ tsupport φ
    · have h3 : Multiplicative.ofAdd (-a) ∈ polyBall (k := k) n s := by
        have := inv_mem ha
        rwa [← ofAdd_neg] at this
      have := key _ hv' (-a) h3
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hv']

theorem restr_lc {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E)
    (f : cIndSpace (LH k n) ρ) : IsLocallyConstant (restr ρ f) := by
  obtain ⟨s, hs⟩ := restr_periodic ρ f
  refine (IsLocallyConstant.iff_exists_open _).2 fun v => ⟨_, isOpen_shiftBall n s v, ?_, fun y hy => ?_⟩
  · show Multiplicative.ofAdd (v - v) ∈ polyBall (k := k) n s
    rw [sub_self, ofAdd_zero]; exact one_mem _
  have hy' : Multiplicative.ofAdd (y - v) ∈ polyBall (k := k) n s := hy
  have e : v + (y - v) = y := by abel
  exact (congrArg (restr ρ f) e).symm.trans (hs v (y - v) hy')

theorem restr_cs {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E)
    (f : cIndSpace (LH k n) ρ) : HasCompactSupport (restr ρ f) := by
  obtain ⟨S, hS⟩ := restr_support ρ f
  refine HasCompactSupport.intro ((isCompact_polyBall n S).image continuous_toAdd) fun v hv => ?_
  by_contra h
  exact hv ⟨Multiplicative.ofAdd v, hS v h, rfl⟩

def restrS {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E) :
    cIndSpace (LH k n) ρ →ₗ[ℂ] SchF k n E where
  toFun f := ⟨restr ρ f, restr_lc ρ f, restr_cs ρ f⟩
  map_add' _ _ := Subtype.ext (map_add (restr ρ) _ _)
  map_smul' c f := Subtype.ext (map_smul (restr ρ) c f)

set_option maxHeartbeats 2000000 in
open Classical in
theorem restrS_surjective {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E)
    (hρ : IsSmooth ρ) : Function.Surjective (restrS ρ) := by
  intro f
  obtain ⟨s, hs⟩ := exists_period f.1 f.2.1 f.2.2
  obtain ⟨S, hS⟩ := exists_compact_polyBall n f.2.2.isCompact
  obtain ⟨R, hR⟩ := exists_reps f.1 s S hs (fun v hv => hS v (subset_tsupport _ hv))
  choose b hb using fun e : E => exists_bump ρ hρ s e
  refine ⟨∑ x ∈ R, cInd (LH k n) ρ (uv n (-x)) (b (f.1 x)), Subtype.ext (funext fun v => ?_)⟩
  have hx : ∀ x, restr ρ (cInd (LH k n) ρ (uv n (-x)) (b (f.1 x))) v =
      if Multiplicative.ofAdd (v - x) ∈ polyBall (k := k) n s then f.1 x else 0 := fun x =>
    (restr_uv ρ (-x) _ v).trans ((hb (f.1 x) (v + -x)).trans (by rw [sub_eq_add_neg]))
  refine (congrFun (map_sum (restr ρ) _ _) v).trans ((Finset.sum_apply _ _ _).trans ?_)
  exact (Finset.sum_congr rfl fun x _ => hx x).trans (hR v).symm

theorem model_LH {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E) (hρ : IsSmooth ρ) :
    ∃ e : SchF k n E ≃ₗ[ℂ] cIndSpace (LH k n) ρ, ∀ f y, restr ρ (e f) y = f.1 y := by
  have hi : Function.Injective (restrS ρ) := fun f f' h =>
    restr_injective ρ (congrArg Subtype.val h)
  refine ⟨(LinearEquiv.ofBijective (restrS ρ) ⟨hi, restrS_surjective ρ hρ⟩).symm, fun f y => ?_⟩
  have := (LinearEquiv.ofBijective (restrS ρ) ⟨hi, restrS_surjective ρ hρ⟩).apply_symm_apply f
  exact congrFun (congrArg Subtype.val this) y

set_option maxHeartbeats 2000000 in

theorem model_H {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (H : Subgroup (Mir k n)) (hH : H = LH k n)
    (ρ : Representation ℂ H E) (hρ : IsSmooth ρ) (hm : ∀ g, levi k n g ∈ H) :
    ∃ e : SchF k n E ≃ₗ[ℂ] cIndSpace H ρ, (∀ x f, e (shiftF x f) = cInd H ρ (uM n x) (e f)) ∧
      ∀ g f, e (actF (ρ.comp ((levi k n).codRestrict H hm)) g f) = cInd H ρ (levi k n g) (e f) := by
  subst hH
  obtain ⟨e, he⟩ := model_LH ρ hρ
  refine ⟨e, fun x f => restr_injective ρ (funext fun y => ?_), fun g f => restr_injective ρ (funext fun y => ?_)⟩
  · exact (he _ y).trans ((he f (y + x)).symm.trans (restr_uv ρ x (e f) y).symm)
  · exact (he _ y).trans ((congrArg (ρ (lv k n g)) (he f _)).symm.trans (restr_levi ρ g (e f) y).symm)

theorem ePG_zero_true' (t : ℕ) (b : Fin t) : (ePG 0 t ⟨true, b⟩ : Fin (0 + t + 1)).val = b.val := by
  simp [ePG, two]

theorem pg_levi (t : ℕ) (c : 0 + t = t) (g : GL (Fin (0 + t)) k) (h : levi k (0 + t) g ∈ HPG k 0 t) :
    pgProj k 0 t ⟨_, h⟩ = (1, glCast c g) := by
  refine Prod.ext ?_ ?_
  · haveI := subsingleton_mir_zero (k := k)
    exact Subsingleton.elim _ _
  · apply Units.ext
    ext i j
    show ((levi k (0 + t) g : Mir k (0 + t)) : GL (Fin (0 + t + 1)) k).val
        (ePG 0 t ⟨true, i⟩) (ePG 0 t ⟨true, j⟩) = (glCast c g).val i j
    have e : ∀ b : Fin t, (ePG 0 t ⟨true, b⟩ : Fin (0 + t + 1)) = Fin.castSucc (Fin.cast c.symm b) := fun b =>
      Fin.ext ((ePG_zero_true' t b).trans rfl)
    rw [e, e, glCast_apply]
    show glEmbMat k _ g.val _ _ = _
    simp [glEmbMat]

def schMap {d : ℕ} {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E'] (ι : E →ₗ[ℂ] E') :
    SchF k d E →ₗ[ℂ] SchF k d E' where
  toFun f := ⟨fun y => ι (f.1 y), f.2.1.comp ι, f.2.2.comp_left (map_zero ι)⟩
  map_add' f f' := Subtype.ext (funext fun y => map_add ι _ _)
  map_smul' c f := Subtype.ext (funext fun y => map_smul ι c _)

theorem model_cast {N t : ℕ} (c : N = t) {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ι : E ≃ₗ[ℂ] E') (X : Representation ℂ (GL (Fin t) k) E) (X' : Representation ℂ (GL (Fin N) k) E')
    (hX : ∀ g v, ι (X g v) = X' (glCast c.symm g) (ι v)) :
    ∃ T : SchF k t E ≃ₗ[ℂ] SchF k N E', (∀ x f, T (shiftF x f) = shiftF (x ∘ Fin.cast c) (T f)) ∧
      ∀ g f, T (actF X g f) = actF X' (glCast c.symm g) (T f) := by
  subst c
  refine ⟨LinearEquiv.ofLinear (schMap ι.toLinearMap) (schMap ι.symm.toLinearMap) ?_ ?_, fun x f => rfl, fun g f => ?_⟩
  · ext f y
    exact congrFun (congrArg Subtype.val (rfl : _ = _)) y |>.trans (ι.apply_symm_apply _)
  · ext f y
    exact ι.symm_apply_apply _
  · exact Subtype.ext (funext fun y => hX g _)

theorem mcast_act {a b : ℕ} (h : a = b) (R : MRep k a) :
    ∃ E : R.V ≃ₗ[ℂ] (mcast h R).V, (∀ x v, E (R.ρ (uM a (x ∘ Fin.cast h)) v) = (mcast h R).ρ (uM b x) (E v)) ∧
      ∀ g v, E (R.ρ (levi k a (glCast h.symm g)) v) = (mcast h R).ρ (levi k b g) (E v) := by
  subst h
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem exists_line_tensor {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (h : Module.finrank ℂ W = 1) : ∃ (w : W) (ι : V ≃ₗ[ℂ] W ⊗[ℂ] V), ∀ v, ι v = w ⊗ₜ[ℂ] v := by
  haveI : Module.Finite ℂ W := Module.finite_of_finrank_pos (by omega)
  let e : ℂ ≃ₗ[ℂ] W := LinearEquiv.ofFinrankEq _ _ (by simp [h])
  refine ⟨e 1, (TensorProduct.lid ℂ V).symm.trans (TensorProduct.congr e (LinearEquiv.refl ℂ V)), fun v => ?_⟩
  simp

set_option maxHeartbeats 2000000 in

theorem model' (t : ℕ) (c : 0 + t = t) (τ : MRep k 0) (σ : GRep k t) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (h1 : Module.finrank ℂ τ.V = 1) :
    ∃ e : SchF k t σ.V ≃ₗ[ℂ] (mcast c (prodPGn τ σ)).V,
      (∀ x f, e (shiftF x f) = (mcast c (prodPGn τ σ)).ρ (uM t x) (e f)) ∧
      ∀ g f, e (actF (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ g f) = (mcast c (prodPGn τ σ)).ρ (levi k t g) (e f) := by
  have hm : ∀ g, levi k (0 + t) g ∈ HPG k 0 t := fun g => by
    rw [HPG_zero t]
    exact ⟨g, rfl⟩
  have hsm := smooth_pg 0 t (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ (sm_mtw hτ _) (sm_tw hσ _)
  obtain ⟨e, e1, e2⟩ := model_H (HPG k 0 t) (HPG_zero t) _ hsm hm
  obtain ⟨w, ι, hι⟩ := exists_line_tensor (W := (mtw τ (((t : ℕ) : ℝ) / 2)).V) (V := (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).V) h1
  obtain ⟨T, T1, T2⟩ := model_cast c ι (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ
    (((extTensor (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k 0 t)).comp
      ((levi k (0 + t)).codRestrict (HPG k 0 t) hm)) (fun g v => by
    show _ = extTensor _ _ (pgProj k 0 t ⟨levi k (0 + t) (glCast c.symm g), hm _⟩) (ι v)
    rw [pg_levi t c, glCast_glCast]
    refine (hι _).trans (Eq.trans ?_ (congrArg _ (hι v)).symm)
    refine Eq.trans ?_ (extTensor_tmul _ _ _ _ _).symm
    have h2 : (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (1 : Mir k 0) w = w := by
      rw [map_one]
      rfl
    exact (congrArg (fun z => z ⊗ₜ[ℂ] ((σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ g v)) h2).symm)
  obtain ⟨E, E1, E2⟩ := mcast_act c (prodPGn τ σ)
  refine ⟨(T.trans e).trans E, fun x f => ?_, fun g f => ?_⟩
  · exact (congrArg (fun z => E (e z)) (T1 x f)).trans ((congrArg E (e1 _ (T f))).trans (E1 x _))
  · exact (congrArg (fun z => E (e z)) (T2 g f)).trans ((congrArg E (e2 _ (T f))).trans (E2 g _))

theorem mem_mirabolicParabolic_zero_right (d : ℕ) (g : Mir k (d + 0)) : g ∈ MirabolicParabolic k d 0 := by
  show (g : GL (Fin (d + 0 + 1)) k) ∈ parab k (eGP d 0)
  rw [mem_parab_iff]
  intro a c i j hac
  obtain ⟨rfl, rfl⟩ : a = true ∧ c = false := by
    revert hac; cases a <;> cases c <;> decide
  have hi : i = Fin.last 0 := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
  subst hi
  rw [blockIndex_true_last]
  have hh := congrFun ((mem_Mir_iff k _).1 g.2) (eGP d 0 ⟨false, j⟩)
  rw [hh]
  simp only [eLast, Pi.single_apply]
  exact if_neg (blockIndex_false_ne_last d 0 j)

theorem gp_uM (d : ℕ) (x : Fin (d + 0) → k) (h : uM (d + 0) x ∈ MirabolicParabolic k d 0) : gpProj k d 0 ⟨_, h⟩ = 1 := by
  refine Prod.ext ?_ ?_
  · apply Units.ext
    ext i j
    show (1 + colMat k (d + 0) x) (eGP d 0 ⟨false, i⟩) (eGP d 0 ⟨false, j⟩) = (1 : Matrix (Fin d) (Fin d) k) i j
    have hinj : eGP d 0 ⟨false, i⟩ = eGP d 0 ⟨false, j⟩ ↔ i = j := by
      constructor
      · intro e
        simpa using (eGP d 0).injective e
      · rintro rfl; rfl
    have hl : eGP d 0 ⟨false, j⟩ ≠ Fin.last (d + 0) := blockIndex_false_ne_last d 0 j
    simp [colMat, hl, one_apply, hinj]
    exact fun h => absurd h hl
  · haveI := subsingleton_mir_zero (k := k)
    exact Subsingleton.elim _ _

theorem cInd_top {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (htop : ∀ g, g ∈ H) (u : G) (h1 : ∀ w, σ ⟨u, htop u⟩ w = w)
    (f : cIndSpace H σ) : cInd H σ u f = f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have hf : ∀ (h : H) (x : G), f.1.1.1 ((h : G) * x) = σ h (f.1.1.1 x) := f.1.1.2
  show f.1.1.1 (g * u) = f.1.1.1 g
  have a1 := hf ⟨g, htop g⟩ u
  have a2 := hf ⟨u, htop u⟩ 1
  have a3 := hf ⟨g, htop g⟩ 1
  rw [mul_one] at a2 a3
  simp only at a1 a2 a3
  rw [a1, a3, a2, h1]

theorem gp_triv {d : ℕ} (ρ : GRep k d) (Z : MRep k 0) (x : Fin (d + 0) → k) (v : (prodGPn ρ Z).V) :
    (prodGPn ρ Z).ρ (uM (d + 0) x) v = v := by
  refine cInd_top _ _ (mem_mirabolicParabolic_zero_right d) _ (fun w => ?_) v
  show extTensor _ _ (gpProj k d 0 ⟨uM (d + 0) x, _⟩) w = w
  rw [gp_uM, map_one]
  rfl

theorem gres_cast {p q : ℕ} (h : p = q) (h' : p + 1 = q + 1) (π : GRep k (p + 1)) :
    gres (π.cast h') = mcast h (gres π) := by
  subst h; rfl

theorem irr_cast {p q : ℕ} (h : p = q) (π : GRep k p) (hi : π.ρ.IsIrreducible) : (π.cast h).ρ.IsIrreducible := by
  subst h; exact hi

theorem cusp_cast {p q : ℕ} (h : p = q) (π : GRep k p) (hi : IsCuspidal π.ρ) : IsCuspidal (π.cast h).ρ := by
  subst h; exact hi

theorem mcast_pg {p q t N : ℕ} (e : p = q) (τ : MRep k p) (σ : GRep k t) (h : p + t = N) (h' : q + t = N) :
    mcast h (prodPGn τ σ) = mcast h' (prodPGn (mcast e τ) σ) := by
  subst e; rfl

theorem mcast_gp {p q r N : ℕ} (e : p = q) (ρ : GRep k r) (τ : MRep k p) (h : r + p = N) (h' : r + q = N) :
    mcast h (prodGPn ρ τ) = mcast h' (prodGPn ρ (mcast e τ)) := by
  subst e; rfl

theorem model (t : ℕ) (c : 0 + t = t) (τ : MRep k 0) (σ : GRep k t) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (h1 : Module.finrank ℂ τ.V = 1) :
    ∃ e : SchF k t σ.V ≃ₗ[ℂ] (mcast c (prodPGn τ σ)).V,
      (∀ x f, e (shiftF x f) = (mcast c (prodPGn τ σ)).ρ (uM t x) (e f)) ∧
      ∀ g f, e (actF (σ.tw (-1 / 2)).ρ g f) = (mcast c (prodPGn τ σ)).ρ (levi k t g) (e f) := by
  have h := model' t c τ σ hτ hσ h1
  rwa [show -((0 + 1 : ℕ) : ℝ) / 2 = -1 / 2 by norm_num] at h

open GlobalTheory.CompanionTheory.LeibOrd.Main in

theorem open_part : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) (a b : GRep k (m + 1))
    (hs : IsSmooth a.ρ) (hb : IsSmooth b.ρ) (hi : a.ρ.IsIrreducible) (hcu : IsCuspidal a.ρ),
    ∃ ι : SchF k (m + 1) b.V →ₗ[ℂ] (Rm ψ a b).V, Function.Injective ι ∧
      (∀ x f, ι (shiftF x f) = (Rm ψ a b).ρ (uM (m + 1) x) (ι f)) ∧
      (∀ g f, ι (actF (b.tw (-1 / 2)).ρ g f) = (Rm ψ a b).ρ (levi k (m + 1) g) (ι f)) ∧
      ∀ x v, (Rm ψ a b).ρ (uM (m + 1) x) v - v ∈ LinearMap.range ι := by
  intro k _ _ _ _ ψ hc h1 m a b hs hb hi hcu
  have e0 : m = 0 + m := by omega
  have e1 : m + 1 = 0 + m + 1 := by omega
  have sa' : IsSmooth (a.cast e1).ρ := isSmooth_gcast e1 hs
  have sb' : IsSmooth (b.cast e1).ρ := isSmooth_gcast e1 hb
  have sga : IsSmooth (gres (a.cast e1)).ρ := isSmooth_gres sa'
  have sgb : IsSmooth (gres (b.cast e1)).ρ := isSmooth_gres sb'
  have hx := GlobalTheory.CompanionTheory.BZRes.resSeq k m m ((m + 1) + m) (by omega) a b hs hb
  have ses := ses_iterN ψ hc m (n := m + 1) (isSmooth_mcast _ (isSmooth_prodPGn _ _))
    (isSmooth_gres (isSmooth_gcast _ (isSmooth_prod _ _))) (isSmooth_mcast _ (isSmooth_prodGPn _ _)) (ses_of_mext hx)
  have hτ₀ : IsSmooth (iterN ψ m (gres (a.cast e1))).ρ := isSmooth_iterN ψ m sga
  have hfin := finrank_iterN ψ hc h1 (a.cast e1) sa' (irr_cast e1 a hi) (cusp_cast e1 a hcu)
  have isoA : MIso (iterN ψ m (mcast (by omega : m + (m + 1) = (m + 1) + m) (prodPGn (gres a) b)))
      (mcast (by omega : 0 + (m + 1) = m + 1) (prodPGn (iterN ψ m (gres (a.cast e1))) b)) := by
    rw [mcast_pg e0 (gres a) b (by omega) (by omega : (0 + m) + (m + 1) = (m + 1) + m), ← gres_cast e0 e1 a]
    exact pg_iter ψ hc h1 m 0 m (gres (a.cast e1)) b (m + 1) (by omega) (by omega) sga hb
      (fun i n' e hi' => dN_gres_vanish ψ (a.cast e1) (cusp_cast e1 a hcu) i n' e (by omega))
  have isoC : MIso (iterN ψ m (mcast (by omega : (m + 1) + m = (m + 1) + m) (prodGPn a (gres b))))
      (prodGPn (m := m + 1) (j := 0) a (iterN ψ m (gres (b.cast e1)))) := by
    rw [mcast_gp e0 a (gres b) (by omega) (by omega : (m + 1) + (0 + m) = (m + 1) + m), ← gres_cast e0 e1 b]
    exact gp_iter ψ hc h1 m 0 (m + 1) a (gres (b.cast e1)) (m + 1) rfl (by omega) hs sgb
  obtain ⟨f, g, hf, hg, hinj, hsurj, hex⟩ := ses
  obtain ⟨eA⟩ := isoA
  obtain ⟨eC⟩ := isoC
  obtain ⟨e, he1, he2⟩ := model (m + 1) (by omega) (iterN ψ m (gres (a.cast e1))) b hτ₀ hb hfin
  refine ⟨f ∘ₗ eA.symm.toLinearEquiv.toLinearMap ∘ₗ e.toLinearMap, ?_, ?_, ?_, ?_⟩
  · exact hinj.comp (eA.symm.toLinearEquiv.injective.comp e.injective)
  · intro x φ
    show f (eA.symm (e (shiftF x φ))) = _
    rw [he1, eint eA.symm, hf]
    rfl
  · intro x φ
    exact (congrArg (fun z => f (eA.symm z)) (he2 x φ)).trans ((congrArg f (eint eA.symm _ _)).trans (hf _ _))
  · intro x v
    have h0 : (Rm ψ a b).ρ (uM (m + 1) x) v - v ∈ LinearMap.ker g := by
      have h4 : g ((Rm ψ a b).ρ (uM (m + 1) x) v) = g v := by
        refine (hg _ _).trans ?_
        apply eC.toLinearEquiv.injective
        exact (eint eC _ _).trans (gp_triv a _ x _)
      exact (map_sub g _ _).trans (sub_eq_zero.2 h4)
    obtain ⟨w, hw⟩ := hex.ge h0
    obtain ⟨φ, hφ⟩ := e.surjective (eA w)
    refine ⟨φ, ?_⟩
    exact (congrArg (fun z => f (eA.symm z)) hφ).trans ((congrArg f (Representation.Equiv.symm_apply_apply eA w)).trans hw)

end GlobalTheory.CompanionTheory.BZShellOpen

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functions_embed_cuspidal_derivative : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) (a b : GRep k (m + 1))
    (hs : IsSmooth a.ρ) (hb : IsSmooth b.ρ) (hi : a.ρ.IsIrreducible) (hcu : IsCuspidal a.ρ),
    ∃ ι : SchF k (m + 1) b.V →ₗ[ℂ] (Rm ψ a b).V, Function.Injective ι ∧
      (∀ x f, ι (shiftF x f) = (Rm ψ a b).ρ (uM (m + 1) x) (ι f)) ∧
      (∀ g f, ι (actF (b.tw (-1 / 2)).ρ g f) = (Rm ψ a b).ρ (levi k (m + 1) g) (ι f)) ∧
      ∀ x v, (Rm ψ a b).ρ (uM (m + 1) x) v - v ∈ LinearMap.range ι := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZShellOpen.open_part
end

section
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
open GlobalTheory.CompanionTheory.MirFourier
open scoped Topology

namespace GlobalTheory.CompanionTheory.BZShell.Radical

section aux

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem uM_add_eq (d : ℕ) (x y : Fin d → k) : uM d (x + y) = uM d x * uM d y :=
  map_mul (unipIn k d) (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

theorem uM_zero_eq (d : ℕ) : uM (k := k) d 0 = 1 := map_one (unipIn k d)

theorem exists_pow_mem (d : ℕ) (H : Subgroup (Multiplicative (Fin d → k)))
    (hH : IsOpen (H : Set (Multiplicative (Fin d → k)))) (x : Multiplicative (Fin d → k)) :
    ∃ n : ℕ, 0 < n ∧ x ^ n ∈ H := by
  obtain ⟨s, hs⟩ := exists_mem_polyBall x
  let P : Subgroup (Multiplicative (Fin d → k)) := polyBall (k := k) d s
  haveI : CompactSpace P := isCompact_iff_compactSpace.mp (isCompact_polyBall d s)
  let N : Subgroup P := H.subgroupOf P
  have hN : IsOpen (N : Set P) := hH.preimage continuous_subtype_val
  haveI : Finite (P ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := N) Subgroup.index_ne_zero_of_finite ⟨x, hs⟩
  exact ⟨n, hn, by simpa [N, Subgroup.mem_subgroupOf] using hmem⟩

def stabU {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Mir k d) W) (t : W) :
    Subgroup (Multiplicative (Fin d → k)) where
  carrier := {x | ρ (unipIn k d x) t = t}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul]
    simp

theorem isOpen_stabU {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Mir k d) W)
    (hρ : IsSmooth ρ) (t : W) : IsOpen (stabU ρ t : Set (Multiplicative (Fin d → k))) :=
  (hρ t).preimage (continuous_unipIn d)

def bump {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (s : kˣ) (a : V) : SchF k d V :=
  ⟨(FourierPi.box (Fin d) s).indicator fun _ => a,
    ((LocallyConstant.const _ a).indicator ⟨(FourierPi.isCompact_box s).isClosed, FourierPi.isOpen_box s⟩).isLocallyConstant,
    HasCompactSupport.intro (FourierPi.isCompact_box s) fun _ hx => Set.indicator_of_notMem hx _⟩

end aux

theorem false_of_translation_invariant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (hd : 0 < d) (R R' : MRep k d) (hR' : IsSmooth R'.ρ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Nontrivial V]
    (B : R.V →ₗ[ℂ] R'.V →ₗ[ℂ] ℂ) (hB : ∀ x v v', B (R.ρ (uM d x) v) (R'.ρ (uM d x) v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (ι : SchF k d V →ₗ[ℂ] R.V) (hι : Function.Injective ι) (hιs : ∀ x f, ι (shiftF x f) = R.ρ (uM d x) (ι f))
    (ι' : SchF k d V' →ₗ[ℂ] R'.V) (hιs' : ∀ x f, ι' (shiftF x f) = R'.ρ (uM d x) (ι' f))
    (hr : ∀ x v, R'.ρ (uM d x) v - v ∈ LinearMap.range ι')
    (hC : ∀ f f' x, B (ι f) (ι' (shiftF x f')) = B (ι f) (ι' f')),
    False := by
  intro k _ _ _ _ d hd R R' hR' V V' _ _ _ _ _ B hB hn ι hι hιs ι' hιs' hr hC
  obtain ⟨a, ha⟩ := exists_ne (0 : V)
  let i₀ : Fin d := ⟨0, hd⟩
  have hU : {y : k | y ≠ 1} ∈ 𝓝 (0 : k) := isOpen_ne.mem_nhds (zero_ne_one (α := k))
  obtain ⟨s, hs⟩ := exists_cball_subset hU
  let x₀ : Fin d → k := Pi.single i₀ 1
  let f₀ : SchF k d V := bump d s a
  have hx₀ : x₀ ∉ FourierPi.box (Fin d) s := fun h => hs (h i₀ trivial) (by simp [x₀])
  have h0 : (0 : Fin d → k) ∈ FourierPi.box (Fin d) s := fun i _ => by simp [cball]
  have hne : shiftF x₀ f₀ - f₀ ≠ 0 := by
    intro h
    have h1 := congrArg (fun f : SchF k d V => f.1 0) h
    have h2 : (shiftF x₀ f₀).1 0 = 0 := by
      rw [shiftF_apply, zero_add]
      exact Set.indicator_of_notMem (f := fun _ => a) hx₀
    have h3 : f₀.1 0 = a := Set.indicator_of_mem (f := fun _ => a) h0
    have h4 : (shiftF x₀ f₀).1 0 - f₀.1 0 = 0 := h1
    rw [h2, h3, zero_sub, neg_eq_zero] at h4
    exact ha h4
  have hv : ι (shiftF x₀ f₀ - f₀) ≠ 0 := fun h => hne (hι (h.trans (map_zero ι).symm))
  obtain ⟨t, ht⟩ := hn _ hv
  apply ht
  have hinv : ∀ y z : Fin d → k, R'.ρ (uM d y) (R'.ρ (uM d z) t) = R'.ρ (uM d (y + z)) t := by
    intro y z
    rw [uM_add_eq, map_mul, Module.End.mul_apply]
  set w : R'.V := R'.ρ (uM d (-x₀)) t - t with hw
  have hBv : B (ι (shiftF x₀ f₀ - f₀)) t = B (ι f₀) w := by
    have h1 := hB x₀ (ι f₀) (R'.ρ (uM d (-x₀)) t)
    rw [hinv, add_neg_cancel, uM_zero_eq, map_one, Module.End.one_apply] at h1
    rw [map_sub, hιs, map_sub, LinearMap.sub_apply, hw, map_sub, h1]
  rw [hBv]
  obtain ⟨f', hf'⟩ := hr (-x₀) t
  have step : ∀ y : Fin d → k, B (ι f₀) (R'.ρ (uM d (y + -x₀)) t) - B (ι f₀) (R'.ρ (uM d y) t) = B (ι f₀) w := by
    intro y
    have hf2 : ι' f' = w := hf'
    have h1 : B (ι f₀) (R'.ρ (uM d y) w) = B (ι f₀) w := by
      rw [← hf2, ← hιs', hC]
    rw [← h1, hw, map_sub, map_sub, hinv]
  have hall : ∀ i : ℕ, B (ι f₀) (R'.ρ (uM d (i • x₀)) t) = B (ι f₀) t - (i : ℂ) * B (ι f₀) w := by
    intro i
    induction i with
    | zero => simp [uM_zero_eq]
    | succ i ih =>
      have h1 := step ((i + 1) • x₀)
      have h2 : (i + 1) • x₀ + -x₀ = i • x₀ := by
        rw [succ_nsmul]; abel
      rw [h2, ih] at h1
      push_cast
      linear_combination -h1
  obtain ⟨n, hn0, hnm⟩ := exists_pow_mem d (stabU R'.ρ t) (isOpen_stabU R'.ρ hR' t) (Multiplicative.ofAdd x₀)
  have hfix : R'.ρ (uM d (n • x₀)) t = t := hnm
  have h1 := hall n
  rw [hfix] at h1
  have h2 : (n : ℂ) * B (ι f₀) w = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 hn0.ne')

end GlobalTheory.CompanionTheory.BZShell.Radical

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerate_unipotent_pairing_schwartz : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (hd : 0 < d) (R R' : MRep k d) (hR' : IsSmooth R'.ρ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Nontrivial V]
    (B : R.V →ₗ[ℂ] R'.V →ₗ[ℂ] ℂ) (hB : ∀ x v v', B (R.ρ (uM d x) v) (R'.ρ (uM d x) v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (ι : SchF k d V →ₗ[ℂ] R.V) (hι : Function.Injective ι) (hιs : ∀ x f, ι (shiftF x f) = R.ρ (uM d x) (ι f))
    (ι' : SchF k d V' →ₗ[ℂ] R'.V) (hιs' : ∀ x f, ι' (shiftF x f) = R'.ρ (uM d x) (ι' f))
    (hr : ∀ x v, R'.ρ (uM d x) v - v ∈ LinearMap.range ι')
    (hC : ∀ f f' x, B (ι f) (ι' (shiftF x f')) = B (ι f) (ι' f')),
    False := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZShell.Radical.false_of_translation_invariant
end

section
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult
  GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.BZShell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dpowM_half_cancel {n : ℕ} (m : ℕ) (p : Mir k n) :
    ((dpowM n (-(m : ℝ) / 2) p : ℂˣ) : ℂ) * ((dpowM n (-(m : ℝ) / 2) p : ℂˣ) : ℂ) *
      ((detChar (Fin (n + 1)) (absPow k (m : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) = 1 := by
  have h : dpowM (k := k) n (-(m : ℝ) / 2) * dpowM n (-(m : ℝ) / 2) * dpowM n (m : ℝ) = 1 := by
    rw [← DerivTw.dpowM_add, ← DerivTw.dpowM_add,
      show (m : ℝ) + (-(m : ℝ) / 2 + -(m : ℝ) / 2) = 0 by ring, DerivTw.dpowM_zero]
  have h2 := congrArg (fun f : Mir k n →* ℂˣ => ((f p : ℂˣ) : ℂ)) h
  simp only [MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one] at h2
  have h3 : ((dpowM n (m : ℝ) p : ℂˣ) : ℂ) =
      ((detChar (Fin (n + 1)) (absPow k (m : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) := by
    show ((detChar (Fin (n + 1)) (absPow k (((m : ℝ)) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) = _
    rw [Complex.ofReal_natCast]
  rw [← h3]
  exact h2

theorem pair_iterN (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) (π π' : GRep k (((m + 1) + m) + 1))
    (hs : IsSmooth π.ρ) (hs' : IsSmooth π'.ρ) (B : π.V →ₗ[ℂ] π'.V →ₗ[ℂ] ℂ) (hB : ∀ g v v', B (π.ρ g v) (π'.ρ g v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) :
    ∃ B' : (iterN ψ m (gres π)).V →ₗ[ℂ] (iterN ψ⁻¹ m (gres π')).V →ₗ[ℂ] ℂ,
      (∀ p v v', B' ((iterN ψ m (gres π)).ρ p v) ((iterN ψ⁻¹ m (gres π')).ρ p v') = B' v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B' v v' ≠ 0 := by
  obtain ⟨B₀, hB₀, hn₀⟩ := GlobalTheory.CompanionTheory.BZPairDescend.pair_iterPhi ψ hc h1 m m π.ρ π'.ρ hs hs' B hB hn
  obtain ⟨e⟩ : MIso (iterN ψ m (gres π)) (mtw (iterPhi k ψ m (resM k π.ρ)) (-(m : ℝ) / 2)) := DerivTw.iterN_iso ψ m (gres π)
  obtain ⟨e'⟩ : MIso (iterN ψ⁻¹ m (gres π')) (mtw (iterPhi k ψ⁻¹ m (resM k π'.ρ)) (-(m : ℝ) / 2)) :=
    DerivTw.iterN_iso ψ⁻¹ m (gres π')
  let f : (iterN ψ m (gres π)).V ≃ₗ[ℂ] (iterPhi k ψ m (resM k π.ρ)).V := e.toLinearEquiv
  let f' : (iterN ψ⁻¹ m (gres π')).V ≃ₗ[ℂ] (iterPhi k ψ⁻¹ m (resM k π'.ρ)).V := e'.toLinearEquiv
  have hf : ∀ p v, f ((iterN ψ m (gres π)).ρ p v) =
      ((dpowM (m + 1) (-(m : ℝ) / 2) p : ℂˣ) : ℂ) • (iterPhi k ψ m (resM k π.ρ)).ρ p (f v) := fun p v => eint e p v
  have hf' : ∀ p v, f' ((iterN ψ⁻¹ m (gres π')).ρ p v) =
      ((dpowM (m + 1) (-(m : ℝ) / 2) p : ℂˣ) : ℂ) • (iterPhi k ψ⁻¹ m (resM k π'.ρ)).ρ p (f' v) := fun p v => eint e' p v
  refine ⟨(B₀.compl₁₂ f.toLinearMap f'.toLinearMap), fun p v v' => ?_, fun v hv => ?_⟩
  · simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    rw [hf, hf', map_smul, map_smul, LinearMap.smul_apply, hB₀, smul_eq_mul, smul_eq_mul]
    linear_combination (B₀ (f v) (f' v')) * dpowM_half_cancel (k := k) m p
  · obtain ⟨w', hw'⟩ := hn₀ (f v) (by simpa using hv)
    refine ⟨f'.symm w', ?_⟩
    simpa using hw'

end GlobalTheory.CompanionTheory.BZShell

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_pairing_iterated_derivative : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) (π π' : GRep k (((m + 1) + m) + 1))
    (hs : IsSmooth π.ρ) (hs' : IsSmooth π'.ρ) (B : π.V →ₗ[ℂ] π'.V →ₗ[ℂ] ℂ) (hB : ∀ g v v', B (π.ρ g v) (π'.ρ g v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0),
    ∃ B' : (iterN ψ m (gres π)).V →ₗ[ℂ] (iterN ψ⁻¹ m (gres π')).V →ₗ[ℂ] ℂ,
      (∀ p v v', B' ((iterN ψ m (gres π)).ρ p v) ((iterN ψ⁻¹ m (gres π')).ρ p v') = B' v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B' v v' ≠ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZShell.pair_iterN
end

section
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.BZSegComm GlobalTheory.CompanionTheory.BZShell

namespace GlobalTheory.CompanionTheory.BZShell.SwapPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem contra_ind₂_swap {r t N : ℕ} (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
    (hs₁ : IsSmooth π₁) (hi₁ : π₁.IsIrreducible) (hs₂ : IsSmooth π₂) (hi₂ : π₂.IsIrreducible)
    (h : r + t = N) (h' : t + r = N) (hX : (ind₂ (stdSum h) (extTensor π₁ π₂)).IsIrreducible) :
    Nonempty ((contra (ind₂ (stdSum h) (extTensor π₁ π₂))).Equiv
      (ind₂ (stdSum h') (extTensor (contra π₂) (contra π₁)))) := by
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  have Gx := nonempty_comp_invT_equiv_contra π₁ (hA k _ _ _ hs₁ hi₁) hi₁
  have Gy := nonempty_comp_invT_equiv_contra π₂ (hA k _ _ _ hs₂ hi₂) hi₂
  have T := nonempty_extTensor_swap π₁ π₂
  have K := ind₂_swap_equiv_comp_invT (k := k) (stdSum h) (stdSum h') (extTensor π₁ π₂)
  have GX := nonempty_comp_invT_equiv_contra (ind₂ (stdSum h) (extTensor π₁ π₂))
    (hA k N _ _ (isSmooth_parInd _ _) hX) hX
  exact Gx.elim fun gx => Gy.elim fun gy => T.elim fun τ => K.elim fun κ => GX.elim fun gX =>
    ⟨gX.symm.trans (κ.symm.trans (ind₂Equiv _ (τ.trans (extTensorCongr gy gx))))⟩

theorem ind₂_contra_fam (F : Fin 2 → IrrGL k) {N : ℕ} (h : (F 0).1 + (F 1).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra (F 0).rep) (contra (F 1).rep))).Equiv
      (contra (ind₂ (stdSum h) (extTensor (F 0).rep (F 1).rep)))) := by
  have hd : ∑ a, (F a).1 = N := (Fin.sum_univ_two _).trans h
  have E₂ := nonempty_ind₂_contra_equiv GlobalTheory.CompanionTheory.BZCuspPair.irrAdm F hd h
  have E₁ := nonempty_ind₂_equiv_multiProd (d := fun a => (F a).1) hd h fun a => (F a).rep
  refine E₂.elim fun ε₂ => E₁.elim fun ε₁ => ?_
  have ε₃ : (ind₂ (stdSum h) (extTensor (F 0).rep (F 1).rep)).Equiv (prodIrr F hd) := ε₁
  have ε₄ : (contra (prodIrr F hd)).Equiv (contra (ind₂ (stdSum h) (extTensor (F 0).rep (F 1).rep))) :=
    GlobalTheory.ContraRefl.contraEquiv ε₃
  exact ⟨ε₂.trans ε₄⟩

theorem induced_two_contragredient_equiv (F : Fin 2 → IrrGL k) (x y : IrrGL k) (h₀ : F 0 = x) (h₁ : F 1 = y) {N : ℕ}
    (h : x.1 + y.1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra x.rep) (contra y.rep))).Equiv
      (contra (ind₂ (stdSum h) (extTensor x.rep y.rep)))) := by
  subst h₀ h₁
  exact ind₂_contra_fam F h

theorem ind₂_contra_rep (x y : IrrGL k) {N : ℕ} (h : x.1 + y.1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra x.rep) (contra y.rep))).Equiv
      (contra (ind₂ (stdSum h) (extTensor x.rep y.rep)))) :=
  induced_two_contragredient_equiv ![x, y] x y rfl rfl h

theorem ind₂_contra_of_equiv (x y : IrrGL k) {N : ℕ} (h : x.1 + y.1 = N)
    (π₁ : Representation ℂ (GL (Fin x.1) k) V) (π₂ : Representation ℂ (GL (Fin y.1) k) W)
    (φ₁ : π₁.Equiv x.rep) (φ₂ : π₂.Equiv y.rep) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra π₁) (contra π₂))).Equiv
      (contra (ind₂ (stdSum h) (extTensor π₁ π₂)))) :=
  (ind₂_contra_rep x y h).elim fun ε =>
    ⟨(ind₂Equiv _ (extTensorCongr (GlobalTheory.ContraRefl.contraEquiv φ₁.symm) (GlobalTheory.ContraRefl.contraEquiv φ₂.symm))).trans
      (ε.trans (GlobalTheory.ContraRefl.contraEquiv (ind₂Equiv _ (extTensorCongr φ₁ φ₂))))⟩

theorem ind₂_contra_equiv {r t N : ℕ} (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W)
    (hs₁ : IsSmooth π₁) (hi₁ : π₁.IsIrreducible) (hs₂ : IsSmooth π₂) (hi₂ : π₂.IsIrreducible) (h : r + t = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra π₁) (contra π₂))).Equiv
      (contra (ind₂ (stdSum h) (extTensor π₁ π₂)))) :=
  ind₂_contra_of_equiv (IrrGL.of π₁ hs₁ hi₁) (IrrGL.of π₂ hs₂ hi₂) h π₁ π₂
    (IrrGL.equivOf π₁ hs₁ hi₁) (IrrGL.equivOf π₂ hs₂ hi₂)

theorem exists_form_of_equiv_contra {N : ℕ} (A : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth A)
    (C : Representation ℂ (GL (Fin N) k) W) (E : C.Equiv (contra A)) :
    ∃ B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ, (∀ g v v', B (A g v) (C g v') = B v v') ∧ ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
  let B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ := LinearMap.flip ((smoothPart A.dual).subtype ∘ₗ E.toLinearEquiv.toLinearMap)
  have hB : ∀ v v', B v v' = ((E.toLinearEquiv v' : smoothPart A.dual) : Module.Dual ℂ V) v := fun _ _ => rfl
  refine ⟨B, fun g v v' => ?_, fun v hv => ?_⟩
  · have hE : E.toLinearEquiv (C g v') = contra A g (E.toLinearEquiv v') :=
      E.toIntertwiningMap.isIntertwining _ _ g v'
    rw [hB, hB, hE, contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs (GlobalTheory.SqIntUnit.compactOpen_basis k N) hv
    refine ⟨E.toLinearEquiv.symm l, ?_⟩
    rw [hB, LinearEquiv.apply_symm_apply]
    exact hl

theorem isIrreducible_ind₂_segTerm {a N : ℕ} (π : Representation ℂ (GL (Fin a) k) V) (hN : 2 * a = N) (h : a + a = N)
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 a) (segTerm π 2)).IsIrreducible) :
    (ind₂ (stdSum h) (extTensor (segTerm π 2 0) (segTerm π 2 1))).IsIrreducible := by
  subst hN
  have hd : ∑ _ : Fin 2, a = 2 * a := by simp
  obtain ⟨E⟩ := nonempty_ind₂_equiv_multiProd (d := fun _ : Fin 2 => a) hd h (X := fun _ => V) (segTerm π 2)
  obtain ⟨ψ⟩ := (Placing.parInd_jac_placing k (Fin 2) (Fin (2 * a)) (fun _ => Fin a)
    (stdBlocks (fun _ : Fin 2 => a) hd) (GlobalTheory.Published.consecBlocks 2 a) _).1 (piTensor (segTerm π 2))
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv (E.trans ψ).symm hirr

theorem segTerm_zero {a : ℕ} (π : Representation ℂ (GL (Fin a) k) V) : segTerm π 2 0 = π := by
  have h : detChar (Fin a) (absPow k (((0 : Fin 2) : ℕ) : ℂ)) = 1 := by
    ext g
    simp
  rw [segTerm, h, twist_one]

theorem segTerm_one {a : ℕ} (π : Representation ℂ (GL (Fin a) k) V) : segTerm π 2 1 = twist π (dpow a 1) := by
  simp [segTerm, dpow]

theorem product_two_contragredient_equiv {a : ℕ} (σ : IrrRep (GL (Fin a) k))
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 a) (segTerm σ.ρ 2)).IsIrreducible) :
    Nonempty ((prod2 (k := k) rfl (contra σ.ρ) (twist (contra σ.ρ) (dpow a (-1)))).Equiv
      (contra (prod2 (k := k) rfl (twist σ.ρ (dpow a 1)) σ.ρ))) := by
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  have hs := σ.smooth
  have hi := σ.irr
  have hs₁ : IsSmooth (twist σ.ρ (dpow (k := k) a 1)) := isSmooth_twist hs (isSmoothChar_absPow _).detChar
  have hi₁ : (twist σ.ρ (dpow (k := k) a 1)).IsIrreducible := isIrreducible_twist hi _
  have hX : (ind₂ (stdSum (rfl : a + a = a + a)) (extTensor σ.ρ (twist σ.ρ (dpow (k := k) a 1)))).IsIrreducible := by
    have h := isIrreducible_ind₂_segTerm σ.ρ (by omega : 2 * a = a + a) rfl hirr
    rwa [segTerm_zero, segTerm_one] at h
  have S := contra_ind₂_swap σ.ρ (twist σ.ρ (dpow (k := k) a 1)) hs hi hs₁ hi₁ rfl rfl hX
  have B₁ := ind₂_contra_equiv σ.ρ (twist σ.ρ (dpow (k := k) a 1)) hs hi hs₁ hi₁ rfl
  have B₂ := ind₂_contra_equiv (twist σ.ρ (dpow (k := k) a 1)) σ.ρ hs₁ hi₁ hs hi rfl
  have Tw : Nonempty ((twist (contra σ.ρ) (dpow (k := k) a (-1))).Equiv (contra (twist σ.ρ (dpow (k := k) a 1)))) :=
    GlobalTheory.CompanionTheory.ZcDual.nonempty_equiv_contra_twist hA σ.ρ hs hi (isSmoothChar_absPow _) (isSmoothChar_absPow _)
      (by rw [Complex.ofReal_neg, absPow_neg, mul_inv_cancel])
  have P₁ := GlobalTheory.CompanionTheory.HighestDeriv.nonempty_prod2_equiv (k := k) (contra σ.ρ) (twist (contra σ.ρ) (dpow (k := k) a (-1)))
  have P₂ := GlobalTheory.CompanionTheory.HighestDeriv.nonempty_prod2_equiv (k := k) (twist σ.ρ (dpow (k := k) a 1)) σ.ρ
  refine S.elim fun s => B₁.elim fun b₁ => B₂.elim fun b₂ => Tw.elim fun τ => P₁.elim fun p₁ => P₂.elim fun p₂ => ?_
  have c₁ : (prod2 (k := k) rfl (contra σ.ρ) (twist (contra σ.ρ) (dpow a (-1)))).Equiv
      (ind₂ (stdSum (rfl : a + a = a + a)) (extTensor (contra σ.ρ) (contra (twist σ.ρ (dpow (k := k) a 1))))) :=
    p₁.trans (ind₂Equiv _ (extTensorCongr (.refl _) τ))
  have c₂ : (contra (ind₂ (stdSum (rfl : a + a = a + a)) (extTensor (twist σ.ρ (dpow (k := k) a 1)) σ.ρ))).Equiv
      (contra (prod2 (k := k) rfl (twist σ.ρ (dpow a 1)) σ.ρ)) :=
    GlobalTheory.ContraRefl.contraEquiv p₂
  exact ⟨c₁.trans (b₁.trans (s.trans (b₂.trans c₂)))⟩

theorem exists_pairing_cast (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k))
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 (m + 1)) (segTerm σ.ρ 2)).IsIrreducible) {N : ℕ}
    (h : (m + 1) + (m + 1) = N) :
    ∃ B : ((((gOf σ).tw 1).prod (gOf σ)).cast h).V →ₗ[ℂ]
        (((gDual σ).prod ((gDual σ).tw (-1))).cast h).V →ₗ[ℂ] ℂ,
      (∀ g v v', B ((((gOf σ).tw 1).prod (gOf σ)).cast h |>.ρ g v)
        (((gDual σ).prod ((gDual σ).tw (-1))).cast h |>.ρ g v') = B v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
  subst h
  exact (product_two_contragredient_equiv σ hirr).elim fun E =>
    exists_form_of_equiv_contra (prod2 (k := k) rfl (twist σ.ρ (dpow (m + 1) 1)) σ.ρ) (isSmooth_parInd _ _) _ E

theorem exists_invariant_pairing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ)
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 (m + 1)) (segTerm σ.ρ 2)).IsIrreducible),
    ∃ B : ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m)).V →ₗ[ℂ]
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m)).V →ₗ[ℂ] ℂ,
      (∀ g v v', B ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m) |>.ρ g v)
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m) |>.ρ g v') = B v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 :=
  fun m σ _ hirr => exists_pairing_cast m σ hirr (size_eq m)

end GlobalTheory.CompanionTheory.BZShell.SwapPair

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_pairing_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ)
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 (m + 1)) (segTerm σ.ρ 2)).IsIrreducible),
    ∃ B : ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m)).V →ₗ[ℂ]
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m)).V →ₗ[ℂ] ℂ,
      (∀ g v v', B ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m) |>.ρ g v)
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m) |>.ρ g v') = B v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZShell.SwapPair.exists_invariant_pairing
end

section
open ValuativeRel
namespace GlobalTheory.CompanionTheory.LocalField
theorem exists_uniformiser (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ ϖ : k, ∃ hϖ : ϖ ∈ (ValuativeRel.valuation k).integer, ϖ ≠ 0 ∧ ValuativeRel.valuation k (ϖ) < 1 ∧ (∀ x : k, ValuativeRel.valuation k (x) < 1 → ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) ∧ Irreducible (⟨ϖ, hϖ⟩ : (ValuativeRel.valuation k).integer) := by
  haveI : IsDiscreteValuationRing (ValuativeRel.valuation k).integer := inferInstance
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation k).integer
  have hp0 : (p : k) ≠ 0 := by
    intro h
    exact hp.ne_zero (Subtype.ext h)
  have hle : ValuativeRel.valuation k (p : k) ≤ 1 := p.2
  have hnu : ¬ IsUnit p := hp.not_isUnit
  have hlt : ValuativeRel.valuation k (p : k) < 1 := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd ((Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).2 h) hnu
  refine ⟨p, p.2, hp0, hlt, ?_, hp⟩
  intro x hx
  have hxi : x ∈ (ValuativeRel.valuation k).integer := le_of_lt hx
  set y : (ValuativeRel.valuation k).integer := ⟨x, hxi⟩ with hy
  have hynu : y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation k).integer := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).1 hu
    exact absurd this (ne_of_lt hx)
  rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hynu
  obtain ⟨c, hc⟩ := hynu
  have hxc : x = (p : k) * (c : k) := by
    have := congrArg (Subtype.val) hc
    simpa using this
  rw [hxc, map_mul]
  have hc1 : ValuativeRel.valuation k (c : k) ≤ 1 := c.2
  exact mul_le_of_le_one_right' hc1
end GlobalTheory.CompanionTheory.LocalField
end

section
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.ContraCusp

theorem contra_facts : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ),
    (contra σ.ρ).IsIrreducible ∧ IsCuspidal (contra σ.ρ) ∧
    ∃ (z : GL (Fin (m + 1)) k) (ϖ : k) (ω : ℂ), (z : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ϖ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ∧
      ValuativeRel.valuation k ϖ < 1 ∧ ϖ ≠ 0 ∧ ω ≠ 0 ∧ (∀ a, σ.ρ z a = ω • a) ∧ ∀ l, contra σ.ρ z l = ω⁻¹ • l := by
  intro k _ _ _ _ m σ hc
  have hadm : IsAdmissible σ.ρ :=
    PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k (m + 1) _ σ.ρ σ.smooth σ.irr
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k (m + 1)
  refine ⟨GlobalTheory.ContraRefl.contra_isIrreducible hG hadm σ.irr,
    GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k (m + 1) _ _
      (GlobalTheory.CompanionTheory.DualCusp.isSupercuspidal_contra hG hadm
        (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k (m + 1) _ _ hc)), ?_⟩
  obtain ⟨ϖ, -, hϖ0, hϖ, -⟩ := GlobalTheory.CompanionTheory.LocalField.exists_uniformiser k
  obtain ⟨χ, -, hχ⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar σ.smooth σ.irr
  let t : kˣ := Units.mk0 ϖ hϖ0
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) t, ϖ, (χ t : ℂ), ?_, hϖ, hϖ0, (χ t).ne_zero,
    fun a => hχ t a, fun l => ?_⟩
  · ext i j
    simp [Matrix.GeneralLinearGroup.scalar, t, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  · refine Subtype.ext (LinearMap.ext fun v => ?_)
    have h1 : (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) t)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) t⁻¹ := (map_inv _ t).symm
    have h2 : ((χ t⁻¹ : ℂˣ) : ℂ) = ((χ t : ℂˣ) : ℂ)⁻¹ := by
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [contra_apply, h1, hχ t⁻¹ v, map_smul, h2]
    rfl

end GlobalTheory.CompanionTheory.ContraCusp
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_contragredient_central_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ),
    (contra σ.ρ).IsIrreducible ∧ IsCuspidal (contra σ.ρ) ∧
    ∃ (z : GL (Fin (m + 1)) k) (ϖ : k) (ω : ℂ), (z : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ϖ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ∧
      ValuativeRel.valuation k ϖ < 1 ∧ ϖ ≠ 0 ∧ ω ≠ 0 ∧ (∀ a, σ.ρ z a = ω • a) ∧ ∀ l, contra σ.ρ z l = ω⁻¹ • l := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ContraCusp.contra_facts
end

section
noncomputable section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.BZShell

theorem false_of_open_parts {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (hd : 0 < d) (R R' : MRep k d) (hR' : IsSmooth R'.ρ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Nontrivial V]
    (X : Representation ℂ (GL (Fin d) k) V) (Y : Representation ℂ (GL (Fin d) k) V') (hX : IsSmooth X) (hY : IsSmooth Y)
    (P : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hP : ∀ g a a', P (X g a) (Y g a') = ((dpow d (-2) g : ℂˣ) : ℂ) * P a a')
    (e : Fin d → k) (he : e ≠ 0)
    (hU : ∀ β : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
      (∀ g : GL (Fin d) k, (g : Matrix (Fin d) (Fin d) k).mulVec e = e → ∀ a a', β (X g a) (Y g a') =
        ((dpow d (-2) g : ℂˣ) : ℂ) * β a a') → ∃ c : ℂ, ∀ a a', β a a' = c * P a a')
    (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (ω ω' : ℂ) (hω : ∀ a, X z a = ω • a) (hω' : ∀ a, Y z a = ω' • a)
    (hωω : ω * ω' = ((dpow d (-2) z : ℂˣ) : ℂ))
    (B : R.V →ₗ[ℂ] R'.V →ₗ[ℂ] ℂ) (hB : ∀ p v v', B (R.ρ p v) (R'.ρ p v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (ι : SchF k d V →ₗ[ℂ] R.V) (hι : Function.Injective ι) (hιs : ∀ x f, ι (shiftF x f) = R.ρ (uM d x) (ι f))
    (hιg : ∀ g f, ι (actF X g f) = R.ρ (levi k d g) (ι f))
    (ι' : SchF k d V' →ₗ[ℂ] R'.V) (hιs' : ∀ x f, ι' (shiftF x f) = R'.ρ (uM d x) (ι' f))
    (hιg' : ∀ g f, ι' (actF Y g f) = R'.ρ (levi k d g) (ι' f))
    (hr : ∀ x v, R'.ρ (uM d x) v - v ∈ LinearMap.range ι') : False := by
  let c : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ := B.compl₁₂ ι ι'
  have hcv : ∀ f f', c f f' = B (ι f) (ι' f') := fun _ _ => rfl
  have hT : ∀ x f f', c (shiftF x f) (shiftF x f') = c f f' := by
    intro x f f'
    rw [hcv, hcv, hιs, hιs']
    exact hB _ _ _
  have hG : ∀ g f f', c (actF X g f) (actF Y g f') = c f f' := by
    intro g f f'
    rw [hcv, hcv, hιg, hιg']
    exact hB _ _ _
  have hC := GlobalTheory.T.invariant_pairing_twisted_modulus d hd X Y hX hY P hP e he hU z ϖ hz hϖ hϖ0 ω ω' hω hω' hωω c hT hG
  exact GlobalTheory.T.nondegenerate_unipotent_pairing_schwartz d hd R R' hR' B (fun x v v' => hB _ v v') hn ι hι hιs ι' hιs' hr hC

theorem false_of_open_dual {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ) (R R' : MRep k (m + 1)) (hR' : IsSmooth R'.ρ)
    (B : R.V →ₗ[ℂ] R'.V →ₗ[ℂ] ℂ) (hB : ∀ p v v', B (R.ρ p v) (R'.ρ p v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (ι : SchF k (m + 1) σ.V →ₗ[ℂ] R.V) (hι : Function.Injective ι) (hιs : ∀ x f, ι (shiftF x f) = R.ρ (uM (m + 1) x) (ι f))
    (hιg : ∀ g f, ι (actF ((gOf σ).tw (-1 / 2)).ρ g f) = R.ρ (levi k (m + 1) g) (ι f))
    (ι' : SchF k (m + 1) (smoothPart σ.ρ.dual) →ₗ[ℂ] R'.V) (hιs' : ∀ x f, ι' (shiftF x f) = R'.ρ (uM (m + 1) x) (ι' f))
    (hιg' : ∀ g f, ι' (actF (((gDual σ).tw (-1)).tw (-1 / 2)).ρ g f) = R'.ρ (levi k (m + 1) g) (ι' f))
    (hr : ∀ x v, R'.ρ (uM (m + 1) x) v - v ∈ LinearMap.range ι') : False := by
  obtain ⟨hci, hcc, z, ϖ, ω, hz, hϖ, hϖ0, hω0, hzσ, hzc⟩ := GlobalTheory.T.cuspidal_contragredient_central_character m σ hc
  have hsm : ∀ s : ℝ, IsSmoothChar (absPow k (s : ℂ)) := fun s => GlobalTheory.LocGL.isSmoothChar_absPow _
  have hsB' : IsSmooth ((gDual σ).tw (-1)).ρ := isSmooth_twist (isSmooth_contra _) (hsm (-1)).detChar
  let X : Representation ℂ (GL (Fin (m + 1)) k) σ.V := twist σ.ρ (dpow (m + 1) (-1 / 2))
  let Y : Representation ℂ (GL (Fin (m + 1)) k) (smoothPart σ.ρ.dual) := twist (twist (contra σ.ρ) (dpow (m + 1) (-1))) (dpow (m + 1) (-1 / 2))
  let P : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ := LinearMap.flip (smoothPart σ.ρ.dual).subtype
  have hadd : ∀ (s t : ℝ) (g : GL (Fin (m + 1)) k), ((dpow (m + 1) (s + t) g : ℂˣ) : ℂ) =
      ((dpow (m + 1) s g : ℂˣ) : ℂ) * ((dpow (m + 1) t g : ℂˣ) : ℂ) := by
    intro s t g
    simp only [dpow, detChar_apply, Complex.ofReal_add, absPow_add, MonoidHom.mul_apply, Units.val_mul]
  have hne : ∀ (s : ℝ) (g : GL (Fin (m + 1)) k), ((dpow (m + 1) s g : ℂˣ) : ℂ) ≠ 0 := fun s g => Units.ne_zero _
  have hXa : ∀ g a, X g a = ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) • σ.ρ g a := fun g a => rfl
  have hYa : ∀ g l, Y g l = ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) • ((dpow (m + 1) (-1) g : ℂˣ) : ℂ) • contra σ.ρ g l := fun g l => rfl
  have hsc : ∀ g : GL (Fin (m + 1)) k, ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * (((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * ((dpow (m + 1) (-1) g : ℂˣ) : ℂ)) =
      ((dpow (m + 1) (-2) g : ℂˣ) : ℂ) := by
    intro g
    rw [← hadd, ← hadd]
    congr 3
    norm_num
  have hPinv : ∀ g a l, P (σ.ρ g a) (contra σ.ρ g l) = P a l := by
    intro g a l
    show (contra σ.ρ g l : Module.Dual ℂ σ.V) (σ.ρ g a) = (l : Module.Dual ℂ σ.V) a
    rw [contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hP : ∀ g a l, P (X g a) (Y g l) = ((dpow (m + 1) (-2) g : ℂˣ) : ℂ) * P a l := by
    intro g a l
    rw [hXa, hYa]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hPinv]
    rw [← hsc g]
    ring
  have hsX : IsSmooth X := isSmooth_twist σ.smooth (hsm _).detChar
  have hsY : IsSmooth Y := isSmooth_twist hsB' (hsm _).detChar
  have he : (Pi.single (Fin.last m) 1 : Fin (m + 1) → k) ≠ 0 := by
    intro h
    simpa using congrFun h (Fin.last m)
  have hU : ∀ β : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ,
      (∀ g : GL (Fin (m + 1)) k, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (Pi.single (Fin.last m) 1) = Pi.single (Fin.last m) 1 →
        ∀ a a', β (X g a) (Y g a') = ((dpow (m + 1) (-2) g : ℂˣ) : ℂ) * β a a') →
      ∃ c : ℂ, ∀ a a', β a a' = c * P a a' := by
    intro β hβ
    refine GlobalTheory.T.cuspidal_mirabolic_invariant_pairing_scalar m σ hc β fun g hg a l => ?_
    have h := hβ g hg a l
    rw [hXa, hYa] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [← hsc g] at h
    have h2 : ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * (((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * ((dpow (m + 1) (-1) g : ℂˣ) : ℂ)) ≠ 0 :=
      mul_ne_zero (hne _ _) (mul_ne_zero (hne _ _) (hne _ _))
    refine mul_left_cancel₀ h2 ?_
    rw [← h]
    ring
  have hzX : ∀ a, X z a = (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * ω) • a := by
    intro a
    rw [hXa, hzσ, smul_smul]
  have hzY : ∀ l, Y z l = (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * (((dpow (m + 1) (-1) z : ℂˣ) : ℂ) * ω⁻¹)) • l := by
    intro l
    rw [hYa, hzc, smul_smul, smul_smul, mul_assoc]
  have hωω : (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * ω) * (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * (((dpow (m + 1) (-1) z : ℂˣ) : ℂ) * ω⁻¹)) =
      ((dpow (m + 1) (-2) z : ℂˣ) : ℂ) := by
    rw [← hsc z]
    field_simp
  haveI : Nontrivial σ.V := by
    have hi := σ.irr
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    apply (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    apply Subrepresentation.ext
    ext x
    rw [Subsingleton.elim x 0]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  exact false_of_open_parts (m + 1) (Nat.succ_pos m) R R' hR' X Y hsX hsY P hP _ he hU z ϖ hz hϖ hϖ0 _ _ hzX hzY hωω B hB hn ι hι hιs hιg ι' hιs' hιg' hr

theorem red_cusp_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible := by
  intro k _ _ _ _ d hd σ hc hirr
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨ψ, hψc, hψ1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one k
  have hψc' : Continuous (ψ⁻¹ : AddChar k Circle) := by
    have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
    rw [this]
    exact hψc.comp continuous_neg
  have hψ1' : ψ⁻¹ ≠ 1 := inv_ne_one.2 hψ1
  obtain ⟨hci, hcc, -⟩ := GlobalTheory.T.cuspidal_contragredient_central_character m σ hc
  have hsm : ∀ s : ℝ, IsSmoothChar (absPow k (s : ℂ)) := fun s => GlobalTheory.LocGL.isSmoothChar_absPow _
  have hsA : IsSmooth ((gOf σ).tw 1).ρ := isSmooth_twist σ.smooth (hsm 1).detChar
  have hsB : IsSmooth (gOf σ).ρ := σ.smooth
  have hsA' : IsSmooth (gDual σ).ρ := isSmooth_contra _
  have hsB' : IsSmooth ((gDual σ).tw (-1)).ρ := isSmooth_twist (isSmooth_contra _) (hsm (-1)).detChar
  obtain ⟨B₀, hB₀, hn₀⟩ := GlobalTheory.T.invariant_pairing_segment_product m σ hc hirr
  obtain ⟨B, hB, hn⟩ := GlobalTheory.T.invariant_pairing_iterated_derivative ψ hψc hψ1 m _ _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_prod _ _))
    (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_prod _ _)) B₀ hB₀ hn₀
  obtain ⟨ι, hι, hιs, hιg, -⟩ := GlobalTheory.T.schwartz_functions_embed_cuspidal_derivative ψ hψc hψ1 m ((gOf σ).tw 1) (gOf σ) hsA hsB
    (GlobalTheory.LocGL.isIrreducible_twist σ.irr _) (GlobalTheory.LocGL.isCuspidal_twist hc (hsm 1))
  obtain ⟨ι', -, hιs', hιg', hr⟩ := GlobalTheory.T.schwartz_functions_embed_cuspidal_derivative ψ⁻¹ hψc' hψ1' m (gDual σ) ((gDual σ).tw (-1)) hsA' hsB' hci hcc
  exact false_of_open_dual m σ hc _ _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_iterN ψ⁻¹ m
    (isSmooth_gres (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_prod _ _))))
    B hB hn ι hι hιs hιg ι' hιs' hιg' hr

end GlobalTheory.CompanionTheory.BZShell
end
end

section
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.BZReducible

theorem cusp_times_nu_reducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible :=
  fun k _ _ _ _ d hd σ hσ => GlobalTheory.CompanionTheory.BZShell.red_cusp_nu k d hd σ hσ

end GlobalTheory.CompanionTheory.BZReducible
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_length_two_reducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZReducible.cusp_times_nu_reducible
end
