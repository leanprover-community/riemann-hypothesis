import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import ReciprocityTheory.DualLattices.ProdDvdOfIso
import ReciprocityTheory.DualLattices.InvolutionPermApplyZero
import ReciprocityTheory.DualLattices.PowMemCarrier
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.HasColenNotUniqueWithoutGuard
import Development.WeilBound.CoreStatements.HodgeTatePoints.PowCongr
import Development.WeilBound.CoreStatements.HodgeTatePoints.RdBase
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExistsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalCharacterStatement
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.HodgeTatePoints.ANonunit
import Development.WeilBound.CoreStatements.HodgeTatePoints.RbAflat
import Development.WeilBound.CoreStatements.HodgeTatePoints.RcFlag
import Development.WeilBound.CoreStatements.HodgeTatePoints.RdFlagFin
import Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfProdEq
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalCharacterIdealPowers
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowers
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExists
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractRestriction
import Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfPowMul

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_ideals_eq_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, idealX AA.carrier K t χ = ⊤ → ∃ τ : MulChar F R, IsFund p τ ∧ idealD p AA.carrier K t τ = ⊤ := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hFS K t ht hGen χ hχ
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  have hval : ∀ g ∈ AA.carrier, ∀ x, ∃ r : R, algebraMap R C r = g x := fun g hg =>
    (show ∀ x, ∃ r : R, algebraMap R C r = g x from AA.le_int hg)
  have hle : ∀ g ∈ AA.carrier, ∀ x, v (g x) ≤ 1 := by
    intro g hg x
    obtain ⟨r, hr⟩ := hval g hg x
    rw [← hr]
    exact hv.map_le_one r
  have hpv : ∀ z ∈ pInt (C := C) R p, v z < 1 := by
    intro z hz
    unfold pInt at hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [Algebra.smul_def, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hv.map_le_one a)) hp
  have hinv : ∀ g, g ∈ invFun AA.carrier K.toAddSubgroup →
      g ∈ AA.carrier ∧ ∀ x, ∀ k ∈ K.toAddSubgroup, g (x + k) = g x := fun g hg => hg
  have hinvI : ∀ g, (g ∈ AA.carrier ∧ ∀ x, ∀ k ∈ K.toAddSubgroup, g (x + k) = g x) →
      g ∈ invFun AA.carrier K.toAddSubgroup := fun g hg => hg
  have hadd : ∀ g, g ∈ addFun (C := C) R p N →
      ∀ x y, g (x + y) - g x - g y ∈ pInt (C := C) R p := fun g hg => hg
  have h1 : (1 : R) ∈ idealX AA.carrier K t χ := by
    rw [hχ]
    exact Submodule.mem_top
  obtain ⟨g0, hg0, hg0e⟩ := Submodule.mem_map.1
    (show LinearMap.toSpanSingleton R (F → C) (fun a => algebraMap R C (χ a)) 1 ∈
      stepOrder AA.carrier K t from h1)
  have hg0a : ∀ a : F, g0 (a • t) = algebraMap R C (χ a) := by
    intro a
    have := congrFun hg0e a
    simpa [LinearMap.funLeft_apply, LinearMap.toSpanSingleton_apply] using this
  have hg0t : g0 t = 1 := by simpa using hg0a 1
  have hg0z : g0 0 = 0 := by
    have e := hg0a 0
    rwa [zero_smul, MulChar.map_zero, map_zero] at e
  obtain ⟨h, hA, hh⟩ : ∃ h ∈ afFun p (invFun AA.carrier K.toAddSubgroup),
      ¬ v (h t - h 0) < 1 := by
    by_contra hcon
    push Not at hcon
    have key : ∀ φ ∈ Algebra.adjoin R
        ((afFun p (invFun AA.carrier K.toAddSubgroup) : Submodule R (N → C)) : Set (N → C)),
        φ ∈ AA.carrier ∧ v (φ t - φ 0) < 1 := by
      intro φ hφ
      induction hφ using Algebra.adjoin_induction with
      | mem x hx =>
        have hx' := Submodule.mem_inf.1 (SetLike.mem_coe.1 hx)
        exact ⟨(hinv x hx'.1).1, hcon x (SetLike.mem_coe.1 hx)⟩
      | algebraMap r =>
        refine ⟨?_, ?_⟩
        · rw [Algebra.algebraMap_eq_smul_one]
          exact AA.carrier.smul_mem r AA.one_mem
        · simp
      | add x y _ _ hx hy =>
        refine ⟨AA.carrier.add_mem hx.1 hy.1, ?_⟩
        have e : (x + y) t - (x + y) 0 = (x t - x 0) + (y t - y 0) := by
          simp only [Pi.add_apply]
          ring
        rw [e]
        exact v.map_add_lt hx.2 hy.2
      | mul x y _ _ hx hy =>
        refine ⟨AA.mul_mem x y hx.1 hy.1, ?_⟩
        have e : (x * y) t - (x * y) 0 = x t * (y t - y 0) + y 0 * (x t - x 0) := by
          simp only [Pi.mul_apply]
          ring
        rw [e]
        refine v.map_add_lt ?_ ?_
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hle x hx.1 t)) hy.2
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hle y hy.1 0)) hx.2
    have hk := (key g0 ((show invFun AA.carrier K.toAddSubgroup ≤ _ from hGen) hg0)).2
    rw [hg0t, hg0z, sub_zero, map_one] at hk
    exact lt_irrefl _ hk
  have hAi := Submodule.mem_inf.1 hA
  obtain ⟨hM, hK⟩ := hinv h hAi.1
  have hAd := hadd h hAi.2
  obtain ⟨r0, hr0⟩ := hval h hM 0
  have h0p : h 0 ∈ pInt (C := C) R p := by
    have h00 := hAd 0 0
    rw [add_zero, show h 0 - h 0 - h 0 = -h 0 by ring] at h00
    simpa using (pInt (C := C) R p).neg_mem h00
  obtain ⟨h', h'apply, h'M⟩ : ∃ h' : N → C, (∀ x, h' x = h x - h 0) ∧ h' ∈ AA.carrier :=
    ⟨h - r0 • (1 : N → C), fun x => by
      show h x - (r0 • (1 : N → C)) x = h x - h 0
      rw [Pi.smul_apply, Pi.one_apply, Algebra.smul_def, mul_one, hr0],
      AA.carrier.sub_mem hM (AA.carrier.smul_mem r0 AA.one_mem)⟩
  have h'z : h' 0 = 0 := by rw [h'apply, sub_self]
  have h'inv : h' ∈ invFun AA.carrier K.toAddSubgroup :=
    hinvI h' ⟨h'M, fun x k hk => by rw [h'apply, h'apply, hK x k hk]⟩
  have h'add : h' ∈ addFun (C := C) R p N := by
    show ∀ x y, h' (x + y) - h' x - h' y ∈ pInt (C := C) R p
    intro x y
    have e : h' (x + y) - h' x - h' y = (h (x + y) - h x - h y) + h 0 := by
      rw [h'apply, h'apply, h'apply]
      ring
    rw [e]
    exact (pInt (C := C) R p).add_mem (hAd x y) h0p
  have h'af : h' ∈ afFun p AA.carrier := by
    unfold afFun
    exact Submodule.mem_inf.2 ⟨h'M, h'add⟩
  have h'aug : h' ∈ augIdeal AA.carrier := by
    unfold augIdeal
    exact Submodule.mem_inf.2 ⟨h'M, by simp [LinearMap.mem_ker, h'z]⟩
  have h't : ¬ v (h' t) < 1 := by
    rw [h'apply]
    exact hh
  obtain ⟨σ, hσ⟩ := PositivityTheory.HtPt.Rb.fund_ex p C v R hv hp F f hc
  obtain ⟨P1, P2, P3, P4, -⟩ :=
    PositivityTheory.HtPt.Rb.proj_props p C v R hv hp F f hc N AA hFS σ hσ h' h'aug
  obtain ⟨m, -, hm⟩ : ∃ m ∈ Finset.Icc 1 (p ^ f - 1), ¬ v (proj (σ ^ m) h' t) < 1 := by
    by_contra hcon
    push Not at hcon
    apply h't
    rw [P2, Finset.sum_apply]
    exact v.map_sum_lt one_ne_zero hcon
  have hτ : IsFund p (σ ^ m) := by
    by_contra hnf
    have hpf := PositivityTheory.HtPt.Rb.proj_nf p C v R hv hp F f hc N AA hFS h' h'af (σ ^ m) hnf
    exact hm (hpv _ (PositivityTheory.HtPt.Rb.mem_pFun.1 hpf t))
  refine ⟨σ ^ m, hτ, ?_⟩
  have hgE : proj (σ ^ m) h' ∈ AA.carrier ∧ ∀ (a : F) x,
      proj (σ ^ m) h' (a • x) = algebraMap R C ((σ ^ m) a) * proj (σ ^ m) h' x := P1 (σ ^ m)
  have hgI := hinv _ (P4 K h'inv (σ ^ m))
  have hgA : proj (σ ^ m) h' ∈ afFun p AA.carrier := P3 h'af (σ ^ m)
  generalize proj (σ ^ m) h' = g at hgE hgI hgA hm
  obtain ⟨u, hu⟩ := hval g hgE.1 t
  have hvu : v (algebraMap R C u) = 1 := by
    rw [hu]
    exact le_antisymm (hle g hgE.1 t) (not_lt.1 hm)
  have huU : IsUnit u := by
    refine hv.isUnit_of_one (isUnit_iff_ne_zero.2 ?_) hvu
    intro h0
    rw [h0, map_zero] at hvu
    exact zero_ne_one hvu
  have hg0' : g 0 = 0 := by
    have e := hgE.2 0 0
    rwa [zero_smul, MulChar.map_zero, map_zero, zero_mul] at e
  refine (Ideal.eq_top_iff_one _).2 ?_
  show ∃ G ∈ afFun p AA.carrier,
    (∀ (a : F) x, G (a • x) - algebraMap R C ((σ ^ m) a) * G x ∈ pInt (C := C) R p) ∧
    (∀ k ∈ K, G k ∈ pInt (C := C) R p) ∧ G t - algebraMap R C 1 ∈ pInt (C := C) R p
  refine ⟨(↑huU.unit⁻¹ : R) • g, (afFun p AA.carrier).smul_mem _ hgA, ?_, ?_, ?_⟩
  · intro a x
    have e : ((↑huU.unit⁻¹ : R) • g) (a • x) - algebraMap R C ((σ ^ m) a) *
        ((↑huU.unit⁻¹ : R) • g) x = 0 := by
      simp only [Pi.smul_apply, hgE.2 a x, Algebra.smul_def]
      ring
    rw [e]
    exact Submodule.zero_mem _
  · intro k hk
    have hgk : g k = 0 := by
      have e := hgI.2 0 k hk
      rwa [zero_add, hg0'] at e
    simp [hgk]
  · have e : ((↑huU.unit⁻¹ : R) • g) t - algebraMap R C 1 = 0 := by
      rw [Pi.smul_apply, Algebra.smul_def, ← hu, ← map_mul, huU.val_inv_mul, sub_self]
    rw [e]
    exact Submodule.zero_mem _
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_ideals_eq_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, idealX AA.carrier K t χ = ⊤ → ∃ τ : MulChar F R, IsFund p τ ∧ idealD p AA.carrier K t τ = ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.hopf_order_ideals_eq_top
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) := by
  first | exact @PositivityTheory.HtPt.Rfin.a_nonunit | exact PositivityTheory.HtPt.Rfin.a_nonunit
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_quotient : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem idealD_pow_mem : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) :=
  @PositivityTheory.HtPt.Rd.a_pow

end GlobalTheory.CompanionTheory.Ar.GR
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_length : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem idealX_le_idealD : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → idealX AA.carrier K t τ ≤ idealD p AA.carrier K t τ := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hq N _ _ _ _ AA hst K t ht hgen τ hτ
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨⟨S, hS, hSst⟩, -⟩ := GlobalTheory.T.stable_hopf_order_subgroup_translation p C v R hv hp F f hq N AA hst K t ht
  obtain ⟨hord, -, hfund, hfunds, -⟩ := GlobalTheory.T.teichmuller_character_order_generates p C v R hv hp F f hq τ hτ
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    rw [hq, pow_zero] at this
    exact lt_irrefl _ this
  have hq1 : 1 < p ^ f := Nat.one_lt_pow hf0 hp1
  have hper1 : τ ^ p ^ f = τ := by
    have : p ^ f = orderOf τ + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hper : ∀ m, τ ^ p ^ (f * m) = τ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hper1]
  have hprin : ∀ χ : MulChar F R, ∃ c : R, c ≠ 0 ∧ xIdeal S.carrier χ = Ideal.span {c} :=
    fun χ => (GlobalTheory.T.character_ideal_principal_eigen p C v R hv hp F f hq S hSst χ).1
  choose c0 hc0 hc0' using hprin
  let c : ℕ → R := fun n => c0 (τ ^ p ^ n)
  have hcX : ∀ n, idealX AA.carrier K t (τ ^ p ^ n) = Ideal.span {c n} := by
    intro n
    rw [idealX, ← hS]
    exact hc0' _
  have hom := GlobalTheory.T.fundamental_ideal_frobenius_product p C v R hv hp F f hq S hSst τ hτ c (fun n => hc0' _)
  have hcper : ∀ m, c (f * m) = c 0 := by
    intro m
    simp only [c, hper m, pow_zero, pow_one]
  let y : ℕ → NNReal := fun n => v (algebraMap R C (c n))
  have hy1 : ∀ n, y n ≤ 1 := fun n => hv.map_le_one _
  have hy0 : ∀ n, y n ≠ 0 := by
    intro n
    refine (Valuation.ne_zero_iff _).2 fun h => hc0 (τ ^ p ^ n) (hv.hom_inj ?_)
    simpa [c] using h
  have hle : ∀ n, y n ^ p ≤ y (n + 1) := by
    intro n
    obtain ⟨δ, hδ⟩ := (hom n).2.1
    have : y n ^ p = v (algebraMap R C δ) * y (n + 1) := by
      simp only [y]
      rw [← map_pow, ← map_pow, hδ, map_mul, map_mul]
    rw [this]
    exact mul_le_of_le_one_left' (hv.map_le_one _)
  have hpowp : ∀ n, (τ ^ p ^ n) ^ p = τ ^ p ^ (n + 1) := by
    intro n
    rw [← pow_mul, ← pow_succ]
  have hlt : ∀ n, y n ^ p < y (n + 1) → c (n + 1) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + 1)) := by
    intro n h
    have := GlobalTheory.T.stable_hopf_order_subgroup_quotient p C v R hv hp F f hq N AA hst K t ht hgen (τ ^ p ^ n) (hfund n)
      (c n) (c (n + 1)) (hcX n) (by rw [hpowp]; exact hcX (n + 1)) h
    rwa [hpowp] at this
  have heq : ∀ n, y n ^ p = y (n + 1) → c n ∈ idealD p AA.carrier K t (τ ^ p ^ n) →
      c (n + 1) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + 1)) := by
    intro n h hg
    have h1 := GlobalTheory.T.stable_hopf_order_subgroup_length p C v R hv hp F f hq N AA hst K t (τ ^ p ^ n) (c n) hg
    rw [hpowp] at h1
    obtain ⟨δ, hδ⟩ := (hom n).2.1
    have hv1 : v (algebraMap R C δ) = 1 := by
      have h2 : y n ^ p = v (algebraMap R C δ) * y (n + 1) := by
        simp only [y]
        rw [← map_pow, ← map_pow, hδ, map_mul, map_mul]
      rw [h] at h2
      exact (mul_right_cancel₀ (hy0 (n + 1)) (by rw [one_mul]; exact h2)).symm
    have hu : IsUnit δ := by
      refine hv.isUnit_of_one ?_ hv1
      refine IsUnit.mk0 _ fun h0 => ?_
      rw [h0, map_zero] at hv1
      exact zero_ne_one hv1
    rw [hδ] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).1 h1
  have hex : ∃ n, c n ∈ idealD p AA.carrier K t (τ ^ p ^ n) := by
    by_cases h : ∃ n, y n ^ p < y (n + 1)
    · obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, hlt n hn⟩
    · have hall : ∀ n, y n ^ p = y (n + 1) := fun n =>
        le_antisymm (hle n) (not_lt.1 fun h' => h ⟨n, h'⟩)
      have hyn : ∀ n, y n = y 0 ^ p ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [← hall n, ih, ← pow_mul, pow_succ]
      have hyf : y 0 ^ p ^ f = y 0 := by
        rw [← hyn f]
        have := hcper 1
        rw [mul_one] at this
        simp only [y, this]
      have hy01 : y 0 = 1 := by
        refine le_antisymm (hy1 0) (not_lt.1 fun h' => ?_)
        have := pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.2 (hy0 0)) h' hq1
        exact absurd hyf this.ne
      have hu : IsUnit (c 0) := by
        refine hv.isUnit_of_one ?_ hy01
        refine IsUnit.mk0 _ fun h0 => ?_
        have : y 0 = 0 := by simp only [y, h0, map_zero]
        exact hy0 0 this
      have hX : idealX AA.carrier K t τ = ⊤ := by
        have := hcX 0
        rw [pow_zero, pow_one] at this
        rw [this]
        exact Ideal.span_singleton_eq_top.2 hu
      obtain ⟨τ', hτ', hD⟩ := GlobalTheory.T.hopf_order_ideals_eq_top p C v R hv hp F f hq N AA hst K t ht hgen τ hX
      obtain ⟨n, -, rfl⟩ := hfunds τ' hτ'
      exact ⟨n, by rw [hD]; trivial⟩
  obtain ⟨n, hn⟩ := hex
  have hlater : ∀ k, c (n + k) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + k)) := by
    intro k
    induction k with
    | zero => exact hn
    | succ k ih =>
      rcases (hle (n + k)).lt_or_eq with h | h
      · exact hlt _ h
      · exact heq _ h ih
  have hnf : n ≤ f * n := Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hf0)
  have hg := hlater (f * n - n)
  rw [Nat.add_sub_cancel' hnf, hper n] at hg
  have hX := hcX (f * n)
  rw [hper n] at hX
  rw [hX]
  exact (Ideal.span_singleton_le_iff_mem _).2 hg

end GlobalTheory.CompanionTheory.Ar.GR
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_generation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → idealX AA.carrier K t τ ≤ idealD p AA.carrier K t τ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.idealX_le_idealD
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∃ d : Fin n → Fin f → R, (∀ (i : Fin n) (s : Fin f), idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ (s : ℕ)) = Ideal.span {d i s}) ∧ HasLen v R (AFQuot p AA.carrier) (∏ i, ∏ s, v (algebraMap R C (d i s))) := by
  first | exact @PositivityTheory.HtPt.Rb.flag_D | exact PositivityTheory.HtPt.Rb.flag_D
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_fundamental_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∃ d : Fin n → Fin f → R, (∀ (i : Fin n) (s : Fin f), idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ (s : ℕ)) = Ideal.span {d i s}) ∧ HasLen v R (AFQuot p AA.carrier) (∏ i, ∏ s, v (algebraMap R C (d i s))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem flag_colen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (cs : Fin n → NNReal) (cN : NNReal), (∀ i : Fin n, HasColen R v (stepOrder AA.carrier (flagSub b i) (b i)) (cs i)) → HasColen R v AA.carrier cN → cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N :=
  @PositivityTheory.HtPt.Rc.flag_colen

end GlobalTheory.CompanionTheory.Ar.GR
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_basis_ideals : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (cs : Fin n → NNReal) (cN : NNReal), (∀ i : Fin n, HasColen R v (stepOrder AA.carrier (flagSub b i) (b i)) (cs i)) → HasColen R v AA.carrier cN → cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.flag_colen
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r := by
  first | exact @PositivityTheory.HtPt.Rd.flag_om | exact PositivityTheory.HtPt.Rd.flag_om
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_basis_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) := by
  first | exact @PositivityTheory.HtPt.Rd.gr_partial | exact PositivityTheory.HtPt.Rd.gr_partial
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_basis_colength : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength
end

section
section
open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem grcount : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s :=
  PositivityTheory.HtPt.Rh.grcount

end GlobalTheory.CompanionTheory.Ar.GR
end

open scoped Matrix TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_inequalities_force_equality : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.grcount
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.RankOneColen

lemma two_mul_sum_digit (p f : ℕ) (j : Fin f) :
    (∑ d : Fin f → Fin p, (d j : ℕ)) * 2 = p ^ f * (p - 1) := by
  let e : (Fin f → Fin p) ≃ (Fin f → Fin p) := Equiv.arrowCongr (Equiv.refl _) Fin.revPerm
  have h1 : ∑ d : Fin f → Fin p, ((e d) j : ℕ) = ∑ d : Fin f → Fin p, (d j : ℕ) :=
    e.sum_comp (fun d => (d j : ℕ))
  have h2 : ∀ d : Fin f → Fin p, ((e d) j : ℕ) = p - ((d j : ℕ) + 1) := by
    intro d
    simp [e, Equiv.arrowCongr_apply, Fin.val_rev]
  simp only [h2] at h1
  rw [mul_two]
  nth_rewrite 2 [← h1]
  rw [← Finset.sum_add_distrib]
  have h3 : ∀ d : Fin f → Fin p, (d j : ℕ) + (p - ((d j : ℕ) + 1)) = p - 1 := by
    intro d; have := (d j).2; omega
  simp only [h3, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

lemma prod_digit_sq (p f : ℕ) (x : Fin f → NNReal) :
    (∏ d : Fin f → Fin p, ∏ j, x j ^ (d j : ℕ)) ^ 2 = (∏ j, x j) ^ (p ^ f * (p - 1)) := by
  have key : ∀ j : Fin f, (∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 = x j ^ (p ^ f * (p - 1)) := by
    intro j
    rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, two_mul_sum_digit]
  calc (∏ d : Fin f → Fin p, ∏ j, x j ^ (d j : ℕ)) ^ 2
      = (∏ j, ∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 := by rw [Finset.prod_comm]
    _ = ∏ j, (∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 := (Finset.prod_pow _ _ _).symm
    _ = ∏ j, x j ^ (p ^ f * (p - 1)) := Finset.prod_congr rfl (fun j _ => key j)
    _ = (∏ j, x j) ^ (p ^ f * (p - 1)) := Finset.prod_pow _ _ _

def num {p f : ℕ} (d : Fin f → Fin p) : ℕ := ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ)

lemma num_eq {p f : ℕ} (d : Fin f → Fin p) : num d = (finFunctionFinEquiv d : ℕ) := by
  rw [num, finFunctionFinEquiv_apply]

lemma num_lt {p f : ℕ} (d : Fin f → Fin p) : num d < p ^ f := by
  rw [num_eq]; exact Fin.isLt _

lemma num_inj {p f : ℕ} {d e : Fin f → Fin p} (h : num d = num e) : d = e := by
  rw [num_eq, num_eq] at h
  exact finFunctionFinEquiv.injective (Fin.ext h)

lemma num_surj {p f m : ℕ} (h : m < p ^ f) : ∃ d : Fin f → Fin p, num d = m :=
  ⟨finFunctionFinEquiv.symm ⟨m, h⟩, by rw [num_eq, Equiv.apply_symm_apply]⟩

lemma num_ne_zero_iff {p f : ℕ} (hp : 0 < p) (d : Fin f → Fin p) :
    num d ≠ 0 ↔ ∃ n, (d n : ℕ) ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    have hc' : ∀ n, (d n : ℕ) = 0 := fun n => by_contra (fun hn => hc ⟨n, hn⟩)
    apply h
    simp [num, hc']
  · rintro ⟨n, hn⟩ h
    apply hn
    rw [num] at h
    have h' := (Finset.sum_eq_zero_iff.mp h) n (Finset.mem_univ _)
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact h''
    · exact absurd h'' (pow_ne_zero _ hp.ne')

lemma prod_Icc_num {M : Type} [CommMonoid M] {p f : ℕ} (hp : 0 < p) (g : ℕ → M)
    (G : (Fin f → Fin p) → M) (h0 : ∀ d, num d = 0 → G d = 1)
    (h1 : ∀ d, num d ≠ 0 → g (num d) = G d) :
    ∏ m ∈ Finset.Icc 1 (p ^ f - 1), g m = ∏ d, G d := by
  classical
  have hfilt : ∏ d ∈ Finset.univ.filter (fun d : Fin f → Fin p => num d ≠ 0), G d = ∏ d, G d :=
    Finset.prod_filter_of_ne (fun d _ hG h0' => hG (h0 d h0'))
  rw [← hfilt]
  symm
  refine Finset.prod_bij (fun d _ => num d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    have := num_lt d
    rw [Finset.mem_Icc]
    omega
  · intro a _ b _ h
    exact num_inj h
  · intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨d, hd⟩ := num_surj (p := p) (f := f) (show m < p ^ f by omega)
    refine ⟨d, ?_, hd⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact (h1 d hd).symm

lemma mono_eq {C R F : Type} [Field C] [CommRing R] [Algebra R C] [Field F] {p f : ℕ}
    (hp : 0 < p) (σ : MulChar F R) (c : ℕ → R) (d : Fin f → Fin p) (hd : num d ≠ 0) (a : F) :
    ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ) =
      algebraMap R C ((∏ n : Fin f, c n ^ (d n : ℕ)) * (σ ^ num d) a) := by
  have hpow' : ∀ n : ℕ, (σ ^ p ^ n) a = σ a ^ p ^ n :=
    fun n => MulChar.pow_apply' σ (pow_ne_zero _ hp.ne') a
  rw [MulChar.pow_apply' σ hd a]
  simp only [hpow']
  simp only [map_mul, map_pow, map_prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, num]
  congr 2
  exact Finset.sum_congr rfl (fun n _ => Nat.mul_comm _ _)

lemma digits_zero {p f : ℕ} (hp : 0 < p) {d : Fin f → Fin p} (hd : num d = 0) (n : Fin f) :
    (d n : ℕ) = 0 := by
  by_contra h
  exact (num_ne_zero_iff hp d).2 ⟨n, h⟩ hd

end GlobalTheory.CompanionTheory.Ar.GR.RankOneColen

open GlobalTheory.CompanionTheory.Ar.GR.RankOneColen in

theorem _root_.GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → AA.carrier = Submodule.span R (Set.range fun (d : Fin f → Fin p) (a : F) => ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) ∧ ∀ cN, HasColen R v AA.carrier cN → cN ^ 2 = (∏ n : Fin f, v (algebraMap R C (c n))) ^ (p ^ f * (p - 1)) := by
  intro p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hst σ hσ c hc
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hT := GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hpv F f hcard AA hst σ hσ c hc
  obtain ⟨c', hc', hc'd⟩ : ∃ c' : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c' m}) ∧
      ∀ d : Fin f → Fin p, num d ≠ 0 → c' (num d) = ∏ n : Fin f, c n ^ (d n : ℕ) := by
    refine ⟨fun m => if h : m ≠ 0 ∧ m < p ^ f then
        ∏ n : Fin f, c n ^ ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ)
      else Classical.choose (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1, ?_, ?_⟩
    · intro m
      dsimp only
      by_cases h : m ≠ 0 ∧ m < p ^ f
      · rw [dif_pos h]
        have hd := Classical.choose_spec (num_surj h.2)
        have hne : ∃ n, ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ) ≠ 0 :=
          (num_ne_zero_iff hp _).mp (by rw [hd]; exact h.1)
        have e : σ ^ m = σ ^ num (Classical.choose (num_surj h.2)) := by rw [hd]
        rw [e]
        exact hT.2 _ hne
      · rw [dif_neg h]
        exact (Classical.choose_spec (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1).2
    · intro d hd
      dsimp only
      have h : num d ≠ 0 ∧ num d < p ^ f := ⟨hd, num_lt d⟩
      rw [dif_pos h]
      have := num_inj (Classical.choose_spec (num_surj h.2))
      rw [this]
  obtain ⟨hAug, hCar, hCol⟩ := r_decomp_relay p C v R hv hpv F f hcard AA hst σ hσ c' hc'
  refine ⟨?_, ?_⟩
  · have hset : Set.range (fun (d : Fin f → Fin p) (a : F) =>
          ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) =
        insert 1 ((fun m a => algebraMap R C (c' m * (σ ^ m) a)) '' ↑(Finset.Icc 1 (p ^ f - 1))) := by
      ext g
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_image, Finset.coe_Icc, Set.mem_Icc]
      constructor
      · rintro ⟨d, rfl⟩
        by_cases h0 : num d = 0
        · left
          funext a
          simp only [Pi.one_apply]
          exact Finset.prod_eq_one (fun n _ => by rw [digits_zero hp h0 n, pow_zero])
        · right
          refine ⟨num d, ⟨by omega, by have := num_lt d; omega⟩, ?_⟩
          funext a
          rw [mono_eq hp σ c d h0 a, hc'd d h0]
      · rintro (rfl | ⟨m, ⟨hm1, hm2⟩, rfl⟩)
        · refine ⟨fun _ => ⟨0, hp⟩, ?_⟩
          funext a
          simp only [Pi.one_apply]
          exact Finset.prod_eq_one (fun n _ => pow_zero _)
        · obtain ⟨d, rfl⟩ := num_surj (p := p) (f := f) (show m < p ^ f by omega)
          have h0 : num d ≠ 0 := by omega
          refine ⟨d, ?_⟩
          funext a
          rw [mono_eq hp σ c d h0 a, hc'd d h0]
    rw [hset, Submodule.span_insert, ← hAug, ← hCar]
  · intro cN hcN
    have huniq : cN = ∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c' m)) := by
      obtain ⟨B, hB, hBd⟩ := hcN
      obtain ⟨B', hB', hB'd⟩ := hCol
      obtain ⟨P, hPu, hP⟩ := AA.lat
      rw [← hBd, ← hB'd, valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB),
        valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB')]
    rw [huniq, prod_Icc_num hp (fun m => v (algebraMap R C (c' m)))
      (fun d => ∏ n : Fin f, v (algebraMap R C (c n)) ^ (d n : ℕ)) ?_ ?_]
    · exact prod_digit_sq p f (fun n => v (algebraMap R C (c n)))
    · intro d hd
      exact Finset.prod_eq_one (fun n _ => by rw [digits_zero hp hd n, pow_zero])
    · intro d hd
      simp only [hc'd d hd, map_prod, map_pow]
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_ideal_frobenius_valuation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → AA.carrier = Submodule.span R (Set.range fun (d : Fin f → Fin p) (a : F) => ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) ∧ ∀ cN, HasColen R v AA.carrier cN → cN ^ 2 = (∏ n : Fin f, v (algebraMap R C (c n))) ^ (p ^ f * (p - 1)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.NonFund

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N)

theorem aug_mul {g h : N → C} (hg : g ∈ augIdeal AA.carrier) (hh : h ∈ AA.carrier) :
    g * h ∈ augIdeal AA.carrier := by
  refine ⟨AA.mul_mem _ _ hg.1 hh, ?_⟩
  have h0 : g 0 = 0 := hg.2
  change g 0 * h 0 = 0
  rw [h0, zero_mul]

theorem sq_mul {g h : N → C} (hg : g ∈ sqIdeal (augIdeal AA.carrier)) (hh : h ∈ AA.carrier) :
    g * h ∈ sqIdeal (augIdeal AA.carrier) := by
  unfold sqIdeal at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact Submodule.subset_span ⟨a, ha, b * h, aug_mul AA hb hh, mul_assoc _ _ _⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

def Lev (k : ℕ) (g : N → C) : Prop :=
  g ∈ AA.carrier ∧ (1 ≤ k → g ∈ augIdeal AA.carrier) ∧
    (2 ≤ k → g ∈ sqIdeal (augIdeal AA.carrier))

theorem lev_one : Lev AA 0 1 :=
  ⟨AA.one_mem, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

theorem lev_mul {k l : ℕ} {g h : N → C} (hg : Lev AA k g) (hh : Lev AA l h) :
    Lev AA (k + l) (g * h) := by
  refine ⟨AA.mul_mem _ _ hg.1 hh.1, fun hk => ?_, fun hk => ?_⟩
  · by_cases h1 : 1 ≤ k
    · exact aug_mul AA (hg.2.1 h1) hh.1
    · rw [mul_comm]; exact aug_mul AA (hh.2.1 (by omega)) hg.1
  · by_cases h2 : 2 ≤ k
    · exact sq_mul AA (hg.2.2 h2) hh.1
    · by_cases h3 : 2 ≤ l
      · rw [mul_comm]; exact sq_mul AA (hh.2.2 h3) hg.1
      · exact Submodule.subset_span ⟨g, hg.2.1 (by omega), h, hh.2.1 (by omega), rfl⟩

theorem lev_pow {g : N → C} (hg : g ∈ augIdeal AA.carrier) (k : ℕ) : Lev AA k (g ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact lev_one AA
  | succ k ih =>
    rw [pow_succ]
    exact lev_mul AA ih ⟨hg.1, fun _ => hg, fun h => absurd h (by omega)⟩

theorem lev_prod {ι : Type} (s : Finset ι) (u : ι → N → C) (hu : ∀ i, u i ∈ augIdeal AA.carrier)
    (d : ι → ℕ) : Lev AA (∑ i ∈ s, d i) (∏ i ∈ s, u i ^ d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact lev_one AA
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact lev_mul AA (lev_pow AA (hu a) _) ih

theorem digits_single {f p : ℕ} (d : Fin f → ℕ) (n : Fin f) (hn : d n ≠ 0)
    (hs : ¬ 2 ≤ ∑ i, d i) : ∑ i : Fin f, d i * p ^ (i : ℕ) = p ^ (n : ℕ) := by
  have h := Finset.add_sum_erase Finset.univ d (Finset.mem_univ n)
  have h1 : d n = 1 := by omega
  have h0 : ∑ i ∈ Finset.univ.erase n, d i = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at h0
  rw [Finset.sum_eq_single n, h1, one_mul]
  · intro b _ hb
    rw [h0 b (Finset.mem_erase.2 ⟨hb, Finset.mem_univ b⟩), zero_mul]
  · intro h; exact absurd (Finset.mem_univ n) h

end GlobalTheory.CompanionTheory.Ar.GR.NonFund

open GlobalTheory.CompanionTheory.Ar.GR.NonFund in
theorem _root_.GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ χ : MulChar F R, ¬ IsFund p χ → eig AA.carrier χ ≤ sqIdeal (augIdeal AA.carrier) := by
  intro p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hc AA hA χ hχ g hg
  obtain ⟨σ, hσ⟩ := fund_ex_relay p C v R hv hp F f hc
  obtain ⟨-, hgen, hfund, -, -⟩ := FundGen.main p C v R hv hp F f hc σ hσ
  obtain ⟨m, hm1, hm2, rfl⟩ := hgen χ
  have hr := eig_rank_one p C v R hv hp F f hc AA hA
  choose c hc0 hcx using fun n : ℕ => (hr (σ ^ p ^ n)).1
  have hp0 : 0 < p := hpp.out.pos
  have hlt : m < p ^ f := by
    have := pow_pos hp0 f
    omega
  obtain ⟨d, hd⟩ : ∃ d : Fin f → Fin p, ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by
    refine ⟨finFunctionFinEquiv.symm ⟨m, hlt⟩, ?_⟩
    rw [← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]
  have hne : ∃ n, (d n : ℕ) ≠ 0 := by
    by_contra hcon
    have h0 : ∀ n, (d n : ℕ) = 0 := fun n => by
      by_contra h; exact hcon ⟨n, h⟩
    simp only [h0, zero_mul, Finset.sum_const_zero] at hd
    omega
  have hx := (GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hp F f hc AA hA σ hσ c hcx).2 d hne
  rw [hd] at hx
  have hs : 2 ≤ ∑ n, (d n : ℕ) := by
    by_contra hs
    obtain ⟨n, hn⟩ := hne
    have := digits_single (p := p) (fun n => (d n : ℕ)) n hn hs
    rw [hd] at this
    rw [this] at hχ
    exact hχ (hfund n)
  obtain ⟨c0, hc0m, rfl⟩ := ((hr (σ ^ m)).2 g).1 hg
  rw [hx, Ideal.mem_span_singleton'] at hc0m
  obtain ⟨r, rfl⟩ := hc0m
  let u : Fin f → F → C := fun n a => algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a)
  have hu : ∀ n, u n ∈ augIdeal AA.carrier := by
    intro n
    have h1 : u n ∈ eig AA.carrier (σ ^ p ^ (n : ℕ)) :=
      ((hr _).2 _).2 ⟨c n, by rw [hcx]; exact Ideal.mem_span_singleton_self _, rfl⟩
    refine ⟨h1.1, ?_⟩
    change algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) 0) = 0
    rw [MulChar.map_zero, mul_zero, map_zero]
  have hprod := (lev_prod AA Finset.univ u hu fun n => (d n : ℕ)).2.2 hs
  convert Submodule.smul_mem _ r hprod using 1
  funext a
  have ha : (σ ^ m) a = ∏ n : Fin f, ((σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ) := by
    rw [MulChar.pow_apply' _ (by omega), ← hd, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [MulChar.pow_apply' _ (pow_pos hp0 _).ne', ← pow_mul, mul_comm]
  rw [ha, mul_assoc, ← Finset.prod_mul_distrib, map_mul, map_prod, Pi.smul_apply,
    Algebra.smul_def, Finset.prod_apply]
  refine congrArg _ (Finset.prod_congr rfl fun n _ => ?_)
  rw [← mul_pow, map_pow, Pi.pow_apply]
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_fundamental_eigen_le_square_augmentation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ χ : MulChar F R, ¬ IsFund p χ → eig AA.carrier χ ≤ sqIdeal (augIdeal AA.carrier) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation
end

section
section
noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.FlagClose

section Val

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

lemma v_le_of_span_le (hv : v.Integers R) {a b : R} (h : Ideal.span {a} ≤ Ideal.span {b}) :
    v (algebraMap R C a) ≤ v (algebraMap R C b) := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.1 (h (Ideal.mem_span_singleton_self a))
  rw [map_mul, map_mul]
  exact mul_le_of_le_one_right' (hv.map_le_one u)

lemma v_eq_of_span_eq (hv : v.Integers R) {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    v (algebraMap R C a) = v (algebraMap R C b) :=
  le_antisymm (v_le_of_span_le hv h.le) (v_le_of_span_le hv h.ge)

lemma span_eq_of_le_of_v_eq (hv : v.Integers R) {c d : R} (hc : c ≠ 0)
    (h : Ideal.span {c} ≤ Ideal.span {d})
    (hvv : v (algebraMap R C c) = v (algebraMap R C d)) :
    Ideal.span {c} = Ideal.span {d} := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.1 (h (Ideal.mem_span_singleton_self c))
  have hu0 : u ≠ 0 := by rintro rfl; simp at hc
  have hd0 : d ≠ 0 := by rintro rfl; simp at hc
  have hinj := hv.hom_inj
  have hd1 : algebraMap R C d ≠ 0 := fun e => hd0 (hinj (by simpa using e))
  have hu1 : algebraMap R C u ≠ 0 := fun e => hu0 (hinj (by simpa using e))
  have hvd : v (algebraMap R C d) ≠ 0 := (Valuation.ne_zero_iff v).2 hd1
  have hvu : v (algebraMap R C u) = 1 := by
    rw [map_mul, map_mul] at hvv
    exact mul_left_cancel₀ hvd (by rw [hvv, mul_one])
  exact Ideal.span_singleton_mul_right_unit (hv.isUnit_of_one (IsUnit.mk0 _ hu1) hvu) d

lemma hasLen_le_one' (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (h : HasLen v R M x) : x ≤ 1 := by
  obtain ⟨m, c, -, rfl⟩ := h
  exact Finset.prod_le_one' fun i _ => hv.map_le_one _

end Val

lemma prod_fin_shift (f : ℕ) (G : ℕ → NNReal) (h : G f = G 0) (h0 : G 0 ≠ 0) :
    ∏ s : Fin f, G ((s : ℕ) + 1) = ∏ s : Fin f, G s := by
  rw [Fin.prod_univ_eq_prod_range (fun i => G (i + 1)), Fin.prod_univ_eq_prod_range G]
  have h1 := Finset.prod_range_succ' G f
  have h2 := Finset.prod_range_succ G f
  rw [h1, h] at h2
  exact mul_right_cancel₀ h0 h2

section Char

variable {R : Type} [CommRing R] {F : Type} [Field F] [Fintype F]

lemma pow_card_char (χ : MulChar F R) : χ ^ Fintype.card F = χ := by
  ext a
  rw [MulChar.pow_apply_coe, ← map_pow, FiniteField.pow_card]

lemma pow_period {p f : ℕ} (hf : Fintype.card F = p ^ f) (σ : MulChar F R) (s : ℕ) :
    σ ^ p ^ (s + f) = σ ^ p ^ s := by
  rw [pow_add, pow_mul, ← hf, pow_card_char]

lemma pow_period_mul {p f : ℕ} (hf : Fintype.card F = p ^ f) (σ : MulChar F R) (s k : ℕ) :
    σ ^ p ^ (s + f * k) = σ ^ p ^ s := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, pow_period hf, ih]

lemma pow_mod {p f : ℕ} (hf : Fintype.card F = p ^ f) (σ : MulChar F R) (s : ℕ) :
    σ ^ p ^ (s % f) = σ ^ p ^ s := by
  conv_rhs => rw [← Nat.mod_add_div s f]
  rw [pow_period_mul hf]

lemma prod_chars {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (σ : MulChar F R)
    (ho : orderOf σ = p ^ f - 1)
    (hfund : ∀ m, IsFund p (σ ^ m) → ∃ n < f, σ ^ m = σ ^ p ^ n)
    (L : MulChar F R → NNReal) (h1 : ∀ χ, ¬ IsFund p χ → L χ = 1) :
    ∏ m ∈ Finset.Icc 1 (p ^ f - 1), L (σ ^ m) = ∏ s : Fin f, L (σ ^ p ^ (s : ℕ)) := by
  have hp2 := hp.two_le
  have hle : ∀ n < f, 1 ≤ p ^ n ∧ p ^ n ≤ p ^ f - 1 := by
    intro n hn
    refine ⟨Nat.one_le_pow _ _ hp.pos, ?_⟩
    have h2 : p ^ (n + 1) ≤ p ^ f := Nat.pow_le_pow_right hp.pos hn
    have h3 : p ^ (n + 1) = p ^ n * p := pow_succ p n
    have h4 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.pos
    have h5 : p ^ n * 2 ≤ p ^ n * p := Nat.mul_le_mul_left _ hp2
    omega
  have hinj : Function.Injective (fun s : Fin f => p ^ (s : ℕ)) := fun a b e =>
    Fin.ext (Nat.pow_right_injective hp2 e)
  have himg : ∏ s : Fin f, L (σ ^ p ^ (s : ℕ)) =
      ∏ m ∈ (Finset.univ : Finset (Fin f)).image (fun s : Fin f => p ^ (s : ℕ)), L (σ ^ m) := by
    rw [Finset.prod_image (fun a _ b _ e => hinj e)]
  rw [himg]
  symm
  apply Finset.prod_subset
  · intro m hm
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hm
    exact Finset.mem_Icc.2 (hle s s.2)
  · intro m hm hnot
    apply h1
    intro hfm
    obtain ⟨n, hn, e⟩ := hfund m hfm
    apply hnot
    refine Finset.mem_image.2 ⟨⟨n, hn⟩, Finset.mem_univ _, ?_⟩
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.1 hm
    obtain ⟨hn1, hn2⟩ := hle n hn
    have hmod : m ≡ p ^ n [MOD orderOf σ] := pow_eq_pow_iff_modEq.1 e
    rw [ho] at hmod
    refine (Nat.ModEq.eq_of_abs_lt hmod ?_).symm
    rw [abs_lt]
    omega

end Char

end GlobalTheory.CompanionTheory.Ar.GR.FlagClose

namespace GlobalTheory.CompanionTheory.Ar.GR

open FlagClose in

theorem flagStatement_holds : FlagStatement := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ N _ _ _ _ AA hFS hT n b hG σ hσ
  obtain ⟨f, hf0, hf⟩ : ∃ f : ℕ, 0 < f ∧ Fintype.card F = p ^ f := by
    obtain ⟨k, -, e⟩ := FiniteField.card F p
    exact ⟨k, k.pos, e⟩
  have hpp : p.Prime := Fact.out
  obtain ⟨hord, -, hfp, hfund, -⟩ := GlobalTheory.T.teichmuller_character_order_generates p C v R hv hp F f hf σ hσ
  have hFp : ∀ s, IsFund p (σ ^ p ^ s) := hfp
  have hbK : ∀ i : Fin n, b i ∉ flagSub b i := fun i =>
    b.linearIndependent.notMem_span_image (by simp)
  have hstep := fun i : Fin n =>
    GlobalTheory.T.stable_hopf_order_subgroup_translation p C v R hv hp F f hf N AA hFS (flagSub b i) (b i) (hbK i)
  choose S hSc hSF using fun i => (hstep i).1
  have hres : ∀ i : Fin n, stepOrder AA.carrier (flagSub b i) (b i) =
      stepOrderRes AA.carrier (flagSub b i) (b i) := fun i => (hstep i).2
  choose c hc0 hcX using fun (i : Fin n) (s : ℕ) =>
    (GlobalTheory.T.character_ideal_principal_eigen p C v R hv hp F f hf (S i) (hSF i) (σ ^ p ^ s)).1
  have hom := fun i : Fin n =>
    GlobalTheory.T.fundamental_ideal_frobenius_product p C v R hv hp F f hf (S i) (hSF i) σ hσ (c i) (hcX i)
  choose δ hδ using fun (i : Fin n) (s : ℕ) => (hom i s).2.1
  have hδL : ∀ (i : Fin n) (s : ℕ), HasLen v R (OmType (S i).carrier (σ ^ p ^ (s + 1)))
      (v (algebraMap R C (δ i s))) := fun i s => (hom i s).2.2 _ (hδ i s)
  have hstepL : ∀ (i : Fin n) (s : ℕ),
      HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) (σ ^ p ^ (s + 1)))
        (v (algebraMap R C (δ i s))) := by
    intro i s
    rw [← hSc i]
    exact hδL i s
  have hXc : ∀ (i : Fin n) (s : ℕ),
      idealX AA.carrier (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} := by
    intro i s
    show xIdeal (stepOrder AA.carrier (flagSub b i) (b i)) (σ ^ p ^ s) = _
    rw [← hSc i]
    exact hcX i s
  obtain ⟨d, hdD, hdL⟩ := GlobalTheory.T.stable_hopf_order_fundamental_lengths p C v R hv hp F f hf N AA hFS σ hσ n b
  obtain ⟨cA, cN, cO, hcA, hcN, hcO, e1, e2⟩ := hT
  obtain ⟨hLex, hLprod⟩ := GlobalTheory.T.stable_hopf_order_fundamental_ideal p C v R hv hp F f hf N AA hFS σ hσ
  choose L hL0 hL using hLex

  have hnf : ∀ χ : MulChar F R, ¬ IsFund p χ → L χ = 1 := by
    intro χ hχ
    have hsub : ∀ i : Fin n,
        HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) 1 := by
      intro i
      rw [← hSc i]
      have hle := GlobalTheory.T.non_fundamental_eigen_le_square_augmentation p C v R hv hp F f hf (S i) (hSF i) χ hχ
      haveI : Subsingleton (OmType (S i).carrier χ) := by
        refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 ?_)
        intro x _
        exact hle x.2
      exact hasLen_subsingleton v R _
    have h1 := GlobalTheory.T.stable_hopf_order_basis_lengths p C v R hv hp F f hf N AA hFS n b χ (fun _ => 1) (L χ) hsub (hL χ)
    exact le_antisymm (hasLen_le_one' hv (hL χ)) (by simpa using h1)

  have hcN0 : cN ≠ 0 := by
    obtain ⟨B, hB, h⟩ := AA.lat
    have e := GlobalTheory.HopfOrderCheck.hasColen_unique v (fun r => hv.map_le_one r) hcN ⟨B, h, rfl⟩
    rw [e]
    exact (Valuation.ne_zero_iff v).2 hB.ne_zero

  have hvc0 : ∀ (i : Fin n) (s : ℕ), v (algebraMap R C (c i s)) ≠ 0 := fun i s =>
    (Valuation.ne_zero_iff v).2 fun e => hc0 i s (hv.hom_inj (by simpa using e))
  have hcmod : ∀ (i : Fin n) (s : ℕ), Ideal.span {c i (s % f)} = Ideal.span {c i s} := by
    intro i s
    rw [← hXc, ← hXc, pow_mod hf]
  have hvper : ∀ (i : Fin n), v (algebraMap R C (c i f)) = v (algebraMap R C (c i 0)) := by
    intro i
    have h := hcmod i f
    rw [Nat.mod_self] at h
    exact (v_eq_of_span_eq hv h).symm
  have hxD : ∀ (t : Fin n) (s : Fin f),
      v (algebraMap R C (c t s)) ≤ v (algebraMap R C (d t s)) := by
    intro t s
    have h := GlobalTheory.T.stable_hopf_order_subgroup_generation p C v R hv hp F f hf N AA hFS (flagSub b t) (b t) (hbK t) (hG t)
      (σ ^ p ^ (s : ℕ)) (hFp s)
    rw [hXc, hdD] at h
    exact v_le_of_span_le hv h
  have hDA : ∏ t, ∏ s, v (algebraMap R C (d t s)) = cA := hasLen_unique hv hdL hcA

  choose cs hcs using fun i : Fin n => hasColen_of_lat v (S i).lat
  have hcsq : ∀ i : Fin n, cs i ^ 2 =
      (∏ s : Fin f, v (algebraMap R C (c i s))) ^ (p ^ f * (p - 1)) := fun i =>
    (GlobalTheory.T.fundamental_ideal_frobenius_valuation p C v R hv hp F f hf (S i) (hSF i) σ hσ (c i) (hcX i)).2 _ (hcs i)
  have hcfl : cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N :=
    GlobalTheory.T.stable_hopf_order_basis_ideals p C v R hv hp F f hf N AA hFS n b cs cN
      (fun i => by rw [← hSc i]; exact hcs i) hcN
  have hxN : (∏ t, ∏ s : Fin f, v (algebraMap R C (c t s))) ^ (Fintype.card N * (p - 1)) =
      cN ^ 2 := by
    have hq : p ^ f ≠ 0 := pow_ne_zero _ hpp.ne_zero
    refine (pow_left_inj₀ zero_le' zero_le' hq).1 ?_
    calc ((∏ t, ∏ s : Fin f, v (algebraMap R C (c t s))) ^ (Fintype.card N * (p - 1))) ^ p ^ f
        = (∏ t, (∏ s : Fin f, v (algebraMap R C (c t s))) ^ (p ^ f * (p - 1))) ^ Fintype.card N := by
          rw [Finset.prod_pow, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = (∏ t, cs t ^ 2) ^ Fintype.card N := by simp only [hcsq]
      _ = (cN ^ 2) ^ p ^ f := by
          rw [Finset.prod_pow, ← pow_mul, pow_right_comm cN, hcfl, ← pow_mul, mul_comm 2]

  have hdx : ∏ t, ∏ s : Fin f, v (algebraMap R C (δ t s)) =
      (∏ t, ∏ s : Fin f, v (algebraMap R C (c t s))) ^ (p - 1) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t _ => ?_
    have hP : ∏ s : Fin f, v (algebraMap R C (c t s)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun s _ => hvc0 t s
    have hsh := prod_fin_shift f (fun s => v (algebraMap R C (c t s))) (hvper t) (hvc0 t 0)
    have hmul : (∏ s : Fin f, v (algebraMap R C (c t s))) ^ p =
        (∏ s : Fin f, v (algebraMap R C (δ t s))) *
          ∏ s : Fin f, v (algebraMap R C (c t s)) := by
      rw [← Finset.prod_pow]
      conv_rhs => rw [← hsh]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [← map_pow, ← map_pow, hδ, map_mul, map_mul]
    have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hpp.one_le).symm
    have h2 : (∏ s : Fin f, v (algebraMap R C (c t s))) ^ (p - 1) *
        ∏ s : Fin f, v (algebraMap R C (c t s)) =
        (∏ s : Fin f, v (algebraMap R C (c t s))) ^ p := by
      rw [← pow_succ, ← hp1]
    exact (mul_right_cancel₀ hP (h2.trans hmul)).symm
  have hrle : ∀ s : Fin f, ∏ t, v (algebraMap R C (δ t s)) ≤ L (σ ^ p ^ ((s : ℕ) + 1)) :=
    fun s => GlobalTheory.T.stable_hopf_order_basis_lengths p C v R hv hp F f hf N AA hFS n b (σ ^ p ^ ((s : ℕ) + 1))
      (fun i => v (algebraMap R C (δ i s))) _ (fun i => hstepL i s) (hL _)
  have hrO : ∏ s : Fin f, L (σ ^ p ^ ((s : ℕ) + 1)) = cO := by
    have h1 := prod_fin_shift f (fun s => L (σ ^ p ^ s))
      (by simpa using congrArg L (pow_period hf σ 0)) (hL0 _)
    have h2 := prod_chars hpp hf0 σ hord (fun m hm => hfund _ hm) L hnf
    have h3 := hasLen_unique hv (hLprod (fun m => L (σ ^ m)) (fun m _ => hL _)) hcO
    exact h1.trans (h2.symm.trans h3)
  obtain ⟨hDx, hlen⟩ := GlobalTheory.T.product_inequalities_force_equality (Fin n) (Fin f) (Fintype.card N) (p - 1) Fintype.card_pos
    (Nat.sub_pos_of_lt hpp.one_lt)
    (fun t s => v (algebraMap R C (c t s))) (fun t s => v (algebraMap R C (d t s)))
    (fun t s => v (algebraMap R C (δ t s))) (fun s => L (σ ^ p ^ ((s : ℕ) + 1))) cA cN cO hcN0
    hxD hDA hxN e1 hrle hrO hdx e2

  have hCD : ∀ (i : Fin n) (s : Fin f), Ideal.span {c i s} = Ideal.span {d i s} := by
    intro i s
    refine span_eq_of_le_of_v_eq hv (hc0 i s) ?_ (hDx i s).symm
    have h := GlobalTheory.T.stable_hopf_order_subgroup_generation p C v R hv hp F f hf N AA hFS (flagSub b i) (b i) (hbK i) (hG i)
      (σ ^ p ^ (s : ℕ)) (hFp s)
    rwa [hXc, hdD] at h
  have hD : ∀ (i : Fin n) (s : ℕ),
      idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} := by
    intro i s
    have hs : s % f < f := Nat.mod_lt _ hf0
    have h := hdD i ⟨s % f, hs⟩
    have h' := hCD i ⟨s % f, hs⟩
    simp only at h h'
    rw [pow_mod hf] at h
    rw [h, ← h', hcmod]
  have hsucc : ∀ s : ℕ, σ ^ p ^ (s % f + 1) = σ ^ p ^ (s + 1) := by
    intro s
    rw [pow_succ, pow_succ, pow_mul, pow_mul, pow_mod hf]
  have hall : ∀ s : ℕ, HasLen v R (OmType AA.carrier (σ ^ p ^ (s + 1)))
      (∏ i, v (algebraMap R C (δ i s))) := by
    intro s
    have hs : s % f < f := Nat.mod_lt _ hf0
    have h := hlen ⟨s % f, hs⟩
    simp only at h
    have hδe : ∀ i : Fin n, v (algebraMap R C (δ i s)) = v (algebraMap R C (δ i (s % f))) := by
      intro i
      have h2 := hδL i (s % f)
      rw [hsucc] at h2
      exact hasLen_unique hv (hδL i s) h2
    simp only [hδe]
    rw [h, hsucc]
    exact hL _
  refine ⟨c, δ, fun i s => ⟨hc0 i s, hXc i s, ?_, hD i s, hδ i s, hstepL i s⟩, hall, ?_⟩
  · rw [← hres i, ← hSc i]
    exact hcX i s
  · intro j s
    exact GlobalTheory.T.stable_hopf_order_basis_colength p C v R hv hp F f hf N AA hFS n b (σ ^ p ^ (s + 1))
      (fun i => v (algebraMap R C (δ i s))) (fun i => hstepL i s) (hall s) j

end GlobalTheory.CompanionTheory.Ar.GR
end
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_comparison_theorem : GlobalTheory.CompanionTheory.Ar.GR.FlagStatement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  first | exact @PositivityTheory.HtPt.Re.ret_tight | exact PositivityTheory.HtPt.Re.ret_tight
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_retract_elementary : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem flagConcl_directFactor_of_subquotient :
    SubquotientStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, (∀ x : N, p • x = 0) → IsAbFactor p AA.carrier → IsTight v p AA.carrier → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (Nw : Type) [AddCommGroup Nw] [Module F Nw] [Fintype Nw] [DecidableEq Nw] (i : Nw →+ N) (π : N →+ Nw), (∀ y, π (i y) = y) → (∀ h ∈ AA.carrier, (fun x => h (i (π x))) ∈ AA.carrier) → FStable F (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) → ∀ (n : ℕ) (b : Module.Basis (Fin n) F Nw) (σ : MulChar F R), IsFund p σ → FlagConcl v p (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) b σ := by
  intro hS p _ C _ _ _ v R _ _ hInt hp hcomp N _ _ _ AA hpN hab htight F _ _ _ _ Nw _ _ _ _ i π hπi
    hstab hFS n b σ hσ
  obtain ⟨⟨A', hA'⟩, -, hgen⟩ := GlobalTheory.T.hopf_order_retract_restriction p C v R hInt hp N AA Nw i π hπi hstab
  have ht' := GlobalTheory.T.hopf_order_retract_elementary p C v R hInt hp N hpN AA Nw i π hπi hstab htight
  rw [← hA'] at hFS ht' ⊢
  refine GlobalTheory.T.flag_comparison_theorem p C v R hInt hp F Nw A' hFS ht' n b ?_ σ hσ
  intro k
  rw [hA']
  exact hgen _ (hS p C v R hInt hp hcomp N AA.carrier hab _)

end GlobalTheory.CompanionTheory.Ar.GR
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_factor_tight_field_action : SubquotientStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, (∀ x : N, p • x = 0) → IsAbFactor p AA.carrier → IsTight v p AA.carrier → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (Nw : Type) [AddCommGroup Nw] [Module F Nw] [Fintype Nw] [DecidableEq Nw] (i : Nw →+ N) (π : N →+ Nw), (∀ y, π (i y) = y) → (∀ h ∈ AA.carrier, (fun x => h (i (π x))) ∈ AA.carrier) → FStable F (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) → ∀ (n : ℕ) (b : Module.Basis (Fin n) F Nw) (σ : MulChar F R), IsFund p σ → FlagConcl v p (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) b σ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.flagConcl_directFactor_of_subquotient
end
