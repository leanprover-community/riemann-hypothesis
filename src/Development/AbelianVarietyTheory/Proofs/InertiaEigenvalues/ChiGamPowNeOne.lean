import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCoeffOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SandZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocPrimeVNormalised
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenDiscConvergentRingWithExpansionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocAinfUntiltEpsOneEqZeta
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisConvergingOpenDisc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvaluationConvergentSeriesBcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeFreeOfCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeAinfSandwichInvertPi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGammaLayerPadicCoordinates

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

namespace GlobalTheory.HWL.LevExp

theorem eq_exp {F : Type} [Field F] [CharZero F] [Algebra ℚ F] (E : PowerSeries F)
    (h0 : PowerSeries.constantCoeff E = 1) (h1 : PowerSeries.derivative F E = E) :
    E = PowerSeries.exp F := by
  exact PowerSeries.exp_unique_of_derivative_eq_self h1 h0

theorem map_poly {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {n : ℕ} (f : LetA O n →ₐ[O] A)
    (i : ZMod n) (hf : ∀ a, a i = 0 → f a = 0) (p : ZMod n → Polynomial O) :
    f (fun j => ((p j : Polynomial O) : PowerSeries O)) = Polynomial.aeval (f letπ) (p i) := by
  have hfam : f (fun j => ((p j : Polynomial O) : PowerSeries O)) =
      f (fun _ => ((p i : Polynomial O) : PowerSeries O)) := by
    have h := hf ((fun j => ((p j : Polynomial O) : PowerSeries O)) -
      (fun _ => ((p i : Polynomial O) : PowerSeries O))) (by simp)
    rwa [map_sub, sub_eq_zero] at h
  rw [hfam]
  have hg : f.comp ((Pi.constAlgHom O (ZMod n) (PowerSeries O)).comp
      (Polynomial.coeToPowerSeries.algHom O)) = Polynomial.aeval (f letπ) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.coeToPowerSeries.algHom_apply,
      Polynomial.coe_X, Algebra.algebraMap_self, PowerSeries.map_id]
    rfl
  have h2 := congrArg (fun φ => φ (p i)) hg
  simp only [AlgHom.comp_apply, Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self,
    PowerSeries.map_id] at h2
  exact h2

theorem map_poly_series {O L : Type} [CommRing O] [CommRing L] [Algebra O L] {n : ℕ}
    (f : LetA O n →ₐ[O] PowerSeries L) (i : ZMod n) (hf : ∀ a, a i = 0 → f a = 0) (p : ZMod n → Polynomial O) :
    f (fun j => ((p j : Polynomial O) : PowerSeries O)) =
      Polynomial.aeval (f letπ) ((p i).map (algebraMap O L)) := by
  rw [map_poly f i hf p, Polynomial.aeval_map_algebraMap]

theorem lev_isExp : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ), ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a) := by
  intro l _ P K s LL Γ R i ζ hζ a
  have hπ : R.lev i ζ letπ = PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1 := by
    obtain ⟨E, hE0, hE1, hE⟩ := R.lev_π i ζ (by rw [P.PD_p K]; exact hζ)
    rw [eq_exp E hE0 hE1] at hE
    rw [← hE]
    ring
  have htr : ∀ m : ℕ, Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1)
      (PowerSeries.trunc m (toLL a i)) =
      R.lev i ζ (fun j => ((PowerSeries.trunc m (a j) : Polynomial ↥(OL LL)) : PowerSeries ↥(OL LL))) := by
    intro m
    rw [map_poly_series (R.lev i ζ) i (R.lev_letter i ζ) (fun j => PowerSeries.trunc m (a j)), hπ]
    simp only [toLL, PowerSeries.trunc_map]
  intro k
  simp only [htr]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (l : ℝ) ^ (-(r : ℝ)) < ε := by
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
    refine ⟨r, ?_⟩
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow]
    exact hr
  obtain ⟨m₀, hm₀⟩ := R.lev_cont i ζ a k r
  refine ⟨m₀, fun m hm => ?_⟩
  have hv := hm₀ m hm
  rw [← WithTop.coe_natCast] at hv
  have hn := ((NormVal.locPrime_v_normalised l P LL).2.1 _ (r : ℚ)).1 hv
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  calc _ = _ := by push_cast; rfl
    _ ≤ _ := hn
    _ = (l : ℝ) ^ (-(r : ℝ)) := by push_cast; rfl
    _ < ε := hr

end GlobalTheory.HWL.LevExp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicPowerSeriesData_lev_isExpansionAtZeta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ), ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a) := by
  first | exact @GlobalTheory.HWL.LevExp.lev_isExp | exact GlobalTheory.HWL.LevExp.lev_isExp | (intros; apply GlobalTheory.HWL.LevExp.lev_isExp <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

namespace GlobalTheory.HWL.Letter

variable {l : ℕ} [Fact l.Prime]

theorem lin_ext (K : FinExt l) {M : Type} [AddCommGroup M] [Module ℚ_[l] M] (σ τ : ↥(K0 K) →ₗ[ℚ_[l]] M)
    (h : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → σ c = τ c) (c : ↥(K0 K)) :
    σ c = τ c := by
  have h1 : ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 → σ c = τ c := by
    intro c hc
    obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c c.2 hc
    have h2 : c = ∑ i, (z i : ℚ_[l]) • (⟨ω i, (hω i).1⟩ : ↥(K0 K)) := by
      apply Subtype.ext
      rw [hsum]
      push_cast
      simp only [Algebra.smul_def]
    rw [h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨m, hm, hl, hx⟩ := (hω i).2
    rw [map_smul, map_smul, h _ m hm hl hx]
  have hl : ‖(l : Om l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖(c : Om l)‖
  rw [zero_mul] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds one_pos)).exists
  have h3 := h1 (((l : ℚ_[l]) ^ n) • c) (by
    rw [Algebra.smul_def]
    push_cast
    rwa [norm_mul, norm_pow])
  rw [map_smul, map_smul] at h3
  have h0 : ((l : ℚ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  rw [← inv_smul_smul₀ h0 (σ c), h3, inv_smul_smul₀ h0]

theorem mul_ext (K : FinExt l) {L B : Type} [Field L] [Algebra ℚ_[l] L] [CommRing B] [Algebra ℚ_[l] B]
    (e : ↥(K0 K) →ₐ[ℚ_[l]] L) (f : ↥(K0 K) →ₐ[ℚ_[l]] B) (x : L ⊗[ℚ_[l]] B)
    (h : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 →
      ((1 : L) ⊗ₜ[ℚ_[l]] f c) * x = e c • x) (c : ↥(K0 K)) : ((1 : L) ⊗ₜ[ℚ_[l]] f c) * x = e c • x :=
  lin_ext K ((LinearMap.mulRight ℚ_[l] x).comp ((TensorProduct.mk ℚ_[l] L B 1).comp f.toLinearMap))
    (((LinearMap.toSpanSingleton L _ x).restrictScalars ℚ_[l]).comp e.toLinearMap) h c

theorem const_mul_letE {O : Type} [CommRing O] {n : ℕ} (o : ZMod n → O) (i : ZMod n) :
    (fun j => PowerSeries.C (o j) : LetA O n) * letE i = algebraMap O (LetA O n) (o i) * letE i := by
  funext j
  by_cases hj : j = i
  · subst hj; rfl
  · simp [letE, hj]

theorem step {O R Q L B : Type} [CommRing O] [CommRing R] [Algebra O R] [Field Q] [Field L] [Algebra Q L]
    [CommRing B] [Algebra Q B] {n : ℕ} (io : LetA O n →ₐ[O] R) (β : R →+* L ⊗[Q] B) (o : ZMod n → O)
    (i : ZMod n) (a : L) (b : B) (h3 : β (io (fun j => PowerSeries.C (o j))) = (1 : L) ⊗ₜ[Q] b)
    (h5 : β (algebraMap O R (o i)) = a ⊗ₜ[Q] (1 : B)) :
    ((1 : L) ⊗ₜ[Q] b) * β (io (letE i)) = a • β (io (letE i)) := by
  rw [← h3, ← map_mul, ← map_mul, const_mul_letE, map_mul, AlgHom.commutes, map_mul, h5, Algebra.smul_def]
  rfl

theorem letter : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (c : ↥(K0 K)), ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.B c) * β (I.io (letE i)) = Γ.emb i c • β (I.io (letE i)) := by
  intro l _ P AI _ K s LL _ Γ R I hI β hβ i c
  refine mul_ext K (Γ.emb i) (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B) _ (fun c m hm hl hc => ?_) c
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hc
  have hc' : c ^ m = 1 := by exact_mod_cast hc
  obtain ⟨o, ho⟩ := GlobalTheory.UnramIdem.exists_vec Γ.emb hm hc'
  have h1 := hI c m hm hl hc xb hxb o ho
  have h2 : AI.ιA (WittVector.teichmuller l xb) = algebraMap ↥(K0 K) P.R.B c :=
    AI.ιA_teich ⟨c, c.2.2⟩ m hm hl hc xb hxb
  have h3 := hβ 1 (WittVector.teichmuller l xb)
  have h5 := hβ (o i) 1
  rw [map_one, ho] at h5
  rw [h2] at h3
  exact step I.io β o i _ _ ((congrArg β h1).trans h3) h5

end GlobalTheory.HWL.Letter
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxUnramified_acts_on_letterIdempotent_image : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (c : ↥(K0 K)), ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.B c) * β (I.io (letE i)) = Γ.emb i c • β (I.io (letE i)) := by
  first | exact @GlobalTheory.HWL.Letter.letter | exact GlobalTheory.HWL.Letter.letter | (intros; apply GlobalTheory.HWL.Letter.letter <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.HWL.Cmp.PerMap

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

section Val

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {B : Type} [CommRing B] [Algebra Qp B]
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    (β : RA →+* LL ⊗[Qp] B) (hβ : ∀ (o : O) (r : RA), β (o • r) = algebraMap O LL o • β r)

def βB (T : LocLat G Qp LL O) : TW RA T →+ T.V ⊗[Qp] B :=
  TensorProduct.liftAddHom
    { toFun := fun r =>
        { toFun := fun t => actS T.V B (β r) ((t : T.V) ⊗ₜ[Qp] (1 : B))
          map_zero' := by simp
          map_add' := fun a b => by simp [add_tmul] }
      map_zero' := by ext t; simp
      map_add' := fun a b => by ext t; simp }
    (fun o r t => by
      change actS T.V B (β (o • r)) ((t : T.V) ⊗ₜ[Qp] (1 : B)) =
        actS T.V B (β r) ((o • (t : T.V)) ⊗ₜ[Qp] (1 : B))
      rw [hβ, map_smul, LinearMap.smul_apply, ← map_smul, smul_tmul', algebraMap_smul])

theorem βB_tmul (T : LocLat G Qp LL O) (r : RA) (t : ↥T.L.T) :
    βB β hβ T (r ⊗ₜ[O] t) = actS T.V B (β r) ((t : T.V) ⊗ₜ[Qp] (1 : B)) := rfl

theorem βB_smul (T : LocLat G Qp LL O) (r : RA) (y : TW RA T) :
    βB β hβ T (r • y) = actS T.V B (β r) (βB β hβ T y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul a t => rw [smul_tmul', βB_tmul, βB_tmul, smul_eq_mul, map_mul, map_mul, Module.End.mul_apply]

theorem map_smul_semi {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (σ : RA →ₐ[O] RW) (f : M →ₗ[O] N) (r : RA) (y : RA ⊗[O] M) :
    TensorProduct.map σ.toLinearMap f (r • y) = σ r • TensorProduct.map σ.toLinearMap f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul a t => simp [smul_tmul']

variable (inclR : RA →ₐ[O] RW)

theorem incl_smul (T : LocLat G Qp LL O) (r : RA) (y : TW RA T) :
    TWincl inclR T (r • y) = inclR r • TWincl inclR T y := map_smul_semi _ _ _ _

theorem incl_inj (hinj : Function.Injective inclR) (T : LocLat G Qp LL O) :
    Function.Injective (TWincl inclR T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) inclR.toLinearMap hinj

def Val (T : LocLat G Qp LL O) (j : TW RW T) (z : T.V ⊗[Qp] B) : Prop :=
  ∃ (r : RA) (y : TW RA T), IsUnit (β r) ∧ TWincl inclR T y = inclR r • j ∧
    βB β hβ T y = actS T.V B (β r) z

variable {β hβ inclR}

theorem act_inj (T : LocLat G Qp LL O) {u : LL ⊗[Qp] B} (hu : IsUnit u) {z z' : T.V ⊗[Qp] B}
    (h : actS T.V B u z = actS T.V B u z') : z = z' :=
  ((Module.End.isUnit_iff _).mp (hu.map (actS T.V B))).1 h

theorem act_comm (T : LocLat G Qp LL O) (u u' : LL ⊗[Qp] B) (z : T.V ⊗[Qp] B) :
    actS T.V B u (actS T.V B u' z) = actS T.V B u' (actS T.V B u z) := by
  rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

theorem Val.exists {T : LocLat G Qp LL O} {j : TW RW T} {r : RA} {y : TW RA T} (hr : IsUnit (β r))
    (hy : TWincl inclR T y = inclR r • j) : ∃ z, Val β hβ inclR T j z := by
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp (hr.map (actS T.V B))).2 (βB β hβ T y)
  exact ⟨z, r, y, hr, hy, hz.symm⟩

theorem Val.spec (hinj : Function.Injective inclR) {T : LocLat G Qp LL O} {j : TW RW T} {z : T.V ⊗[Qp] B}
    (h : Val β hβ inclR T j z) {r : RA} {y : TW RA T} (hy : TWincl inclR T y = inclR r • j) :
    βB β hβ T y = actS T.V B (β r) z := by
  obtain ⟨r₀, y₀, hu, h1, h2⟩ := h
  have h3 : r₀ • y = r • y₀ := incl_inj inclR hinj T (by
    rw [incl_smul, incl_smul, hy, h1, smul_comm])
  apply act_inj T hu
  rw [← βB_smul, h3, βB_smul, h2, act_comm]

theorem Val.unique (hinj : Function.Injective inclR) {T : LocLat G Qp LL O} {j : TW RW T} {z z' : T.V ⊗[Qp] B}
    (h : Val β hβ inclR T j z) (h' : Val β hβ inclR T j z') : z = z' := by
  obtain ⟨r₀, y₀, hu, h1, h2⟩ := h'
  apply act_inj T hu
  rw [← h.spec hinj h1, h2]

theorem Val.add {T : LocLat G Qp LL O} {j j' : TW RW T} {z z' : T.V ⊗[Qp] B}
    (h : Val β hβ inclR T j z) (h' : Val β hβ inclR T j' z') : Val β hβ inclR T (j + j') (z + z') := by
  obtain ⟨r, y, hu, h1, h2⟩ := h
  obtain ⟨r', y', hu', h1', h2'⟩ := h'
  refine ⟨r * r', r' • y + r • y', by rw [map_mul]; exact hu.mul hu', ?_, ?_⟩
  · rw [map_add, incl_smul, incl_smul, h1, h1', smul_smul, smul_smul, map_mul, smul_add, mul_comm (inclR r')]
  · rw [map_add, βB_smul, βB_smul, h2, h2', act_comm, map_mul, map_mul, map_add]
    rfl

theorem Val.smul {T : LocLat G Qp LL O} {j : TW RW T} {z : T.V ⊗[Qp] B}
    (h : Val β hβ inclR T j z) (a : RA) : Val β hβ inclR T (inclR a • j) (actS T.V B (β a) z) := by
  obtain ⟨r, y, hu, h1, h2⟩ := h
  refine ⟨r, a • y, hu, ?_, ?_⟩
  · rw [incl_smul, h1, smul_comm]
  · rw [βB_smul, h2, act_comm]

theorem Val.map {T T' : LocLat G Qp LL O} (f : T.V →ₗ[LL] T'.V) (fT : ↥T.L.T →ₗ[O] ↥T'.L.T)
    (hf : ∀ t, (fT t : T'.V) = f t) (σA : RA →ₐ[O] RA) (σW : RW →ₐ[O] RW) (hB : B →ₐ[Qp] B)
    (h1 : ∀ r, inclR (σA r) = σW (inclR r))
    (h2 : ∀ r, β (σA r) = Algebra.TensorProduct.map (AlgHom.id Qp LL) hB (β r))
    {j : TW RW T} {z : T.V ⊗[Qp] B} (h : Val β hβ inclR T j z) :
    Val β hβ inclR T' (TensorProduct.map σW.toLinearMap fT j) (AlgebraTensorModule.map f hB.toLinearMap z) := by
  obtain ⟨r, y, hu, h3, h4⟩ := h
  have e1 : ∀ y : TW RA T, TWincl inclR T' (TensorProduct.map σA.toLinearMap fT y) =
      TensorProduct.map σW.toLinearMap fT (TWincl inclR T y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a t => simp [TWincl, h1]
  have e2 : ∀ y : TW RA T, βB β hβ T' (TensorProduct.map σA.toLinearMap fT y) =
      AlgebraTensorModule.map f hB.toLinearMap (βB β hβ T y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a t =>
      rw [TensorProduct.map_tmul, βB_tmul, βB_tmul, map_actS, ← h2, hf]
      simp
  refine ⟨σA r, TensorProduct.map σA.toLinearMap fT y, by rw [h2]; exact hu.map _, ?_, ?_⟩
  · rw [e1, h3, map_smul_semi, h1]
  · rw [e2, h4, map_actS, h2]

end Val

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s}
    {R : WSer Γ} {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n}

theorem exists_isPer (Mo : WN E zl) (β : O ⊗[Zl] Ai →+* LL ⊗[Qp] B) (ιA : Ai →+* B) (ιdR : Ai →+* BdR) (p1 : Ai)
    (hβ₀ : ∀ (o : O) (w : Ai), β (o ⊗ₜ[Zl] w) = algebraMap O LL o ⊗ₜ[Qp] ιA w)
    (hdR : ∀ w, ιdR w = PD.ι (ιA w)) (hinj : Function.Injective inclR) (hu : IsUnit (ιA p1))
    (gA : G → (O ⊗[Zl] Ai →ₐ[O] O ⊗[Zl] Ai)) (hg1 : ∀ g r, inclR (gA g r) = gR g (inclR r))
    (hg2 : ∀ g r, β (gA g r) =
      Algebra.TensorProduct.map (AlgHom.id Qp LL) ((PD.actB g).toAlgHom.restrictScalars Qp) (β r))
    (φA : O ⊗[Zl] Ai →ₐ[O] O ⊗[Zl] Ai) (hφ1 : ∀ r, inclR (φA r) = φR (inclR r))
    (hφ2 : ∀ r, β (φA r) = Algebra.TensorProduct.map (AlgHom.id Qp LL) PD.φ (β r))
    (hS : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∃ m : ℕ, Sand Mo T ((1 : O) ⊗ₜ[Zl] (p1 ^ m))) :
    ∃ βdR bT, IsPer Mo (β.comp I.io.toRingHom) ιdR p1 βdR bT := by
  classical
  have hβ : ∀ (o : O) (r : O ⊗[Zl] Ai), β (o • r) = algebraMap O LL o • β r := by
    intro o r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [smul_add, map_add, ha, hb]
    | tmul a w => rw [smul_tmul', hβ₀, hβ₀, smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  have hex : ∀ T : LocLat G Qp LL O, ∀ x : ↥(Mo.N T), ∃ z, IsCrys PD T.ρ → Val β hβ inclR T (E.jD T x) z := by
    intro T x
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨m, hm, -⟩ := hS T hT
      obtain ⟨y, hy⟩ := hm x x.2
      have hun : IsUnit (β ((1 : O) ⊗ₜ[Zl] (p1 ^ m))) := by
        rw [hβ₀, map_one, map_pow]
        exact (hu.pow m).map (Algebra.TensorProduct.includeRight : B →ₐ[Qp] LL ⊗[Qp] B)
      obtain ⟨z, hz⟩ := Val.exists (hβ := hβ) hun hy
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hT⟩
  choose b hb using hex
  let bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B := fun T =>
    if hT : IsCrys PD T.ρ then
      AddMonoidHom.mk' (b T) (fun x y => (hb T (x + y) hT).unique hinj (by
        rw [Submodule.coe_add, map_add]
        exact (hb T x hT).add (hb T y hT)))
    else 0
  have hv : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ x : ↥(Mo.N T), Val β hβ inclR T (E.jD T x) (bT T x) := by
    intro T hT x
    simp only [bT, dif_pos hT]
    exact hb T x hT
  have hj : ∀ (T : LocLat G Qp LL O) (a : LetA O n) (x : E.DD T), E.jD T (a • x) = inclR (I.io a) • E.jD T x := by
    intro T a x
    rw [← algebraMap_smul R.EE a x, E.jD_smul, I.ioE_ext]
  refine ⟨fun T => (ιV PD (LL := LL) (V := T.V)).toAddMonoidHom.comp (βB β hβ T), bT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T a w t
    change ιV PD (LL := LL) (V := T.V) (βB β hβ T _) = _
    rw [βB_tmul, hβ₀, actS_tmul, hdR, mul_one, algebraMap_smul]
    rfl
  · intro T hT a x
    refine (hv T hT (a • x)).unique hinj ?_
    rw [Submodule.coe_smul, hj]
    exact (hv T hT x).smul _
  · intro T hT g x
    refine (hv T hT _).unique hinj ?_
    change Val β hβ inclR T (E.jD T (E.γD T (Γ.resΓ g) x)) _
    rw [E.jD_act]
    exact Val.map (T.ρ g) (T.actT g) (fun _ => rfl) (gA g) (gR g) _ (hg1 g) (hg2 g) (hv T hT x)
  · intro T hT x m hx
    refine (hv T hT _).unique hinj ?_
    change Val β hβ inclR T (E.jD T (R.Q ^ m • E.φD T x)) _
    rw [hj, E.jD_φ]
    exact (Val.map LinearMap.id LinearMap.id (fun _ => rfl) φA φR _ hφ1 hφ2 (hv T hT x)).smul _
  · intro T T' f hT hT' x hx
    refine (hv T' hT' _).unique hinj ?_
    change Val β hβ inclR T' (E.jD T' (E.map f x)) _
    rw [E.jD_map]
    exact Val.map (inclR := inclR) f.f _ (fun _ => rfl) (AlgHom.id O _) (AlgHom.id O _) (AlgHom.id Qp B) (fun _ => rfl)
      (fun r => by simp) (hv T hT x)
  · intro T hT x k y hy
    rw [← map_pow] at hy
    change ιV PD (LL := LL) (V := T.V) (βB β hβ T _) = _
    rw [(hv T hT x).spec hinj hy, Algebra.TensorProduct.tmul_pow, one_pow, hβ₀, map_one]
    refine (map_actS (LinearMap.id : T.V →ₗ[LL] T.V) (PD.ι.restrictScalars Qp) _ _).trans ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, actS_one_tmul, ← map_pow, hdR]
    rfl

omit [TopologicalSpace LL] in
theorem beta_map (β : O ⊗[Zl] Ai →+* LL ⊗[Qp] B) (ιA : Ai →+* B)
    (hβ₀ : ∀ (o : O) (w : Ai), β (o ⊗ₜ[Zl] w) = algebraMap O LL o ⊗ₜ[Qp] ιA w)
    (a : Ai →ₐ[Zl] Ai) (h : B →ₐ[Qp] B) (hc : ∀ w, ιA (a w) = h (ιA w)) (r : O ⊗[Zl] Ai) :
    β (Algebra.TensorProduct.map (AlgHom.id O O) a r) = Algebra.TensorProduct.map (AlgHom.id Qp LL) h (β r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul o w => simp [hβ₀, hc]

theorem map_map_comm {Wc : Type} [CommRing Wc] [Algebra Zl Wc] (i : Ai →ₐ[Zl] Wc)
    (a : Ai →ₐ[Zl] Ai) (b : Wc →ₐ[Zl] Wc) (hc : ∀ w, i (a w) = b (i w)) (r : O ⊗[Zl] Ai) :
    Algebra.TensorProduct.map (AlgHom.id O O) i (Algebra.TensorProduct.map (AlgHom.id O O) a r) =
      Algebra.TensorProduct.map (AlgHom.id O O) b (Algebra.TensorProduct.map (AlgHom.id O O) i r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul o w => simp [hc]

end Generic

variable {l : ℕ} [Fact l.Prime]

def frobA (l : ℕ) [Fact l.Prime] : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (frobenius (OCb l) l)
  commutes' := fun x => map_zlW l _ x

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (E : WEt I) (Mo : NS E), (∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ → ∃ m : ℕ, Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL)) → ∃ βdR bT, IsPer Mo (β.comp I.io.toRingHom) (P.ιB.toRingHom.comp AI.ιA) AI.π₁ βdR bT := by
  intro l _ P AI hT K s LL _ Γ R I _ β hβ E Mo hS
  refine exists_isPer Mo β AI.ιA _ AI.π₁ hβ (fun w => (P.PD_ι K _).symm) (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1
    ((GlobalTheory.TiedMu.tied_mu_units l P AI hT).1 1)
    (fun g => Algebra.TensorProduct.map (AlgHom.id _ _) (AI.actWHom (g : GQ l)).toAlgHom) (fun g r => ?_)
    (fun g r => ?_) (Algebra.TensorProduct.map (AlgHom.id _ _) (frobA l)) (fun r => ?_) (fun r => ?_) hS
  · refine map_map_comm (inclWA l) _ _ (fun w => ?_) r
    ext k
    exact (autCb_alg l (AI.actT (g : GQ l)) (w.coeff k)).symm
  · exact beta_map β AI.ιA hβ _ _ (fun w => (AI.ιA_act g w).trans (P.PD_actB K g _).symm) r
  · refine map_map_comm (inclWA l) _ _ (fun w => ?_) r
    ext k
    exact map_pow (algebraMap (OCb l) (Cb l)) (w.coeff k) l
  · refine beta_map β AI.ιA hβ _ _ (fun w => ?_) r
    refine Eq.trans ?_ ((AI.ιA_φ w).trans (P.PD_φ K _).symm)
    rw [WittVector.frobenius_eq_map_frobenius]
    rfl

end GlobalTheory.HWL.Cmp.PerMap
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachModule_periodMap_to_bcris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (E : WEt I) (Mo : NS E), (∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ → ∃ m : ℕ, Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL)) → ∃ βdR bT, IsPer Mo (β.comp I.io.toRingHom) (P.ιB.toRingHom.comp AI.ιA) AI.π₁ βdR bT := by
  first | exact @GlobalTheory.HWL.Cmp.PerMap.main | exact GlobalTheory.HWL.Cmp.PerMap.main | (intros; apply GlobalTheory.HWL.Cmp.PerMap.main <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

noncomputable section

namespace GlobalTheory.HWL.Mat

section Abstract

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {N : Submodule A M} {r : ℕ}

theorem coeff_ext (nb : Module.Basis (Fin r) A ↥N) {a b : Fin r → A}
    (h : ∑ i, a i • (nb i : M) = ∑ i, b i • (nb i : M)) (i : Fin r) : a i = b i := by
  have hli : LinearIndependent A (fun i => (nb i : M)) :=
    nb.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  exact Fintype.linearIndependent_iffₛ.1 hli a b h i

theorem eq_sum (nb : Module.Basis (Fin r) A ↥N) {x : M} (hx : x ∈ N) :
    x = ∑ i, nb.repr ⟨x, hx⟩ i • (nb i : M) := by
  have h := congrArg N.subtype (nb.sum_repr ⟨x, hx⟩)
  rw [map_sum] at h
  simpa using h.symm

theorem semi_sum {f : M →+ M} {σ : A → A} (hf : ∀ a x, f (a • x) = σ a • f x) (a : Fin r → A)
    (x : Fin r → M) : f (∑ i, a i • x i) = ∑ i, σ (a i) • f (x i) := by
  rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hf _ _

theorem sum_sum (P C : Matrix (Fin r) (Fin r) A) (e : Fin r → M) (j : Fin r) :
    ∑ k, C k j • ∑ i, P i k • e i = ∑ i, (P * C) i j • e i := by
  simp only [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem common_exp (S : Submodule A M) (Q : A) (x : Fin r → M) (h : ∀ j, ∃ k : ℕ, Q ^ k • x j ∈ S) :
    ∃ m : ℕ, ∀ j, Q ^ m • x j ∈ S := by
  choose k hk using h
  refine ⟨∑ j, k j, fun j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  rw [hc, add_comm, pow_add, mul_smul]
  exact S.smul_mem _ (hk j)

theorem exists_matrices {Γ : Type} [Mul Γ] (nb : Module.Basis (Fin r) A ↥N) (Q π : A)
    (φ : M →+ M) (σ : A → A) (hφ : ∀ a x, φ (a • x) = σ a • φ x)
    (γ : Γ → M →+ M) (τ : Γ → A →+* A) (hγ : ∀ g a x, γ g (a • x) = τ g a • γ g x)
    (hmul : ∀ g h x, γ (g * h) x = γ g (γ h x)) (hcomm : ∀ g x, φ (γ g x) = γ g (φ x))
    (hNφ : ∀ x ∈ N, ∃ k : ℕ, Q ^ k • φ x ∈ N)
    (hNinv : ∀ y ∈ N, ∃ k : ℕ, Q ^ k • y ∈ Submodule.span A (φ '' (N : Set M)))
    (hNΓ : ∀ g, ∀ x ∈ N, γ g x ∈ N) (hNπ : ∀ g, ∀ x ∈ N, ∃ y ∈ N, γ g x - x = π • y) :
    ∃ (m m' : ℕ) (Gm : Γ → Matrix (Fin r) (Fin r) A) (Pm Pm' : Matrix (Fin r) (Fin r) A),
      (∀ g h, Gm (g * h) = Gm g * (Gm h).map (τ g)) ∧
      (∀ g i j, ∃ c, Gm g i j = (if i = j then 1 else 0) + π * c) ∧
      Pm * Pm' = (Q ^ m') • (1 : Matrix (Fin r) (Fin r) A) ∧
      (∀ g, (τ g Q ^ m) • (Pm * (Gm g).map σ) = (Q ^ m) • (Gm g * Pm.map (τ g))) ∧
      (∀ g j, γ g (nb j : M) = ∑ i, Gm g i j • (nb i : M)) ∧
      ∀ j, Q ^ m • φ (nb j : M) = ∑ i, Pm i j • (nb i : M) := by
  classical
  obtain ⟨m, hm⟩ := common_exp N Q (fun j => φ (nb j : M)) fun j => hNφ _ (nb j).2
  obtain ⟨k, hk⟩ := common_exp _ Q (fun j => (nb j : M)) fun j => hNinv _ (nb j).2
  have hspan : Submodule.span A (φ '' (N : Set M)) ≤
      Submodule.span A (Set.range fun i => φ (nb i : M)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [eq_sum nb hx, semi_sum hφ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun A).1 (hspan (hk j))
  obtain ⟨Gm, hG⟩ : ∃ Gm : Γ → Matrix (Fin r) (Fin r) A,
      ∀ g j, γ g (nb j : M) = ∑ i, Gm g i j • (nb i : M) :=
    ⟨fun g i j => nb.repr ⟨_, hNΓ g _ (nb j).2⟩ i, fun g j => eq_sum nb _⟩
  obtain ⟨Pm, hP⟩ : ∃ Pm : Matrix (Fin r) (Fin r) A,
      ∀ j, Q ^ m • φ (nb j : M) = ∑ i, Pm i j • (nb i : M) :=
    ⟨fun i j => nb.repr ⟨_, hm j⟩ i, fun j => eq_sum nb _⟩
  have hone : ∀ (a : A) (j : Fin r),
      ∑ i, (a * if i = j then 1 else 0) • (nb i : M) = a • (nb j : M) := by
    intro a j
    rw [Finset.sum_eq_single j] <;> simp +contextual
  refine ⟨m, m + k, Gm, Pm, Matrix.of fun i j => c j i, ?_, ?_, ?_, ?_, hG, hP⟩
  · intro g h
    ext i j
    refine coeff_ext nb (a := fun i => Gm (g * h) i j)
      (b := fun i => (Gm g * (Gm h).map (τ g)) i j) ?_ i
    rw [← hG, hmul, hG h, semi_sum (hγ g), ← sum_sum]
    simp only [hG, Matrix.map_apply]
  · intro g i j
    obtain ⟨y, hy, e⟩ := hNπ g _ (nb j).2
    refine ⟨nb.repr ⟨y, hy⟩ i, ?_⟩
    refine coeff_ext nb (a := fun i => Gm g i j)
      (b := fun i => (if i = j then 1 else 0) + π * nb.repr ⟨y, hy⟩ i) ?_ i
    have h1 := hone 1 j
    simp only [one_mul, one_smul] at h1
    simp only [add_smul, Finset.sum_add_distrib, mul_smul]
    rw [← hG, h1, ← Finset.smul_sum, ← eq_sum nb hy, ← e]
    abel
  · ext i j
    refine coeff_ext nb (a := fun i => (Pm * Matrix.of fun i j => c j i) i j)
      (b := fun i => ((Q ^ (m + k)) • (1 : Matrix (Fin r) (Fin r) A)) i j) ?_ i
    rw [← sum_sum]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hone, ← hP, Matrix.of_apply]
    rw [pow_add, mul_smul, ← hc j, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _
  · intro g
    ext i j
    refine coeff_ext nb (a := fun i => ((τ g Q ^ m) • (Pm * (Gm g).map σ)) i j)
      (b := fun i => ((Q ^ m) • (Gm g * Pm.map (τ g))) i j) ?_ i
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← sum_sum, ← sum_sum]
    have h1 : ∑ k, (Gm g).map σ k j • ∑ i, Pm i k • (nb i : M) = Q ^ m • γ g (φ (nb j : M)) := by
      rw [← hcomm, hG, semi_sum hφ, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [← hP, smul_comm, Matrix.map_apply]
    have h2 : ∑ k, Pm.map (τ g) k j • ∑ i, Gm g i k • (nb i : M) =
        τ g Q ^ m • γ g (φ (nb j : M)) := by
      rw [← map_pow, ← hγ, hP, semi_sum (hγ g)]
      exact Finset.sum_congr rfl fun l _ => by rw [← hG, Matrix.map_apply]
    rw [h1, h2, smul_comm]

end Abstract

theorem wach_matrices : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ} {Γ : WGam PD LL O v n s} {R : WSer Γ} {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n} (Mo : WN E zl) (T : LocLat G Qp LL O) (r : ℕ) (nb : Module.Basis (Fin r) (LetA O n) ↥(Mo.N T)), ∃ (m m' : ℕ) (Gm : Γ.Gam → Matrix (Fin r) (Fin r) (LetA O n)) (Pm Pm' : Matrix (Fin r) (Fin r) (LetA O n)), (∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (R.γ₀ g))) ∧ (∀ g i j k, PowerSeries.constantCoeff (Gm g i j k) = if i = j then 1 else 0) ∧ Pm * Pm' = (R.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (LetA O n)) ∧ (∀ g, (letγ (R.γ₀ g) R.Q ^ m) • (Pm * (Gm g).map (letφ R.φ₀)) = (R.Q ^ m) • (Gm g * Pm.map (letγ (R.γ₀ g)))) ∧ (∀ g j, E.γD T g (nb j : E.DD T) = ∑ i, Gm g i j • (nb i : E.DD T)) ∧ ∀ j, R.Q ^ m • E.φD T (nb j : E.DD T) = ∑ i, Pm i j • (nb i : E.DD T) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n s Γ R Zl Ai _ _ _ _
    RW _ _ inclR φR gR πA I E zl Mo T r nb
  have hφ : ∀ (a : LetA O n) (x : E.DD T), E.φD T (a • x) = letφ R.φ₀ a • E.φD T x := by
    intro a x
    rw [← algebraMap_smul R.EE a x, E.φD_smul, R.φE_ext, algebraMap_smul]
  have hγ : ∀ g (a : LetA O n) (x : E.DD T),
      E.γD T g (a • x) = letγ (R.γ₀ g) a • E.γD T g x := by
    intro g a x
    rw [← algebraMap_smul R.EE a x, E.γD_smul, R.γE_ext, algebraMap_smul]
  obtain ⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩ :=
    exists_matrices nb R.Q letπ (E.φD T).toAddMonoidHom (letφ R.φ₀) hφ
      (fun g => (E.γD T g).toAddMonoidHom) (fun g => (letγ (n := n) (R.γ₀ g)).toRingHom) hγ
      (E.γD_mul T) (E.φγ_comm T) (Mo.N_φ T) (Mo.N_φinv T) (Mo.N_Γ T) (Mo.N_π T)
  refine ⟨m, m', Gm, Pm, Pm', h1, ?_, h3, h4, h5, h6⟩
  intro g i j k
  obtain ⟨c, hc⟩ := h2 g i j
  rw [hc]
  split_ifs <;> simp [letπ]

end GlobalTheory.HWL.Mat
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachLattice_matrices_gamma_phi : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ} {Γ : WGam PD LL O v n s} {R : WSer Γ} {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n} (Mo : WN E zl) (T : LocLat G Qp LL O) (r : ℕ) (nb : Module.Basis (Fin r) (LetA O n) ↥(Mo.N T)), ∃ (m m' : ℕ) (Gm : Γ.Gam → Matrix (Fin r) (Fin r) (LetA O n)) (Pm Pm' : Matrix (Fin r) (Fin r) (LetA O n)), (∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (R.γ₀ g))) ∧ (∀ g i j k, PowerSeries.constantCoeff (Gm g i j k) = if i = j then 1 else 0) ∧ Pm * Pm' = (R.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (LetA O n)) ∧ (∀ g, (letγ (R.γ₀ g) R.Q ^ m) • (Pm * (Gm g).map (letφ R.φ₀)) = (R.Q ^ m) • (Gm g * Pm.map (letγ (R.γ₀ g)))) ∧ (∀ g j, E.γD T g (nb j : E.DD T) = ∑ i, Gm g i j • (nb i : E.DD T)) ∧ ∀ j, R.Q ^ m • E.φD T (nb j : E.DD T) = ∑ i, Pm i j • (nb i : E.DD T) := by
  first | exact @GlobalTheory.HWL.Mat.wach_matrices | exact GlobalTheory.HWL.Mat.wach_matrices | (intros; apply GlobalTheory.HWL.Mat.wach_matrices <;> assumption)
end

section
namespace GlobalTheory

open PowerSeries in

theorem powerSeries_eq_C_of_subst_eq_self (L : Type) [Field L] (y : PowerSeries L)
    (hy : PowerSeries.constantCoeff y = 0)
    (hu : ∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) (a : PowerSeries L)
    (ha : (PowerSeries.subst y a : PowerSeries L) = a) :
    a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  classical
  obtain ⟨z, rfl⟩ : X ∣ y := by rwa [PowerSeries.X_dvd_iff]
  have hs : HasSubst (X * z) := HasSubst.of_constantCoeff_zero' hy
  have hu1 : coeff 1 (X * z) = constantCoeff z := by
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [hu1] at hu

  have hc : ∀ n, coeff n (a.subst (X * z)) =
      ∑ d ∈ Finset.range (n + 1), coeff d a * coeff (n - d) (z ^ d) := by
    intro n
    rw [coeff_subst' hs, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [mul_pow, coeff_X_pow_mul', if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)),
        smul_eq_mul]
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

  have main : ∀ k, 0 < k → coeff k a = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have h1 := hc k
      rw [ha, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self,
        coeff_zero_eq_constantCoeff_apply, map_pow] at h1
      · have h2 : coeff k a * (1 - constantCoeff z ^ k) = 0 := by
          rw [mul_sub, mul_one, ← h1, sub_self]
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h).symm (hu k hk)
      · intro d hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp [coeff_one, hk.ne']
        · rw [ih d (Finset.mem_range.mp hd) hd0, zero_mul]
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_C, if_neg (Nat.succ_ne_zero n)]
    exact main (n + 1) (Nat.succ_pos n)

end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_eq_C_of_subst_fixed_not_root_of_unity : ∀ (L : Type) [Field L] (y : PowerSeries L), PowerSeries.constantCoeff y = 0 → (∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) → ∀ a : PowerSeries L, (PowerSeries.subst y a : PowerSeries L) = a → a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  atlas_forward_decl GlobalTheory.powerSeries_eq_C_of_subst_eq_self
end

section
section
noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

section Filt

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

end Filt

open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] in
private theorem tmul_mem_filV_of_mem_fil (n : ℤ) (v : V) {y : BdR} (hy : y ∈ PD.Fil n) :
    v ⊗ₜ[Qp] y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) n := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV
  exact ⟨v ⊗ₜ[Qp] (⟨y, hy⟩ : (PD.Fil n).restrictScalars Qp), by simp⟩

open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
private theorem fil_antitone' {a b : ℤ} (h : b ≤ a) : PD.Fil a ≤ PD.Fil b := by
  induction a, h using Int.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (PD.Fil_anti n).trans ih

open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] in
private theorem filV_antitone' {a b : ℤ} (h : b ≤ a) :
    _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a ≤ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) b := by
  intro x hx
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV at hx
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simpa using tmul_mem_filV_of_mem_fil PD b v (fil_antitone' PD h y.2)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] in
private theorem exists_mem_filV' (x : V ⊗[Qp] BdR) : ∃ n, x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) n := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v y =>
    obtain ⟨n, hn⟩ := PD.Fil_exh y
    exact ⟨n, tmul_mem_filV_of_mem_fil PD n v hn⟩
  | add x y hx hy =>
    obtain ⟨n₁, h₁⟩ := hx
    obtain ⟨n₂, h₂⟩ := hy
    exact ⟨min n₁ n₂, add_mem (filV_antitone' PD (min_le_left _ _) h₁)
      (filV_antitone' PD (min_le_right _ _) h₂)⟩

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_tmul' (β : BdR) (v : T.V) (y : BdR) :
    _root_.Formalism.BasicNotions.mulVR T β (v ⊗ₜ[Qp] y) = v ⊗ₜ[Qp] (β * y) := by
  simp [_root_.Formalism.BasicNotions.mulVR]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_mulVR' (β γ : BdR) (x : T.V ⊗[Qp] BdR) :
    _root_.Formalism.BasicNotions.mulVR T β (_root_.Formalism.BasicNotions.mulVR T γ x) = _root_.Formalism.BasicNotions.mulVR T (β * γ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp only [mulVR_tmul', mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_mem_compKer (ι : LL →ₐ[Qp] BdR) (β : BdR) {x : T.V ⊗[Qp] BdR}
    (hx : x ∈ _root_.Formalism.BasicNotions.compKer T ι) : _root_.Formalism.BasicNotions.mulVR T β x ∈ _root_.Formalism.BasicNotions.compKer T ι := by
  unfold _root_.Formalism.BasicNotions.compKer at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, y, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨c, _root_.Formalism.BasicNotions.mulVR T β y, ?_⟩
    rw [map_sub, LinearMap.map_smul, mulVR_mulVR', mulVR_mulVR', mul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ c hx

open TensorProduct in
private theorem mulRight_mem_filV_lemma_4 {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type}
    [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K]
    [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B]
    [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {p n : ℤ} {β : BdR}
    (hβ : β ∈ PD.Fil p) {x : T.V ⊗[Qp] BdR} (hx : x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) n) :
    _root_.Formalism.BasicNotions.mulVR T β x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (p + n) := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV at hx
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v y =>
    simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype,
      mulVR_tmul']
    exact tmul_mem_filV_of_mem_fil PD _ v (PD.Fil_mul _ _ _ _ hβ y.2)
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_add' (β γ : BdR) (x : T.V ⊗[Qp] BdR) :
    _root_.Formalism.BasicNotions.mulVR T (β + γ) x = _root_.Formalism.BasicNotions.mulVR T β x + _root_.Formalism.BasicNotions.mulVR T γ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp only [mulVR_tmul', add_mul, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_zero' (x : T.V ⊗[Qp] BdR) : _root_.Formalism.BasicNotions.mulVR T 0 x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp only [mulVR_tmul', zero_mul, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_sum {ι : Type} (s : Finset ι) (f : ι → BdR) (x : T.V ⊗[Qp] BdR) :
    _root_.Formalism.BasicNotions.mulVR T (∑ i ∈ s, f i) x = ∑ i ∈ s, _root_.Formalism.BasicNotions.mulVR T (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mulVR_zero']
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, mulVR_add', ih]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem smul_sub_mulVR_mem_compKer (ι : LL →ₐ[Qp] BdR) (c : LL) (x : T.V ⊗[Qp] BdR) :
    c • x - _root_.Formalism.BasicNotions.mulVR T (ι c) x ∈ _root_.Formalism.BasicNotions.compKer T ι := by
  unfold _root_.Formalism.BasicNotions.compKer
  exact Submodule.subset_span ⟨c, x, rfl⟩

open TensorProduct in

theorem _root_.GlobalTheory.HWL.Cmp.filt_expansion_component : ∀ {G : Type} [Group G]
    [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀]
    [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B]
    [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR]
    [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR]
    [IsScalarTower Qp K₀ BdR] (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) (tS pk : BdR), IsUnit tS → tS ∈ PD.Fil 1 →
    ∀ (r w : ℕ) (z : T.V ⊗[Qp] BdR) (D : Fin r → T.V ⊗[Qp] BdR) (b : Fin r → BdR)
    (e : Fin r → PowerSeries LL) (L : ℤ → T.V ⊗[Qp] BdR),
    _root_.Formalism.BasicNotions.mulVR T (tS ^ w) z - ∑ j, _root_.Formalism.BasicNotions.mulVR T (b j) (D j) ∈ _root_.Formalism.BasicNotions.compKer T ι →
    (∀ (j : Fin r) (m : ℕ), b j - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (e j)) * tS ^ k ∈
      PD.Fil (m : ℤ)) →
    (∀ k : ℤ, L k - ∑ j, _root_.GlobalTheory.HWL.Cmp.cz (e j) (k + (w : ℤ)) • D j ∈ _root_.Formalism.BasicNotions.compKer T ι) →
    ∀ a : ℕ, (∀ k : ℤ, k < -(a : ℤ) → L k = 0) → ∃ c : ℤ, ∀ M : ℕ,
      _root_.Formalism.BasicNotions.mulVR T (tS ^ a) (_root_.Formalism.BasicNotions.mulVR T pk z) -
        _root_.Formalism.BasicNotions.mulVR T pk (∑ k ∈ Finset.range M, _root_.Formalism.BasicNotions.mulVR T (tS ^ k) (L ((k : ℤ) - (a : ℤ)))) ∈
      _root_.Formalism.BasicNotions.compKer T ι ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ T ι tS pk
    hunit htS r w z D b e L hz hb hL a hLa
  classical
  set C := _root_.Formalism.BasicNotions.compKer T ι with hC

  set t : BdRˣ := hunit.unit with ht_def
  have htt : (t : BdR) = tS := hunit.unit_spec
  set τ : ℤ → BdR := fun n => ((t ^ n : BdRˣ) : BdR) with hτ_def
  have τ_add : ∀ m n : ℤ, τ (m + n) = τ m * τ n := fun m n => by
    simp only [hτ_def, zpow_add, Units.val_mul]
  have τ_nat : ∀ n : ℕ, τ n = tS ^ n := fun n => by
    simp only [hτ_def, zpow_natCast, Units.val_pow_eq_pow_val, htt]

  obtain ⟨q₁, hq₁⟩ := PD.Fil_exh (1 : BdR)
  have hpow : ∀ n : ℕ, tS ^ n ∈ PD.Fil (q₁ + n) := by
    intro n
    induction n with
    | zero => simpa using hq₁
    | succ n ih =>
      rw [pow_succ]
      convert PD.Fil_mul _ _ _ _ ih htS using 2
      push_cast
      ring
  obtain ⟨p, hp⟩ := PD.Fil_exh pk
  set β₀ : BdR := pk * τ ((a : ℤ) - w) with hβ₀_def
  obtain ⟨q₂, hq₂⟩ := PD.Fil_exh β₀
  choose dj hdj using fun j => exists_mem_filV' PD (LL := LL) (D j)
  set d : ℤ := -∑ j, |dj j| with hd_def
  have hDd : ∀ j, D j ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) d := fun j => by
    refine filV_antitone' PD ?_ (hdj j)
    have h1 : |dj j| ≤ ∑ i, |dj i| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (dj i)) (Finset.mem_univ j)
    have h2 := neg_abs_le (dj j)
    linarith
  have hmulS : ∀ {β : BdR} {q n : ℤ} {x : T.V ⊗[Qp] BdR}, β ∈ PD.Fil q →
      x ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) n →
      _root_.Formalism.BasicNotions.mulVR T β x ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (q + n) := by
    intro β q n x hβ hx
    obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (mulVR_mem_compKer T ι β hy) (mulRight_mem_filV_lemma_4 PD T hβ hy')
  have hsupmono : ∀ {m n : ℤ}, n ≤ m → C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) m ≤
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) n := fun h => sup_le_sup_left (filV_antitone' PD h) _

  have hcoeff : ∀ (f : PowerSeries LL) (k : ℕ), _root_.GlobalTheory.HWL.Cmp.cz f (k : ℤ) = PowerSeries.coeff k f := by
    intro f k
    simp [_root_.GlobalTheory.HWL.Cmp.cz]
  have hLC : ∀ i : ℤ, i < -(w : ℤ) → L i ∈ C := by
    intro i hi
    have h := hL i
    simpa [_root_.GlobalTheory.HWL.Cmp.cz_neg _ (show i + (w : ℤ) < 0 by omega)] using h
  have hLF : ∀ i : ℤ, L i ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) d := by
    intro i
    have hs : ∑ j, _root_.GlobalTheory.HWL.Cmp.cz (e j) (i + (w : ℤ)) • D j ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) d :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hDd j)
    have h := Submodule.add_mem_sup (hL i) hs
    rwa [sub_add_cancel] at h

  set H : ℤ → T.V ⊗[Qp] BdR := fun i => _root_.Formalism.BasicNotions.mulVR T (pk * τ (i + a)) (L i) with hH_def
  have hH0 : ∀ i : ℤ, i < -(a : ℤ) → H i = 0 := fun i hi => by
    simp only [hH_def, hLa i hi, map_zero]
  have hHC : ∀ i : ℤ, i < -(w : ℤ) → H i ∈ C := fun i hi =>
    mulVR_mem_compKer T ι _ (hLC i hi)
  have hHF : ∀ (N : ℕ) (i : ℤ), (N : ℤ) ≤ i + a →
      H i ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (N + (p + q₁ + d)) := by
    intro N i hi
    obtain ⟨n, hn⟩ : ∃ n : ℕ, i + a = n := ⟨(i + a).toNat, by omega⟩
    have hβ : pk * τ (i + a) ∈ PD.Fil (p + (q₁ + n)) := by
      rw [hn, τ_nat]
      exact PD.Fil_mul _ _ _ _ hp (hpow n)
    refine hsupmono ?_ (hmulS hβ (hLF i))
    omega

  have hbase : ∑ k ∈ Finset.range w, H ((k : ℤ) - w) - ∑ k ∈ Finset.range a, H ((k : ℤ) - a) ∈ C := by
    have e1 : ∑ k ∈ Finset.range (a + w), H ((k : ℤ) - ((a + w : ℕ) : ℤ)) =
        ∑ k ∈ Finset.range a, H ((k : ℤ) - ((a + w : ℕ) : ℤ)) +
          ∑ k ∈ Finset.range w, H ((k : ℤ) - w) := by
      rw [Finset.sum_range_add]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      push_cast
      ring
    have e2 : ∑ k ∈ Finset.range (a + w), H ((k : ℤ) - ((a + w : ℕ) : ℤ)) =
        ∑ k ∈ Finset.range a, H ((k : ℤ) - a) := by
      rw [add_comm a w, Finset.sum_range_add, Finset.sum_eq_zero (fun k hk => hH0 _ ?_), zero_add]
      · refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        push_cast
        ring
      · have := Finset.mem_range.mp hk
        push_cast
        omega
    have hC1 : ∑ k ∈ Finset.range a, H ((k : ℤ) - ((a + w : ℕ) : ℤ)) ∈ C :=
      Submodule.sum_mem _ fun k hk => hHC _ (by have := Finset.mem_range.mp hk; push_cast; omega)
    have hrw : ∑ k ∈ Finset.range w, H ((k : ℤ) - w) - ∑ k ∈ Finset.range a, H ((k : ℤ) - a) =
        -∑ k ∈ Finset.range a, H ((k : ℤ) - ((a + w : ℕ) : ℤ)) := by
      rw [← e2, e1]
      abel
    rw [hrw]
    exact neg_mem hC1
  have hshift : ∀ N : ℕ, ∑ k ∈ Finset.range (N + w), H ((k : ℤ) - w) -
      ∑ k ∈ Finset.range (N + a), H ((k : ℤ) - a) ∈ C := by
    intro N
    induction N with
    | zero => simpa using hbase
    | succ N ih =>
      rw [show N + 1 + w = (N + w) + 1 by ring, show N + 1 + a = (N + a) + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
      have heq : H (((N + w : ℕ) : ℤ) - w) = H (((N + a : ℕ) : ℤ) - a) := by
        congr 1
        push_cast
        ring
      rw [heq]
      convert ih using 1
      abel

  refine ⟨-(min (p + q₁ + d) (q₂ + w + d)), fun M => ?_⟩
  have hmin1 := min_le_left (p + q₁ + d) (q₂ + w + d)
  have hmin2 := min_le_right (p + q₁ + d) (q₂ + w + d)
  have hbnd1 : C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (M + (p + q₁ + d)) ≤
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) ((M : ℤ) - -(min (p + q₁ + d) (q₂ + w + d))) :=
    hsupmono (by omega)
  have hbnd2 : C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (q₂ + ((M + w : ℕ) : ℤ) + d) ≤
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) ((M : ℤ) - -(min (p + q₁ + d) (q₂ + w + d))) :=
    hsupmono (by push_cast; omega)

  have hτw : τ ((a : ℤ) - w) * tS ^ w = tS ^ a := by
    rw [← τ_nat w, ← τ_add, sub_add_cancel, τ_nat]
  have eqB : _root_.Formalism.BasicNotions.mulVR T (tS ^ a) (_root_.Formalism.BasicNotions.mulVR T pk z) = _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) := by
    rw [mulVR_mulVR', mulVR_mulVR', hβ₀_def, mul_assoc, hτw, mul_comm]
  have eqC : _root_.Formalism.BasicNotions.mulVR T pk (∑ k ∈ Finset.range M, _root_.Formalism.BasicNotions.mulVR T (tS ^ k) (L ((k : ℤ) - (a : ℤ)))) =
      ∑ k ∈ Finset.range M, H ((k : ℤ) - a) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVR_mulVR', hH_def]
    dsimp only
    rw [sub_add_cancel, τ_nat]
  have m1 : _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) - ∑ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) ∈ C := by
    have h := mulVR_mem_compKer T ι β₀ hz
    rwa [map_sub, map_sum] at h
  have hstep : ∀ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) -
      (∑ k ∈ Finset.range (M + w), PowerSeries.coeff k (e j) • _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (D j) +
        _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
          ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j)) ∈ C := by
    intro j
    have hsplit : _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) =
        ∑ k ∈ Finset.range (M + w),
          _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (_root_.Formalism.BasicNotions.mulVR T (ι (PowerSeries.coeff k (e j))) (D j)) +
        _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
          ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j) := by
      rw [mulVR_mulVR']
      rw [show β₀ * b j = β₀ * (∑ k ∈ Finset.range (M + w), ι (PowerSeries.coeff k (e j)) * tS ^ k) +
          β₀ * (b j - ∑ k ∈ Finset.range (M + w), ι (PowerSeries.coeff k (e j)) * tS ^ k) by ring,
        mulVR_add', Finset.mul_sum, mulVR_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mulVR_mulVR']
      exact congrArg (fun β => _root_.Formalism.BasicNotions.mulVR T β (D j)) (by ring)
    rw [hsplit, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun k _ => ?_
    have h := mulVR_mem_compKer T ι (β₀ * tS ^ k)
      (smul_sub_mulVR_mem_compKer T ι (PowerSeries.coeff k (e j)) (D j))
    rw [map_sub, LinearMap.map_smul] at h
    rw [← neg_sub]
    exact neg_mem h
  have m2 := Submodule.sum_mem C (t := Finset.univ) fun j _ => hstep j
  rw [Finset.sum_sub_distrib] at m2
  have hβk : ∀ k : ℕ, pk * τ ((k : ℤ) - w + a) = β₀ * tS ^ k := fun k => by
    rw [show (k : ℤ) - w + a = ((a : ℤ) - w) + k by ring, τ_add, τ_nat, hβ₀_def, mul_assoc]
  have hterm : ∀ k : ℕ, _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) -
      H ((k : ℤ) - w) ∈ C := by
    intro k
    have h := mulVR_mem_compKer T ι (β₀ * tS ^ k) (hL ((k : ℤ) - w))
    simp only [sub_add_cancel, hcoeff] at h
    have h' := neg_mem h
    rw [← map_neg, neg_sub] at h'
    rw [hH_def]
    dsimp only
    rw [hβk k, ← map_sub]
    exact h'
  have m3 := Submodule.sum_mem C (t := Finset.range (M + w)) fun k _ => hterm k
  rw [Finset.sum_sub_distrib] at m3
  have m4 := hshift M
  have eqD : ∑ k ∈ Finset.range (M + a), H ((k : ℤ) - a) =
      ∑ k ∈ Finset.range M, H ((k : ℤ) - a) + ∑ k ∈ Finset.range a, H (((M + k : ℕ) : ℤ) - a) :=
    Finset.sum_range_add _ _ _
  have m5 : ∑ k ∈ Finset.range a, H (((M + k : ℕ) : ℤ) - a) ∈
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (M + (p + q₁ + d)) :=
    Submodule.sum_mem _ fun k _ => hHF M _ (by push_cast; omega)
  have m6 : ∑ j, _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
      ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j) ∈
      _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (q₂ + ((M + w : ℕ) : ℤ) + d) :=
    Submodule.sum_mem _ fun j _ => mulRight_mem_filV_lemma_4 PD T (PD.Fil_mul _ _ _ _ hq₂ (hb j (M + w)))
      (hDd j)
  have eqA : ∑ j, ∑ k ∈ Finset.range (M + w), PowerSeries.coeff k (e j) • _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (D j) =
      ∑ k ∈ Finset.range (M + w), _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    simp only [LinearMap.map_smul]
  rw [Finset.sum_add_distrib, eqA] at m2
  rw [eqB, eqC]
  have hX : _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) - ∑ k ∈ Finset.range M, H ((k : ℤ) - a) =
      (_root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) - ∑ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j))) +
      (∑ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) -
        (∑ k ∈ Finset.range (M + w), _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) +
          ∑ j, _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
            ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j))) +
      (∑ k ∈ Finset.range (M + w), _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) -
        ∑ k ∈ Finset.range (M + w), H ((k : ℤ) - w)) +
      (∑ k ∈ Finset.range (M + w), H ((k : ℤ) - w) - ∑ k ∈ Finset.range (M + a), H ((k : ℤ) - a)) +
      ∑ k ∈ Finset.range a, H (((M + k : ℕ) : ℤ) - a) +
      ∑ j, _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
        ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j) := by
    rw [eqD]
    abel
  rw [hX]
  refine add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) (hbnd1 m5))
    (hbnd2 (Submodule.mem_sup_right m6))
  · exact Submodule.mem_sup_left m1
  · exact Submodule.mem_sup_left m2
  · exact Submodule.mem_sup_left m3
  · exact Submodule.mem_sup_left m4

end GlobalTheory.HWL.Cmp
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_estimate_expansion_tensorBdR_component : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]  (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) (tS pk : BdR), IsUnit tS → tS ∈ PD.Fil 1 → ∀ (r w : ℕ) (z : T.V ⊗[Qp] BdR) (D : Fin r → T.V ⊗[Qp] BdR) (b : Fin r → BdR) (e : Fin r → PowerSeries LL) (L : ℤ → T.V ⊗[Qp] BdR), mulVR T (tS ^ w) z - ∑ j, mulVR T (b j) (D j) ∈ compKer T ι → (∀ (j : Fin r) (m : ℕ), b j - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (e j)) * tS ^ k ∈ PD.Fil (m : ℤ)) → (∀ k : ℤ, L k - ∑ j, cz (e j) (k + (w : ℤ)) • D j ∈ compKer T ι) → ∀ a : ℕ, (∀ k : ℤ, k < -(a : ℤ) → L k = 0) → ∃ c : ℤ, ∀ M : ℕ, mulVR T (tS ^ a) (mulVR T pk z) - mulVR T pk (∑ k ∈ Finset.range M, mulVR T (tS ^ k) (L ((k : ℤ) - (a : ℤ)))) ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c) := by
  atlas_forward_decl GlobalTheory.HWL.Cmp.filt_expansion_component
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_basis_converging_open_disc : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ), ∀ (r m m' : ℕ) (Gm : Γ.Gam → Matrix (Fin r) (Fin r) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) (Pm Pm' : Matrix (Fin r) (Fin r) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))), (∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (R.γ₀ g))) → (∀ g i j k, PowerSeries.constantCoeff (Gm g i j k) = if i = j then 1 else 0) → Pm * Pm' = (R.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) → (∀ g, (letγ (R.γ₀ g) R.Q ^ m) • (Pm * (Gm g).map (letφ R.φ₀)) = (R.Q ^ m) • (Gm g * Pm.map (letγ (R.γ₀ g)))) → ∃ (U V : Matrix (Fin r) (Fin r) (LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)))) (w : ℕ), U * V = 1 ∧ (∀ i j k, PowerSeries.constantCoeff (U i j k) = if i = j then 1 else 0) ∧ (∀ i j k, Conv (logS LL ^ w * U i j k) ∧ Conv (logS LL ^ w * V i j k)) ∧ (∀ g, (Gm g).map toLL * U.map (fun a k => PowerSeries.subst (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.γ₀ g PowerSeries.X)) (a k)) = U) ∧ ∃ Cm : Matrix (Fin r) (Fin r) (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥LL.1), Pm.map toLL * U.map (fun a k => PowerSeries.subst ((1 + PowerSeries.X) ^ l - 1 : PowerSeries ↥LL.1) (a (k - 1))) = (toLL R.Q ^ m) • (U * Cm.map (fun c k => PowerSeries.C (c k))) := by
  first | exact @GlobalTheory.HWL.exists_invariant_basis_conv | exact GlobalTheory.HWL.exists_invariant_basis_conv | (intros; apply GlobalTheory.HWL.exists_invariant_basis_conv <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_ainf_sandwich_invert_pi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (Mo : NS E) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → ∃ m : ℕ, Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) := by
  first | exact @GlobalTheory.HWL.SandProof.sandwich | exact GlobalTheory.HWL.SandProof.sandwich | (intros; apply GlobalTheory.HWL.SandProof.sandwich <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWLBeta

theorem exists_beta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ LL : FinExt l, ∃ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β := by
  intro l _ P AI T LL
  have hz := (GlobalTheory.TiedMu.tied_mu_units l P AI T).2.2.2
  let _ : Algebra ℤ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) :=
    ((algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  let f : ↥(OL LL) →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom).comp (OL LL).val.toRingHom
      commutes' := fun z => by
        show ((algebraMap ℤ_[l] ↥LL.1 z) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1] }
  let g : Ainf l →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)).toRingHom.comp AI.ιA
      commutes' := fun z => by
        show Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)
            (AI.ιA (algebraMap ℤ_[l] (Ainf l) z)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [hz, AlgHom.commutes]
        rfl }
  refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, fun o w => ?_⟩
  show Algebra.TensorProduct.productMap f g (o ⊗ₜ[ℤ_[l]] w) = _
  rw [Algebra.TensorProduct.productMap_apply_tmul]
  show ((o : ↥LL.1) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) * ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] AI.ιA w) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end GlobalTheory.HWLBeta
end

section
noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s}

variable {R : WSer Γ} {b₀ : LetA O n →+* LL ⊗[Qp] B} {tS zS : BdR}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n}

open Classical in

def levOf {Dc : Disc R b₀ tS zS} {Mo : WN E zl} (bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B)
    (Fr : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Frame Dc Mo T) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) :
    ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] B) :=
  if h : IsCrys PD T.ρ then (Fr T h).lev bT i ζ else 0

set_option maxHeartbeats 1000000 in
theorem nonempty_wCmp [NeZero n] (Dc : Disc R b₀ tS zS) (Mo : WN E zl) {ιdR : Ai →+* BdR} {p1 : Ai}
    {βdR : ∀ T : LocLat G Qp LL O, TW (O ⊗[Zl] Ai) T →+ T.V ⊗[Qp] BdR}
    {bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B} (hP : IsPer Mo b₀ ιdR p1 βdR bT)
    (Fr : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Frame Dc Mo T)
    (hinv : ∀ a : LetA LL n, γL R Γ.gam a = a → ∃ c, a = cst c) : Nonempty (WCmp Mo ιdR p1 tS zS) := by
  have pos : ∀ (T : LocLat G Qp LL O) (h : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL), levOf bT Fr T i ζ = Frame.lev bT (Fr T h) i ζ :=
    fun T h i ζ => dif_pos h
  have neg : ∀ (T : LocLat G Qp LL O) (_ : ¬ IsCrys PD T.ρ) (i : ZMod n) (ζ : LL), levOf bT Fr T i ζ = 0 := fun T h i ζ => dif_neg h
  have hmem : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ), levOf bT Fr T i ζ x k ∈ DcrisL PD T.ρ (Γ.emb i) := by
    intro T i ζ x k
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_mem hP h _ i ζ x k
    · rw [neg T h]; exact Submodule.zero_mem _
  have hsupp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)), ∃ m : ℤ, ∀ k < m, levOf bT Fr T i ζ x k = 0 := by
    intro T i ζ x
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact ⟨_, Frame.lev_supp bT _ i ζ x⟩
    · rw [neg T h]; exact ⟨0, fun _ _ => rfl⟩
  have hneg : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(Mo.N T)) (k : ℤ), k < 0 → levOf bT Fr T i 1 x k = 0 := by
    intro T i x k hk
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_one_neg bT _ i x k hk
    · rw [neg T h]; rfl
  have hsmul : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (α : LetA O n) (x : ↥(Mo.N T)) (k : ℤ), levOf bT Fr T i ζ (α • x) k =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (R.lev i ζ α) • levOf bT Fr T i ζ x (k - (j : ℤ)) := by
    intro T i ζ α x k
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_smul bT _ i ζ α x k
    · rw [neg T h]; simp
  have hsmul0 : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (α : LetA O n) (x : ↥(Mo.N T)), levOf bT Fr T i 1 (α • x) 0 =
      PowerSeries.constantCoeff (R.lev i 1 α) • levOf bT Fr T i 1 x 0 := by
    intro T i α x
    rw [hsmul, finsum_eq_single _ 0]
    · simp
    · intro j hj
      rw [hneg T i x _ (by omega), smul_zero]
  let cmp : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B := fun T =>
    ∑ i : ZMod n, (Pi.evalAddMonoidHom (fun _ : ℤ => T.V ⊗[Qp] B) 0).comp (levOf bT Fr T i 1)
  have hcmp : ∀ (T : LocLat G Qp LL O) (x : ↥(Mo.N T)), cmp T x = ∑ i : ZMod n, levOf bT Fr T i 1 x 0 := by
    intro T x
    simp [cmp, AddMonoidHom.finset_sum_apply]
  have hcmpE : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(Mo.N T)), cmp T ((letE i : LetA O n) • x) = levOf bT Fr T i 1 x 0 := by
    intro T i x
    rw [hcmp, Finset.sum_eq_single i]
    · rw [hsmul0, Dc.lev_letE]; simp
    · intro j _ hj
      rw [hsmul0, Dc.lev_letE]; simp [hj]
    · simp
  have hmap : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
      ∀ (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (hx : E.map f (x : E.DD T) ∈ Mo.N T') (k : ℤ),
      levOf bT Fr T' i ζ ⟨E.map f (x : E.DD T), hx⟩ k =
        AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] B) (levOf bT Fr T i ζ x k) := by
    intro T T' f h h' i ζ x hx k
    rw [pos T h, pos T' h']
    exact Frame.lev_map hP hinv f h h' _ _ i ζ x hx k
  let levN : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] BdR) := fun T i ζ =>
    ((ιV PD (LL := LL) (V := T.V)).toAddMonoidHom.compLeft ℤ).comp (levOf bT Fr T i ζ)
  have hN : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ), levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (levOf bT Fr T i ζ x k) :=
    fun _ _ _ _ _ => rfl
  refine ⟨{
    cmp := cmp
    cmp_smul := fun T c x => ?_
    cmp_π := fun T x => ?_
    cmp_mem := fun T x => ?_
    cmp_letter := fun T i x => by rw [hcmpE]; exact hmem T i 1 x 0
    cmp_map := fun f h h' x hx => by simp only [hcmp, hmap f h h', map_sum]
    levN := levN
    levN_supp := fun T i ζ x => ?_
    levN_smul := fun T i ζ α x k => ?_
    levN_map := fun {T T'} f h h' i ζ x hx k => ?_
    levB := levOf bT Fr
    levB_mem := hmem
    levB_supp := hsupp
    levN_eq := hN
    cmp_eq := fun T _ => hcmpE T
    levB_φ := fun T h i ζ hζ x m hx k => by
      simp only [pos T h]; exact Frame.lev_φ hP h _ i ζ hζ x m hx k
    levB_Γ := fun T h g i ζ ζ' j a h1 h2 h3 x hx k => by
      simp only [pos T h]; exact Frame.lev_Γ bT _ g i ζ ζ' j a h1 h2 h3 x hx k
    βdR := βdR
    βdR_tmul := hP.tmul
    levN_dR := fun T h i ζ ι h1 h2 x k y hy a ha => ?_ }⟩
  · have : c • x = algebraMap O (LetA O n) c • x := Subtype.ext (algebraMap_smul (LetA O n) c (x : E.DD T)).symm
    rw [this, hcmp, hcmp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul0, AlgHom.commutes]
    simp [PowerSeries.algebraMap_apply]
  · rw [hcmp]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨e, he, -, h3⟩ := R.lev_π i 1 ⟨0, by simp⟩
    have h4 := congrArg PowerSeries.constantCoeff h3
    rw [map_add, map_mul, he] at h4
    have h5 : PowerSeries.constantCoeff (R.lev i 1 letπ) = 0 := by simpa using h4
    rw [hsmul0, h5, zero_smul]
  · rw [hcmp]
    exact Submodule.sum_mem _ fun i _ => (hmem T i 1 x 0).1
  · obtain ⟨m, hm⟩ := hsupp T i ζ x
    exact ⟨m, fun k hk => by rw [hN, hm k hk, map_zero]⟩
  · obtain ⟨m, hm⟩ := hsupp T i ζ x
    have hz : ∀ j : ℕ, j ∉ Finset.range ((k - m).toNat + 1) → levOf bT Fr T i ζ x (k - (j : ℤ)) = 0 := by
      intro j hj
      have : (k - m).toNat + 1 ≤ j := by simpa using hj
      exact hm _ (by omega)
    rw [hN, hsmul, finsum_eq_sum_of_support_subset (s := Finset.range ((k - m).toNat + 1)),
      finsum_eq_sum_of_support_subset (s := Finset.range ((k - m).toNat + 1)), map_sum]
    · simp only [map_smul, hN]
    · intro j hj
      by_contra hc
      exact hj (by simp only [hN, hz j hc, map_zero, smul_zero])
    · intro j hj
      by_contra hc
      exact hj (by simp only [hz j hc, smul_zero])
  · rw [hN, hN, hmap f h h']
    induction levOf bT Fr T i ζ x k using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b => simp [ιV]
  · rw [hP.dR T h x k y hy]
    refine GlobalTheory.T.filtration_estimate_expansion_tensorBdR_component PD T ι tS (ιdR p1 ^ k) (Dc.ι_tb ▸ Dc.tb_unit.map PD.ι) Dc.tS_mem (Fr T h).r (Fr T h).w _
      (fun j => ιV PD (LL := LL) (V := T.V) ((Fr T h).d bT j)) _ (fun j => Dc.ex i ζ ((Fr T h).a x j)) _
      (Frame.dR_basis hP h (Fr T h) ι x) (fun j m => Dc.taylor i ζ ι h1 h2 _ m) (fun k => ?_) a ha
    rw [hN, pos T h]
    exact Frame.dR_lev (Fr T h) i ζ ι h1 h2 x k

end Generic

theorem chi_gam_pow_ne_one {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (hG : Good K s LL) (Γ : GamS P K s LL) (k : ℕ) (hk : 0 < k) :
    algebraMap ↥(OL LL) ↥LL.1 (Γ.χΓ Γ.gam : ↥(OL LL)) ^ k ≠ 1 := by
  intro h
  obtain ⟨⟨lam, -, h1, h2, ⟨g, hg⟩, -⟩, -⟩ := GlobalTheory.HWL.Coord.exists_gamma_coordinates l P K s LL hG Γ
  have h3 : Γ.gam ^ k = 1 := by
    apply Γ.χΓ_inj
    rw [map_pow, map_one]
    apply Units.ext
    apply Subtype.ext
    simpa using h
  have h4 : lam (g ^ k) = 1 := by
    rw [h1, Subgroup.coe_pow, map_pow, (h2 g).mp hg, h3]
  rw [map_pow, hg, ← ofAdd_nsmul, ofAdd_eq_one] at h4
  simp at h4
  omega

set_option maxHeartbeats 1000000 in

theorem nonempty_cmpS : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R),
    IoW I → ∀ (E : WEt I) (Mo : NS E), Nonempty (CmpS Mo) := by
  intro l _ P AI hT K s LL hG Γ R I hI E Mo
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.HWLBeta.exists_beta l P AI hT LL
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_evaluation_convergent_series_Bcris l P AI hT K s LL hG Γ R I hI β hβ
  obtain ⟨Dc, hC, ht⟩ := GlobalTheory.T.exists_openDiscConvergentRing_with_expansions l P AI hT K s LL hG Γ R I hI β hβ J hJ (GlobalTheory.T.cyclotomicPowerSeriesData_lev_isExpansionAtZeta l P K s LL Γ R)
    (GlobalTheory.T.maxUnramified_acts_on_letterIdempotent_image l P AI hT K s LL hG Γ R I hI β hβ)
  obtain ⟨βdR, bT, hP⟩ := GlobalTheory.T.exists_wachModule_periodMap_to_bcris l P AI hT K s LL hG Γ R I hI β hβ E Mo
    (GlobalTheory.T.wachLattice_ainf_sandwich_invert_pi l P AI K s LL hG Γ R I hI E Mo)
  have hF : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ → Nonempty (Frame Dc Mo T) := by
    intro T h
    obtain ⟨nb⟩ := GlobalTheory.T.wach_lattice_free_of_crystalline l P AI K s LL hG Γ R I hI E Mo T h
    obtain ⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_wachLattice_matrices_gamma_phi Mo T _ nb
    obtain ⟨U, V, w, k1, -, k3, k4, Cm, k5⟩ := GlobalTheory.T.exists_invariant_basis_converging_open_disc l P K s LL hG Γ R _ m m' Gm Pm Pm' h1 h2 h3 h4
    refine ⟨{
      r := _, w := w, m := m, nb := nb, U := U, V := V, UV := k1
      U_mem := fun i j => hC _ fun k => by rw [ht]; exact (k3 i j k).1
      V_mem := fun i j => hC _ fun k => by rw [ht]; exact (k3 i j k).2
      Gm := Gm, Gm_def := h5
      GU := fun g => ?_
      Pm := Pm, Pm_def := h6, Cm := Cm
      PU := ?_ }⟩
    · rw [funext (γL_apply R g)]
      exact k4 g
    · have e1 : ⇑(φL ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) (P.PD K).p) = fun a k =>
          PowerSeries.subst ((1 + PowerSeries.X) ^ l - 1 : PowerSeries ↥LL.1) (a (k - 1)) := by
        funext a
        rw [φL_apply, P.PD_p]
      have e2 : toL ↥(OL LL) ↥LL.1 _ (R.Q ^ m) = toLL R.Q ^ m := (toL ↥(OL LL) ↥LL.1 _).map_pow R.Q m
      rw [e1]
      exact k5.trans (congrArg (fun q : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) => q • (U * Cm.map cst)) e2.symm)
  refine nonempty_wCmp Dc Mo hP (fun T h => (hF T h).some) fun a ha => ?_
  refine ⟨fun i => PowerSeries.constantCoeff (a i), funext fun i => ?_⟩
  refine GlobalTheory.T.powerSeries_eq_C_of_subst_fixed_not_root_of_unity _ (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.γ₀ Γ.gam PowerSeries.X)) ?_ ?_ (a i) ?_
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (R.γ₀_X _).1, map_zero]
  · intro k hk
    rw [PowerSeries.coeff_map, (R.γ₀_X _).2]
    exact chi_gam_pow_ne_one hG Γ k hk
  · rw [γL_apply] at ha
    exact congrFun ha i

end GlobalTheory.HWL.Cmp
end
end
