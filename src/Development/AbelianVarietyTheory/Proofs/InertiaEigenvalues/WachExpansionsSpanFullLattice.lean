import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachImageDeRhamPlusComponentLevel

section
section
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.MemLoc
open scoped Formalism.Per

namespace Bridge.TateSpanAlt

theorem exists_ev {L A : Type*} [Field L] [CommRing A] (t : A)
    [hc : IsAdicComplete (Ideal.span {t}) A] (ι : L →+* A) :
    ∃ ev : PowerSeries L →+* A, (∀ c, ev (PowerSeries.C c) = ι c) ∧ ev PowerSeries.X = t := by
  letI : WithIdeal A := ⟨Ideal.span {t}⟩
  letI : UniformSpace L := ⊥
  haveI : DiscreteUniformity L := ⟨rfl⟩
  have hadic : IsAdic (Ideal.span {t}) := rfl
  obtain ⟨h1, h2⟩ := (hadic.isAdicComplete_iff).1 hc
  haveI : IsLinearTopology A A := Ideal.isLinearTopology (Ideal.span {t})
  have hι : Continuous ι := continuous_of_discreteTopology
  have ht : PowerSeries.HasEval t := by
    refine (WithIdeal.isTopologicallyNilpotent_of_mem ?_)
    exact Ideal.mem_span_singleton_self t
  refine ⟨PowerSeries.eval₂Hom hι ht, fun c => ?_, ?_⟩
  · rw [PowerSeries.coe_eval₂Hom]; exact PowerSeries.eval₂_C _ _ _
  · rw [PowerSeries.coe_eval₂Hom]; exact PowerSeries.eval₂_X _ _

theorem ev_sub {L A : Type*} [Field L] [CommRing A] (t : A) (ι : L →+* A)
    (ev : PowerSeries L →+* A) (hC : ∀ c, ev (PowerSeries.C c) = ι c) (hX : ev PowerSeries.X = t)
    (f : PowerSeries L) (M : ℕ) :
    t ^ M ∣ ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * t ^ k := by
  have h : (PowerSeries.X : PowerSeries L) ^ M ∣
      f - ∑ k ∈ Finset.range M, PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, hm]
  have := map_dvd ev h
  simpa [map_sum, hC, hX] using this

theorem ev_dvd_iff {L A : Type*} [Field L] [CommRing A] [IsDomain A] (t : A) (ht0 : t ≠ 0)
    (htu : ¬ IsUnit t) (ι : L →+* A)
    (ev : PowerSeries L →+* A) (hC : ∀ c, ev (PowerSeries.C c) = ι c) (hX : ev PowerSeries.X = t)
    (f : PowerSeries L) (M : ℕ) :
    t ^ M ∣ ev f ↔ (PowerSeries.X : PowerSeries L) ^ M ∣ f := by
  constructor
  · induction M with
    | zero => simp
    | succ n ih =>
      intro h
      obtain ⟨g, rfl⟩ := ih ((pow_dvd_pow t n.le_succ).trans h)
      rw [map_mul, map_pow, hX, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n ht0)] at h
      rw [pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [PowerSeries.X_dvd_iff]
      by_contra hg
      have hu : IsUnit g := PowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hg)
      exact htu (isUnit_of_dvd_unit h (hu.map ev))
  · intro h
    simpa [hX] using map_dvd ev h

open Reformulated.AutPerF Formalism in
open scoped Formalism.Per in

theorem main (l : ℕ) [Fact l.Prime] {B L : Type*} [CommRing B] [Field L]
    (e : B ≃+* BdR l (Per.OC l)) (Fil : ℤ → B → Prop)
    (hF : ∀ a x, Fil a x ↔ e x ∈ BdR.fil l (Per.OC l) a) (t : B) (π : BdRPlus l (Per.OC l))
    (hπ : RingHom.ker (BdRPlus.theta l (Per.OC l)) = Ideal.span {π})
    (ht : e t = algebraMap _ _ π) (ι : L →+* B) (hι : ∀ x, Fil 0 (ι x)) :
    ∃ ev : PowerSeries L →+* B,
      (∀ f (M : ℕ), Fil M (ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * t ^ k)) ∧
      (∀ f (M : ℕ), Fil M (ev f) ↔ (PowerSeries.X : PowerSeries L) ^ M ∣ f) ∧ IsUnit t ∧
      (∀ (a : ℤ) (b : B), Fil (a + 1) (t * b) ↔ Fil a b) ∧ ∀ b, (∀ a, Fil a b) → b = 0 := by
  have hinj : Function.Injective (algebraMap (BdRPlus l (Per.OC l)) (BdR l (Per.OC l))) :=
    BdR.algebraMap_injective
  have h0 := BdR.algebraMap_ne_zero hπ
  have hirr := (BdRPlus.irreducible_iff π).2 hπ
  choose j hj using fun x => (BdR.mem_fil_zero_iff _).1 ((hF _ _).1 (hι x))
  let ι₀ : L →+* BdRPlus l (Per.OC l) :=
    { toFun := j
      map_one' := hinj (by rw [hj]; simp)
      map_mul' := fun x y => hinj (by rw [map_mul, hj, hj, hj, map_mul, map_mul])
      map_zero' := hinj (by rw [hj]; simp)
      map_add' := fun x y => hinj (by rw [map_add, hj, hj, hj, map_add, map_add]) }
  have hj' : ∀ x, algebraMap _ (BdR l (Per.OC l)) (ι₀ x) = e (ι x) := hj
  haveI : IsAdicComplete (Ideal.span {π}) (BdRPlus l (Per.OC l)) := by
    rw [← hπ]; infer_instance
  obtain ⟨ev, hC, hX⟩ := exists_ev π ι₀
  have key : ∀ (M : ℕ) (y : BdRPlus l (Per.OC l)),
      algebraMap _ (BdR l (Per.OC l)) y ∈ BdR.fil l (Per.OC l) M ↔ π ^ M ∣ y := fun M y => by
    rw [BdR.algebraMap_mem_fil_iff, BdRPlus.fil, hπ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  refine ⟨e.symm.toRingHom.comp ((algebraMap _ (BdR l (Per.OC l))).comp ev), fun f M => ?_,
    fun f M => ?_, ?_, fun a b => ?_, fun b hb => ?_⟩
  · have := (key M _).2 (ev_sub π ι₀ ev hC hX f M)
    rw [hF]
    convert this using 1
    simp [map_sum, hj', ht]
  · rw [hF, ← ev_dvd_iff π hirr.ne_zero hirr.not_isUnit ι₀ ev hC hX, ← key]
    simp
  · have := (h0.isUnit).map e.symm
    rwa [← ht, e.symm_apply_apply] at this
  · rw [hF, hF, map_mul, ht, BdR.mem_fil_iff hπ, BdR.mem_fil_iff hπ]
    refine exists_congr fun c => ?_
    rw [zpow_add_one₀ h0, mul_comm _ (algebraMap _ _ π), mul_assoc, mul_right_inj' h0]
  · exact e.injective (by
      rw [map_zero]; exact BdR.eq_zero_of_forall_mem_fil fun a => (hF _ _).1 (hb a))

open Reformulated.AutPerF Formalism in
open scoped Formalism.Per in

theorem exists_gen (l : ℕ) [Fact l.Prime] (x : BdR l (Per.OC l))
    (h1 : x ∈ BdR.fil l (Per.OC l) 1) (h2 : x ∉ BdR.fil l (Per.OC l) 2) :
    ∃ π : BdRPlus l (Per.OC l), RingHom.ker (BdRPlus.theta l (Per.OC l)) = Ideal.span {π} ∧
      x = algebraMap _ _ π := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat l (Per.OC l)) := inferInstance
  have hξ := BdRPlus.ker_theta ϖ
  obtain ⟨c, hc⟩ := (BdR.mem_fil_iff hξ 1 x).1 h1
  have hu : IsUnit c := by
    rw [BdRPlus.isUnit_iff_theta_ne_zero, Ne, BdRPlus.theta_eq_zero_iff_dvd ϖ]
    rintro ⟨d, rfl⟩
    exact h2 ((BdR.mem_fil_iff hξ 2 x).2 ⟨d, by rw [hc, map_mul, zpow_one, zpow_two, mul_assoc]⟩)
  exact ⟨BdRPlus.xi ϖ * c, by rw [Ideal.span_singleton_mul_right_unit hu, hξ],
    by rw [hc, zpow_one, map_mul]⟩

open Reformulated.AutPerF Formalism in
open scoped Formalism.Per in
theorem main' (l : ℕ) [Fact l.Prime] {B L : Type*} [CommRing B] [Field L]
    (e : B ≃+* Per.BdR l) (Fil : ℤ → B → Prop)
    (hF : ∀ a x, Fil a x ↔ e x ∈ Per.FilD l a) (t : B) (h1 : Fil 1 t) (h2 : ¬ Fil 2 t)
    (ι : L →+* B) (hι : ∀ x, Fil 0 (ι x)) :
    ∃ ev : PowerSeries L →+* B,
      (∀ f (M : ℕ), Fil M (ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * t ^ k)) ∧
      (∀ f (M : ℕ), Fil M (ev f) ↔ (PowerSeries.X : PowerSeries L) ^ M ∣ f) ∧ IsUnit t ∧
      (∀ (a : ℤ) (b : B), Fil (a + 1) (t * b) ↔ Fil a b) ∧ ∀ b, (∀ a, Fil a b) → b = 0 := by
  obtain ⟨π, hπ, ht⟩ := exists_gen l (e t) ((hF _ _).1 h1) (fun h => h2 ((hF _ _).2 h))
  exact main l e Fil hF t π hπ ht ι hι

open Reformulated.AutPerF in

theorem mem_zero_of_isIntegral (l : ℕ) [Fact l.Prime] {F B : Type*} [Field F] [CommRing B]
    [Algebra F B] (e : B ≃+* BdR l (Per.OC l))
    (h : ∀ c : F, ∃ y : BdRPlus l (Per.OC l), algebraMap _ _ y = e (algebraMap F B c))
    {x : B} (hx : IsIntegral F x) : e x ∈ BdR.fil l (Per.OC l) 0 := by
  rw [BdR.mem_fil_zero_iff, ← IsIntegrallyClosed.isIntegral_iff]
  obtain ⟨q, hq, h0⟩ := hx
  have hl : q.map (e.toRingHom.comp (algebraMap F B)) ∈
      Polynomial.lifts (algebraMap (BdRPlus l (Per.OC l)) (BdR l (Per.OC l))) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact h _
  obtain ⟨r, hr, -, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (hq.map _)
  refine ⟨r, hm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hr, ← Polynomial.eval₂_eq_eval_map]
  have := Polynomial.hom_eval₂ q (algebraMap F B) e.toRingHom x
  rw [h0, map_zero] at this
  exact this.symm

theorem mem_zero (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) {x : P.R.BdR} (hx : IsIntegral ℚ_[l] x) : x ∈ (P.PD K).Fil 0 := by
  refine (T.fil K 0 x).2 (mem_zero_of_isIntegral l _ (fun c => ?_) hx)
  obtain ⟨y, h1, -⟩ := T.om (algebraMap ℚ_[l] (Om l) c)
  rw [← IsScalarTower.algebraMap_apply] at h1
  exact ⟨y, h1.symm⟩

theorem reduction (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K LL : FinExt l) (s : ℕ) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR)
    (h1 : GlobalTheory.NL.tS P s ∈ (P.PD K).Fil 1) (h2 : GlobalTheory.NL.tS P s ∉ (P.PD K).Fil 2) :
    ∃ ev : PowerSeries ↥LL.1 →+* P.R.BdR,
      (∀ f (M : ℕ), (ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * GlobalTheory.NL.tS P s ^ k) ∈
        (P.PD K).Fil M) ∧
      (∀ f (M : ℕ), ev f ∈ (P.PD K).Fil M ↔ (PowerSeries.X : PowerSeries ↥LL.1) ^ M ∣ f) ∧
      IsUnit (GlobalTheory.NL.tS P s) ∧
      (∀ (a : ℤ) (b : P.R.BdR), GlobalTheory.NL.tS P s * b ∈ (P.PD K).Fil (a + 1) ↔ b ∈ (P.PD K).Fil a) ∧
      ∀ b : P.R.BdR, (∀ a, b ∈ (P.PD K).Fil a) → b = 0 :=
  main' l _ (fun a x => x ∈ (P.PD K).Fil a) (fun a x => T.fil K a x) _ h1 h2 ι.toRingHom
    (fun x => by
      haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
      exact mem_zero l P AI T K ((IsIntegral.of_finite ℚ_[l] x).map ι))

theorem smul_mem (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (c : ℚ_[l]) (a : ℤ) (x : P.R.BdR) (hx : x ∈ (P.PD K).Fil a) :
    c • x ∈ (P.PD K).Fil a := by
  have h0 := (T.fil K 0 _).1 (mem_zero l P AI T K (isIntegral_algebraMap (x := c)))
  refine (T.fil K a _).2 ?_
  rw [Algebra.smul_def, map_mul]
  have := Reformulated.AutPerF.BdR.mul_mem_fil (p := l) (R := Per.OC l) h0 ((T.fil K a _).1 hx)
  rw [zero_add] at this
  exact this

theorem tS_mem_iff (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (s : ℕ) (a : ℤ) :
    GlobalTheory.NL.tS P s ∈ (P.PD K).Fil a ↔ P.ιB P.tB ∈ (P.PD K).Fil a := by
  refine ⟨fun h => ?_, smul_mem l P AI T K _ a _⟩
  have := smul_mem l P AI T K ((l : ℚ_[l]) ^ s) a _ h
  rwa [GlobalTheory.NL.tS, smul_smul, mul_inv_cancel₀
    (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)), one_smul] at this

theorem reduction' (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K LL : FinExt l) (s : ℕ) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR)
    (h1 : P.ιB P.tB ∈ (P.PD K).Fil 1) (h2 : P.ιB P.tB ∉ (P.PD K).Fil 2) :
    ∃ ev : PowerSeries ↥LL.1 →+* P.R.BdR,
      (∀ f (M : ℕ), (ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * GlobalTheory.NL.tS P s ^ k) ∈
        (P.PD K).Fil M) ∧
      (∀ f (M : ℕ), ev f ∈ (P.PD K).Fil M ↔ (PowerSeries.X : PowerSeries ↥LL.1) ^ M ∣ f) ∧
      IsUnit (GlobalTheory.NL.tS P s) ∧
      (∀ (a : ℤ) (b : P.R.BdR), GlobalTheory.NL.tS P s * b ∈ (P.PD K).Fil (a + 1) ↔ b ∈ (P.PD K).Fil a) ∧
      ∀ b : P.R.BdR, (∀ a, b ∈ (P.PD K).Fil a) → b = 0 :=
  reduction l P AI T K LL s ι ((tS_mem_iff l P AI T K s 1).2 h1)
    (fun h => h2 ((tS_mem_iff l P AI T K s 2).1 h))

end Bridge.TateSpanAlt

theorem Bridge.exists_power_series_evaluation : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P) (T : Formalism.BasicNotions.LocTied l P AI) (K LL : Formalism.BasicNotions.Loc.FinExt l) (s : ℕ) (ι : ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K)) →ₐ[ℚ_[l]] P.R.BdR), ∃ (ev : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K)) →+* P.R.BdR), (∀ (f : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (M : ℕ), HSub.hSub (α := P.R.BdR) (β := P.R.BdR) (DFunLike.coe (β := fun (x : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) ↦ P.R.BdR) ev f : P.R.BdR) (∑ k ∈ Finset.range M, HMul.hMul (α := P.R.BdR) (DFunLike.coe (α := ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (β := fun (x : ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) ↦ P.R.BdR) ι (DFunLike.coe (F := LinearMap (R := ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (RingHom.id ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (β := fun (x : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) ↦ ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (PowerSeries.coeff k) f : ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) : P.R.BdR) (GlobalTheory.NL.tS P s ^ k) : P.R.BdR) ∈ (P.PD K).Fil M.cast) ∧ (∀ (f : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) (M : ℕ), Membership.mem (α := P.R.BdR) ((P.PD K).Fil M.cast) (DFunLike.coe (β := fun (x : PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) ↦ P.R.BdR) ev f : P.R.BdR) ↔ HPow.hPow (α := PowerSeries ↥(LL.val (p := fun (K : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↦ FiniteDimensional ℚ_[l] ↥K))) PowerSeries.X M ∣ f) ∧ IsUnit (GlobalTheory.NL.tS P s) ∧ (∀ (a : ℤ) (b : P.R.BdR), GlobalTheory.NL.tS P s * b ∈ (P.PD K).Fil (a + OfNat.ofNat 1) ↔ b ∈ (P.PD K).Fil a) ∧ ∀ (b : P.R.BdR), (∀ (a : ℤ), b ∈ (P.PD K).Fil a) → b = OfNat.ofNat 0 := by
  intro l _ P AI T K LL s ι
  have h1 := (P.PD K).mem_filtration_one
  have h2 := (P.PD K).not_mem_filtration_two
  rw [P.PD_ι, P.period_datum_t_eq] at h1 h2
  exact Bridge.TateSpanAlt.reduction' l P AI T K LL s ι h1 h2

end

noncomputable section

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.NL.EvdR

section General

variable {L A : Type*} [Field L] [CommRing A] (c : L →+* A) (t : A)

def part (M : ℕ) (f : PowerSeries L) : A := Polynomial.eval₂RingHom c t (PowerSeries.trunc M f)

theorem dvd_part_sub (M : ℕ) (f : PowerSeries L) (q : Polynomial L)
    (h : ∀ k < M, PowerSeries.coeff k f = q.coeff k) :
    t ^ M ∣ part c t M f - Polynomial.eval₂RingHom c t q := by
  have h1 : Polynomial.X ^ M ∣ PowerSeries.trunc M f - q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hk, h k hk, sub_self]
  have h2 := map_dvd (Polynomial.eval₂RingHom c t) h1
  rw [map_sub, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at h2
  exact h2

theorem mem_iff (n : ℕ) (x : A) : x ∈ (Ideal.span {t} ^ n • ⊤ : Submodule A A) ↔ t ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

variable [IsAdicComplete (Ideal.span {t}) A]

theorem eq_zero_of_dvd (x : A) (h : ∀ n, t ^ n ∣ x) : x = 0 :=
  IsHausdorff.haus (I := Ideal.span {t}) inferInstance x fun n => by
    rw [SModEq.zero, mem_iff]; exact h n

theorem exists_lim (f : PowerSeries L) : ∃ x : A, ∀ M, t ^ M ∣ x - part c t M f := by
  obtain ⟨x, hx⟩ := IsPrecomplete.prec (I := Ideal.span {t}) inferInstance
    (f := fun M => part c t M f) fun {m n} h => by
      rw [SModEq.sub_mem, mem_iff]
      exact dvd_part_sub c t m f _ fun k hk => by
        rw [PowerSeries.coeff_trunc, if_pos (hk.trans_le h)]
  exact ⟨x, fun M => by rw [← mem_iff, ← SModEq.sub_mem]; exact (hx M).symm⟩

theorem exists_ev : ∃ ev : PowerSeries L →+* A, ∀ f M, t ^ M ∣ ev f - part c t M f := by
  choose e he using exists_lim c t
  have key : ∀ f x, (∀ M, t ^ M ∣ x - part c t M f) → e f = x := fun f x h => by
    refine sub_eq_zero.1 (eq_zero_of_dvd t _ fun n => ?_)
    have := dvd_sub (he f n) (h n)
    rwa [sub_sub_sub_cancel_right] at this
  refine ⟨⟨⟨⟨e, key _ _ fun M => ?_⟩, fun f g => key _ _ fun M => ?_⟩, key _ _ fun M => ?_,
    fun f g => key _ _ fun M => ?_⟩, he⟩
  · have := dvd_part_sub c t M 1 1 fun k _ => by
      rw [PowerSeries.coeff_one, Polynomial.coeff_one]
    rw [map_one] at this
    exact dvd_sub_comm.1 this
  · have h := dvd_part_sub c t M (f * g) (PowerSeries.trunc M f * PowerSeries.trunc M g) fun k hk => by
      rw [PowerSeries.coeff_mul, Polynomial.coeff_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos (by omega), if_pos (by omega)]
    rw [map_mul] at h
    have h' := dvd_sub (dvd_add ((he f M).mul_right (e g)) ((he g M).mul_left (part c t M f))) h
    convert h' using 1
    simp only [part]
    ring
  · simp [part]
  · have h' := dvd_add (he f M) (he g M)
    convert h' using 1
    simp only [part, map_add]
    ring

end General

theorem exists_ev_tied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K LL : FinExt l) (s : ℕ) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) :
    ∃ ev : PowerSeries ↥LL.1 →+* P.R.BdR,
      (∀ (f : PowerSeries ↥LL.1) (M : ℕ),
        ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * tS P s ^ k ∈ (P.PD K).Fil (M : ℤ)) ∧
      (∀ (f : PowerSeries ↥LL.1) (M : ℕ), ev f ∈ (P.PD K).Fil (M : ℤ) ↔ PowerSeries.X ^ M ∣ f) ∧
      IsUnit (tS P s) ∧
      (∀ (a : ℤ) (b : P.R.BdR), tS P s * b ∈ (P.PD K).Fil (a + 1) ↔ b ∈ (P.PD K).Fil a) ∧
      ∀ b : P.R.BdR, (∀ a : ℤ, b ∈ (P.PD K).Fil a) → b = 0 := by
  first | exact Bridge.exists_power_series_evaluation | exact Bridge.exists_power_series_evaluation .. | (intros; apply Bridge.exists_power_series_evaluation <;> assumption)

theorem exists_ev_dR : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (s : ℕ) (ι : ↥LL.1 →ₐ[ℚ_[l]] (D.loc l).R.BdR), ∃ ev : PowerSeries ↥LL.1 →+* (D.loc l).R.BdR, (∀ (f : PowerSeries ↥LL.1) (M : ℕ), ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * tS (D.loc l) s ^ k ∈ ((D.loc l).PD K).Fil (M : ℤ)) ∧ (∀ (f : PowerSeries ↥LL.1) (M : ℕ), ev f ∈ ((D.loc l).PD K).Fil (M : ℤ) ↔ PowerSeries.X ^ M ∣ f) ∧ IsUnit (tS (D.loc l) s) ∧ (∀ (a : ℤ) (b : (D.loc l).R.BdR), tS (D.loc l) s * b ∈ ((D.loc l).PD K).Fil (a + 1) ↔ b ∈ ((D.loc l).PD K).Fil a) ∧ ∀ b : (D.loc l).R.BdR, (∀ a : ℤ, b ∈ ((D.loc l).PD K).Fil a) → b = 0 :=
  fun D l _ K LL s ι => exists_ev_tied l _ _ (D.locT l) K LL s ι

end GlobalTheory.NL.EvdR
end
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

noncomputable section

namespace GlobalTheory.NL.FullLevel

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_eq_zero (e : PowerSeries L) (f : ℤ → M) (w : ℕ) (h0 : ∀ k : ℤ, k < -(w : ℤ) → f k = 0)
    (k : ℤ) (hk : k < -(w : ℤ)) : conv e f k = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun j => by rw [h0 _ (by omega), smul_zero]

theorem conv_apply (e : PowerSeries L) (f : ℤ → M) (w : ℕ) (h0 : ∀ k : ℤ, k < -(w : ℤ) → f k = 0)
    (n : ℕ) : conv e f ((n : ℤ) - w) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 e • f ((p.2 : ℤ) - w) := by
  rw [conv, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1)),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun p q : ℕ => PowerSeries.coeff p e • f ((q : ℤ) - w))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    congr 2
    omega
  · intro j hj
    by_contra hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    exact hj (by simp only []; rw [h0 _ (by omega), smul_zero])

theorem full_of_det {ι : Type} (D : Submodule L M) {r : ℕ} (d : Module.Basis (Fin r) L D)
    (ex : ι → ℤ → M) (x : Fin r → ι) (w : ℕ) (U : Matrix (Fin r) (Fin r) (PowerSeries L))
    (h0 : ∀ j (k : ℤ), k < -(w : ℤ) → ex (x j) k = 0)
    (hU : ∀ j (n : ℕ), ex (x j) ((n : ℤ) - w) = ∑ a, PowerSeries.coeff n (U a j) • (d a : M))
    (hdet : U.det ≠ 0) : Full D (latSpan ex) := by
  refine ⟨U.det.order.toNat, fun f hf hf0 => ?_⟩
  obtain ⟨u, hu⟩ := (PowerSeries.isUnit_divided_by_X_pow_order hdet).exists_right_inv
  let F : Fin r → PowerSeries L := fun a => PowerSeries.mk fun n => d.repr ⟨f ((n : ℤ) - w), hf _⟩ a
  have hF : ∀ a, U.det ∣ F a := by
    intro a
    have h1 : U.det ∣ PowerSeries.X ^ U.det.order.toNat :=
      ⟨u, by
        conv_rhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := U.det)]
        rw [mul_assoc, hu, mul_one]⟩
    refine h1.trans (PowerSeries.X_pow_dvd_iff.2 fun n hn => ?_)
    have : (⟨f ((n : ℤ) - w), hf _⟩ : D) = 0 := Subtype.ext (hf0 _ (by omega))
    simp [F, this]
  choose F' hF' using hF
  let e : Fin r → PowerSeries L := U.adjugate.mulVec F'
  have he : U.mulVec e = F := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    funext a
    simp [hF']
  have hsum : f = ∑ j, conv (e j) (ex (x j)) := by
    funext k
    rw [Finset.sum_apply]
    rcases lt_or_ge k (-(w : ℤ)) with hk | hk
    · rw [hf0 k (by omega), Finset.sum_eq_zero fun j _ => conv_eq_zero _ _ w (h0 j) k hk]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) - w := ⟨(k + w).toNat, by omega⟩
      have h1 : f ((n : ℤ) - w) = ∑ a, PowerSeries.coeff n (F a) • (d a : M) := by
        have := congrArg Subtype.val (d.sum_repr ⟨f ((n : ℤ) - w), hf _⟩)
        simpa only [F, PowerSeries.coeff_mk, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul] using this.symm
      rw [h1, ← he]
      simp only [conv_apply _ _ w (h0 _), hU, Matrix.mulVec, dotProduct, map_sum, Finset.sum_smul,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm, PowerSeries.coeff_mul, Finset.sum_smul]
  rw [hsum]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨e j, x j, rfl⟩

theorem exists_coord (D : Submodule L M) {r : ℕ} (d : Module.Basis (Fin r) L D) (f : ℤ → M)
    (hf : ∀ k, f k ∈ D) (w : ℕ) : ∃ g : Fin r → PowerSeries L,
      ∀ n : ℕ, f ((n : ℤ) - w) = ∑ a, PowerSeries.coeff n (g a) • (d a : M) := by
  refine ⟨fun a => PowerSeries.mk fun n => d.repr ⟨f ((n : ℤ) - w), hf _⟩ a, fun n => ?_⟩
  have := congrArg Subtype.val (d.sum_repr ⟨f ((n : ℤ) - w), hf _⟩)
  simpa only [PowerSeries.coeff_mk, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul] using this.symm

end Series

theorem exists_det_ne_zero {R ι : Type} [CommRing R] [Nontrivial R] {r : ℕ} (g : ι → Fin r → R)
    (hg : Submodule.span R (Set.range g) = ⊤) : ∃ x : Fin r → ι, (Matrix.of fun j => g (x j)).det ≠ 0 := by
  by_contra h
  push Not at h
  have h1 : (Matrix.detRowAlternating (n := Fin r) (R := R)).toMultilinearMap = 0 :=
    MultilinearMap.ext_of_span_eq_top (g := fun _ => g) (fun _ => hg) fun x => h x
  have h2 := congrArg (fun f => f (1 : Matrix (Fin r) (Fin r) R)) h1
  exact one_ne_zero ((Matrix.det_one (n := Fin r) (R := R)).symm.trans h2)

theorem eq_sum_ev {L R : Type} [Field L] [CommRing R] (Fil : ℤ → AddSubgroup R) (hanti : Antitone Fil)
    (hmul : ∀ a b x y, x ∈ Fil a → y ∈ Fil b → x * y ∈ Fil (a + b)) (hexh : ∀ x, ∃ a, x ∈ Fil a)
    (hsep : ∀ x, (∀ a, x ∈ Fil a) → x = 0) (ι : L → R) (t : R) (ev : PowerSeries L → R)
    (hev : ∀ (f : PowerSeries L) (M : ℕ),
      ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * t ^ k ∈ Fil (M : ℤ))
    {r : ℕ} (P : Fin r → R) (g : Fin r → PowerSeries L) (y : R) (c : ℤ)
    (hy : ∀ M : ℕ, y - ∑ k ∈ Finset.range M, t ^ k * ∑ a, ι (PowerSeries.coeff k (g a)) * P a ∈
      Fil ((M : ℤ) - c)) : y = ∑ a, ev (g a) * P a := by
  choose β hβ using hexh
  obtain ⟨b, hb⟩ := (Set.finite_range fun a => β (P a)).bddBelow
  rw [← sub_eq_zero]
  refine hsep _ fun n => ?_
  obtain ⟨M, h1, h2⟩ : ∃ M : ℕ, n ≤ (M : ℤ) - c ∧ n ≤ (M : ℤ) + b :=
    ⟨(n + c).toNat + (n - b).toNat, by omega, by omega⟩
  have e : y - ∑ a, ev (g a) * P a =
      (y - ∑ k ∈ Finset.range M, t ^ k * ∑ a, ι (PowerSeries.coeff k (g a)) * P a) -
        ∑ a, (ev (g a) - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k (g a)) * t ^ k) * P a := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (s := Finset.range M)]
    simp only [mul_comm, mul_left_comm]
    ring
  rw [e]
  refine sub_mem (hanti h1 (hy M)) (sum_mem fun a _ => hanti h2 ?_)
  exact hmul _ _ _ _ (hev _ M) (hanti (hb ⟨a, rfl⟩) (hβ _))

section Comp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR)

def form (φ : T.V →ₗ[LL] LL) : T.V ⊗[Qp] BdR →ₗ[Qp] BdR :=
  TensorProduct.lift ((LinearMap.mul Qp BdR) ∘ₗ ι.toLinearMap ∘ₗ φ.restrictScalars Qp)

theorem form_tmul (φ : T.V →ₗ[LL] LL) (x : T.V) (b : BdR) : form T ι φ (x ⊗ₜ b) = ι (φ x) * b := by
  simp [form]

theorem form_mul (φ : T.V →ₗ[LL] LL) (b : BdR) (y : T.V ⊗[Qp] BdR) :
    form T ι φ (mulVR T b y) = b * form T ι φ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul x c => simp [mulVR, form_tmul, mul_left_comm]

theorem form_smul (φ : T.V →ₗ[LL] LL) (c : LL) (y : T.V ⊗[Qp] BdR) :
    form T ι φ (c • y) = ι c * form T ι φ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy, mul_add]
  | tmul x b => rw [smul_tmul', form_tmul, form_tmul, map_smul, smul_eq_mul, map_mul, mul_assoc]

theorem form_ker (φ : T.V →ₗ[LL] LL) {y : T.V ⊗[Qp] BdR} (hy : y ∈ compKer T ι) : form T ι φ y = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, y, rfl⟩ := hz
    rw [map_sub, form_smul, form_mul, sub_self]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [form_smul, hx, mul_zero]

theorem form_fil (hι : ∀ c, ι c ∈ PD.Fil 0) (φ : T.V →ₗ[LL] LL) (n : ℤ) {y : T.V ⊗[Qp] BdR}
    (hy : y ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) n) : form T ι φ y ∈ PD.Fil n := by
  obtain ⟨y', hy', _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
  clear hy
  rw [map_add, form_ker T ι φ hy', zero_add]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add]; exact add_mem ha hb
  | tmul x b =>
    have := PD.Fil_mul _ _ _ _ (hι (φ x)) b.2
    rw [zero_add] at this
    simpa [form_tmul] using this

theorem full_of_span {X : Type} (D : Submodule LL (T.V ⊗[Qp] B)) [Module.Finite LL D]
    (hD : Module.finrank LL D = Module.finrank LL T.V) (ex : X → ℤ → T.V ⊗[Qp] B)
    (hmem : ∀ x k, ex x k ∈ D) (hsupp : ∀ x, ∃ m : ℤ, ∀ k < m, ex x k = 0)
    (t : BdR) (ht : IsUnit t) (ev : PowerSeries LL →+* BdR)
    (hev : ∀ (f : PowerSeries LL) (M : ℕ),
      ev f - ∑ k ∈ Finset.range M, ι (PowerSeries.coeff k f) * t ^ k ∈ PD.Fil (M : ℤ))
    (Ψ : X → T.V ⊗[Qp] BdR)
    (hspan : ∀ z ∈ FilV PD (LL := LL) (V := T.V) 0, ∃ (m : ℕ) (b : Fin m → BdR) (x : Fin m → X),
      z - ∑ j, mulVR T (b j) (Ψ (x j)) ∈ compKer T ι)
    (hΨ : ∀ (x : X) (a : ℕ), (∀ r : ℤ, r < -(a : ℤ) → ex x r = 0) → ∃ c : ℤ, ∀ M : ℕ,
      mulVR T (t ^ a) (Ψ x) - ∑ r ∈ Finset.range M, mulVR T (t ^ r)
        (ιV PD (LL := LL) (V := T.V) (ex x ((r : ℤ) - (a : ℤ)))) ∈
        compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c)) :
    Full D (latSpan ex) := by
  have : Nontrivial BdR := ⟨⟨PD.ι PD.t, 0, fun h => PD.not_mem_filtration_two (h ▸ zero_mem _)⟩⟩
  have hι : ∀ c, ι c ∈ PD.Fil 0 := by
    intro c
    have h0 := hev (PowerSeries.C c) 0
    have h1 := PD.Fil_anti 0 (hev (PowerSeries.C c) 1)
    have := sub_mem h0 h1
    simpa using this
  set r := Module.finrank LL T.V
  let v : Module.Basis (Fin r) LL T.V := Module.finBasis LL T.V
  let d : Module.Basis (Fin r) LL D := Module.finBasisOfFinrankEq LL D hD
  let g : X → Fin r → BdR := fun x a => form T ι (v.coord a) (Ψ x)
  have hg : Submodule.span BdR (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun BdR (Fin r)).span_eq, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨m, b, x, hx⟩ := hspan (v a ⊗ₜ 1) ⟨v a ⊗ₜ ⟨1, PD.one_mem⟩, by simp⟩
    have : Pi.basisFun BdR (Fin r) a = ∑ j, b j • g (x j) := by
      funext a'
      have := form_ker T ι (v.coord a') hx
      rw [map_sub, sub_eq_zero, map_sum, form_tmul] at this
      simp only [form_mul] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, g, ← this]
      by_cases h : a' = a
      · subst h; simp
      · simp [h]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x j, rfl⟩)
  obtain ⟨x, hx⟩ := exists_det_ne_zero g hg
  choose m hm using hsupp
  obtain ⟨m₀, hm₀⟩ := (Set.finite_range fun j => m (x j)).bddBelow
  let w : ℕ := (-m₀).toNat
  have h0 : ∀ j (k : ℤ), k < -(w : ℤ) → ex (x j) k = 0 := fun j k hk =>
    hm _ _ (lt_of_lt_of_le (by omega) (hm₀ ⟨j, rfl⟩))
  choose U hU using fun j => exists_coord D d (ex (x j)) (hmem _) w
  refine full_of_det D d ex x w (Matrix.of U).transpose h0 hU fun hdet => hx ?_
  let P : Matrix (Fin r) (Fin r) BdR := Matrix.of fun a a' =>
    form T ι (v.coord a') (ιV PD (LL := LL) (V := T.V) (d a))
  have key : (t ^ w) • (Matrix.of fun j => g (x j)) = ev.mapMatrix (Matrix.of U) * P := by
    ext j a'
    obtain ⟨c, hc⟩ := hΨ (x j) w (h0 j)
    refine eq_sum_ev (fun n => (PD.Fil n).toAddSubgroup)
      (fun m n h => antitone_int_of_succ_le PD.Fil_anti h) PD.Fil_mul PD.Fil_exh PD.Fil_sep ι t ev hev
      (fun a => P a a') (U j) _ c fun M => ?_
    have := form_fil PD T ι hι (v.coord a') _ (hc M)
    simp only [map_sub, map_sum, form_mul, hU, map_smul, form_smul] at this
    simp only [Finset.mul_sum, mul_left_comm (t ^ _)]
    exact this
  have := congrArg Matrix.det key
  rw [Matrix.det_transpose] at hdet
  rw [Matrix.det_smul, Matrix.det_mul, ← RingHom.map_det, hdet, map_zero, zero_mul] at this
  exact ((ht.pow w).pow _).mul_right_eq_zero.1 this

end Comp

set_option maxHeartbeats 1600000 in

theorem full_lat : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → Full (Di (HW l) h T i) (Lat C h T i ζ) := by
  intro D HW F Cm l _ K s LL h W E C T hT i ζ hζ
  obtain ⟨h1, h2, -, -, hc⟩ := Points.points D HW l K s LL h
  obtain ⟨τ, hτ⟩ := h1 i ζ hζ
  obtain ⟨-, -, ι, hι⟩ := h2 i ζ τ hτ
  obtain ⟨Ψ, -, hspan, hΨ⟩ := GlobalTheory.T.wach_image_deRham_plus_component_level D HW F Cm l K s LL h T hT i ζ τ ι hι
  obtain ⟨ev, hev, -, ht, -⟩ := EvdR.exists_ev_dR D l K LL s ι
  have := GlobalTheory.Per.LetterDim.finite_Dcris ((D.loc l).PD K) T.ρ hT
  have : Module.Finite ↥LL.1 ↥(Di (HW l) h T i) :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : Di (HW l) h T i ≤ Dcris _ T.ρ))
      (Submodule.inclusion_injective _)
  refine full_of_span ((D.loc l).PD K) T ι (Di (HW l) h T i)
    ((GlobalTheory.Per.LetterDim.tied_letter_component_finrank l _ _ (D.locT l) K LL T.V T.ρ).1 hc hT _)
    (ex C h T i ζ) (fun x k => (C.C K s LL h).tie.levB_mem T i ζ x k)
    (fun x => (C.C K s LL h).tie.levB_supp T i ζ x) (tS (D.loc l) s) ht ev hev Ψ (fun z hz => ?_) hΨ
  obtain ⟨m, b, x, -, hx⟩ := hspan z hz
  exact ⟨m, b, x, hx⟩

end GlobalTheory.NL.FullLevel
end
end
