import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSeedDiscNormBounds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionPrincipalPerfect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisDiscRingHomExtOfAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadius

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisDisc

section General

variable {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0}

theorem norm_add_le_max_disc (x y : Disc l u ρ) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y : Disc l u ρ => ‖x + y‖ ≤ max ‖x‖ ‖y‖) ?_ ?_ x y
  · exact isClosed_le (continuous_norm.comp (continuous_fst.add continuous_snd))
      ((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd))
  · intro a b
    rw [← map_add, norm_ofPre, norm_ofPre, norm_ofPre]
    exact gauge_add_le_max l u ρ a b

def unitBall (l : ℕ) (u : A) (ρ : ℝ≥0) : Subring (Disc l u ρ) where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by
    show ‖(1 : Disc l u ρ)‖ ≤ 1
    simpa using norm_toDisc_le (l := l) (u := u) (ρ := ρ) (1 : A)
  add_mem' {x y} hx hy := (norm_add_le_max_disc x y).trans (max_le hx hy)
  mul_mem' {x y} hx hy := (norm_mul_le x y).trans (mul_le_one₀ hx (norm_nonneg _) hy)
  neg_mem' {x} hx := by simpa using hx

end General

section Complete

variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0}

theorem norm_lpow_mul (hL : ∀ y : Disc l u ρ, ‖(l : Disc l u ρ) * y‖ = (l : ℝ)⁻¹ * ‖y‖) (n : ℕ)
    (y : Disc l u ρ) : ‖(l : Disc l u ρ) ^ n * y‖ = (l : ℝ)⁻¹ ^ n * ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, hL, ih, pow_succ']; ring

theorem inv_l_lt_one : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)

namespace UnitBall
open Filter Topology

theorem norm_le_one_of_mem (x : unitBall l u ρ) : ‖(x : Disc l u ρ)‖ ≤ 1 := x.2

theorem norm_pow_mul (hmul : ∀ y : Disc l u ρ, ‖(l : Disc l u ρ) * y‖ = (l : ℝ)⁻¹ * ‖y‖) (n : ℕ)
    (y : Disc l u ρ) : ‖(l : Disc l u ρ) ^ n * y‖ = ((l : ℝ)⁻¹) ^ n * ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, hmul, ih, pow_succ']; ring

theorem mem_smul_top_iff (n : ℕ) (x : unitBall l u ρ) :
    x ∈ (Ideal.span {((l : ℕ) : unitBall l u ρ)}) ^ n • (⊤ : Submodule (unitBall l u ρ) (unitBall l u ρ)) ↔
      ∃ a : unitBall l u ρ, a * ((l : ℕ) : unitBall l u ρ) ^ n = x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']

theorem inv_pow_pos (n : ℕ) : (0 : ℝ) < ((l : ℝ)⁻¹) ^ n := by
  have : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  positivity

theorem norm_le_of_mem (hmul : ∀ y : Disc l u ρ, ‖(l : Disc l u ρ) * y‖ = (l : ℝ)⁻¹ * ‖y‖) (n : ℕ)
    (x : unitBall l u ρ)
    (hx : x ∈ (Ideal.span {((l : ℕ) : unitBall l u ρ)}) ^ n • (⊤ : Submodule (unitBall l u ρ) (unitBall l u ρ))) :
    ‖(x : Disc l u ρ)‖ ≤ ((l : ℝ)⁻¹) ^ n := by
  obtain ⟨a, rfl⟩ := (mem_smul_top_iff n x).1 hx
  have e : ((a * ((l : ℕ) : unitBall l u ρ) ^ n : unitBall l u ρ) : Disc l u ρ) =
      (l : Disc l u ρ) ^ n * (a : Disc l u ρ) := by
    push_cast; ring
  rw [e, norm_pow_mul hmul]
  calc ((l : ℝ)⁻¹) ^ n * ‖(a : Disc l u ρ)‖ ≤ ((l : ℝ)⁻¹) ^ n * 1 :=
        mul_le_mul_of_nonneg_left (norm_le_one_of_mem a) (inv_pow_pos n).le
    _ = _ := mul_one _

theorem tendsto_inv_pow : Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ n) atTop (𝓝 0) := by
  have h1 : (1 : ℝ) < l := Nat.one_lt_cast.2 hl.out.one_lt
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (by linarith)) (inv_lt_one_of_one_lt₀ h1)

theorem isAdicComplete_unitBall (hmul : ∀ y : Disc l u ρ, ‖(l : Disc l u ρ) * y‖ = (l : ℝ)⁻¹ * ‖y‖) :
    IsAdicComplete (Ideal.span {((l : ℕ) : unitBall l u ρ)}) (unitBall l u ρ) := by
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hb : ∀ n : ℕ, ‖(x : Disc l u ρ)‖ ≤ ((l : ℝ)⁻¹) ^ n := fun n =>
      norm_le_of_mem hmul n x (by simpa [SModEq.sub_mem] using hx n)
    have h0 : ‖(x : Disc l u ρ)‖ ≤ 0 := ge_of_tendsto' tendsto_inv_pow hb
    exact Subtype.ext (by simpa using norm_le_zero_iff.1 h0)
  · intro f hf

    have hd : ∀ m n, m ≤ n → ‖((f m : Disc l u ρ) - f n)‖ ≤ ((l : ℝ)⁻¹) ^ m := fun m n hmn => by
      have := norm_le_of_mem hmul m (f m - f n) (SModEq.sub_mem.1 (hf hmn))
      simpa using this
    have hc : CauchySeq (fun n => (f n : Disc l u ρ)) := by
      refine cauchySeq_of_le_tendsto_0 (fun N => 2 * ((l : ℝ)⁻¹) ^ N) (fun n m N hn hm => ?_) ?_
      · rw [dist_eq_norm]
        have e : (f n : Disc l u ρ) - f m = ((f N : Disc l u ρ) - f m) - ((f N : Disc l u ρ) - f n) := by ring
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        linarith [hd N m hm, hd N n hn]
      · simpa using tendsto_inv_pow.const_mul (2 : ℝ)
    obtain ⟨L₀, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L₀‖ ≤ 1 :=
      (isClosed_le continuous_norm continuous_const).mem_of_tendsto hL
        (Eventually.of_forall fun n => norm_le_one_of_mem (f n))
    let L : unitBall l u ρ := ⟨L₀, hL1⟩
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_smul_top_iff]
    have hn : ‖(f n : Disc l u ρ) - L₀‖ ≤ ((l : ℝ)⁻¹) ^ n := by
      have ht : Tendsto (fun k => (f n : Disc l u ρ) - f k) atTop (𝓝 ((f n : Disc l u ρ) - L₀)) :=
        tendsto_const_nhds.sub hL
      exact (isClosed_le continuous_norm continuous_const).mem_of_tendsto ht
        (eventually_atTop.2 ⟨n, fun k hk => hd n k hk⟩)
    let v : (Disc l u ρ)ˣ := (isUnit_l_disc l u ρ).unit
    have hv : (v : Disc l u ρ) = (l : Disc l u ρ) := (isUnit_l_disc l u ρ).unit_spec
    set y : Disc l u ρ := ((v⁻¹ ^ n : (Disc l u ρ)ˣ) : Disc l u ρ) * ((f n : Disc l u ρ) - L₀) with hy
    have hly : (l : Disc l u ρ) ^ n * y = (f n : Disc l u ρ) - L₀ := by
      rw [hy, ← mul_assoc, ← hv, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel,
        one_pow, Units.val_one, one_mul]
    have hy1 : ‖y‖ ≤ 1 := by
      have h2 : ((l : ℝ)⁻¹) ^ n * ‖y‖ ≤ ((l : ℝ)⁻¹) ^ n * 1 := by
        rw [← norm_pow_mul hmul, hly, mul_one]; exact hn
      exact le_of_mul_le_mul_left h2 (inv_pow_pos n)
    refine ⟨⟨y, hy1⟩, Subtype.ext ?_⟩
    push_cast
    rw [mul_comm]
    exact hly

end UnitBall

theorem isAdicComplete_unitBall (hL : ∀ y : Disc l u ρ, ‖(l : Disc l u ρ) * y‖ = (l : ℝ)⁻¹ * ‖y‖) :
    IsAdicComplete (Ideal.span {(l : unitBall l u ρ)}) (unitBall l u ρ) :=
  UnitBall.isAdicComplete_unitBall hL

end Complete

section Main

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

def locMap : Per.AinfP l →+* bk.DA bk.ρ₀ :=
  IsLocalization.Away.lift (l : Ainf l) (g := bk.iA) (by rw [map_natCast]; exact isUnit_l_disc _ _ _)

theorem locMap_alg (a : Ainf l) : locMap bk (algebraMap (Ainf l) (Per.AinfP l) a) = bk.iA a :=
  IsLocalization.Away.lift_eq _ _ a

variable {bk}

theorem le_norm_mul_coprime (hL : ∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖)
    {m : ℕ} (hm : ¬ l ∣ m) (w : bk.DA bk.ρ₀) : ‖w‖ ≤ ‖(m : bk.DA bk.ρ₀) * w‖ := by
  have hcop : IsCoprime (m : ℤ) (l : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm).symm
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : ((a : ℤ) : bk.DA bk.ρ₀) * m + (b : bk.DA bk.ρ₀) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → bk.DA bk.ρ₀) hab
  have hn : ∀ c : ℤ, ‖(c : bk.DA bk.ρ₀)‖ ≤ 1 := fun c => by
    simpa using norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (c : Ainf l)
  have e : w = (a : bk.DA bk.ρ₀) * ((m : bk.DA bk.ρ₀) * w) + (b : bk.DA bk.ρ₀) * ((l : bk.DA bk.ρ₀) * w) := by
    linear_combination (-w) * h1
  have h2 : ‖w‖ ≤ max ‖(m : bk.DA bk.ρ₀) * w‖ ((l : ℝ)⁻¹ * ‖w‖) := by
    conv_lhs => rw [e]
    refine (norm_add_le_max_disc _ _).trans (max_le_max ?_ ?_)
    · exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hn a))
    · rw [← hL]; exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hn b))
  rcases le_max_iff.1 h2 with h | h
  · exact h
  · have : ‖w‖ ≤ 0 := by nlinarith [inv_l_lt_one (l := l), norm_nonneg w]
    exact this.trans (norm_nonneg _)

theorem norm_locMap_gen (hL : ∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖)
    (hθ : ∀ a : Ainf l, Per.θ l a = 0 → ‖bk.iA a‖ ≤ (l : ℝ)⁻¹)
    (y : Per.AinfP l) (x : Ainf l) (hx : Per.θ l x = 0) (n : ℕ)
    (hn : ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Ainf l) (Per.AinfP l) x ^ n) : ‖locMap bk y‖ ≤ 1 := by
  have h1 := congrArg (locMap bk) hn
  rw [map_mul, map_natCast, map_pow, locMap_alg] at h1
  have hxn' : ∀ k : ℕ, ‖bk.iA x ^ k‖ ≤ (l : ℝ)⁻¹ ^ k := by
    intro n
    induction n with
    | zero => simpa using norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (1 : Ainf l)
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih (hθ x hx) (norm_nonneg _) (by positivity))
  have hxn := hxn' n
  set v := n.factorial.factorization l
  set m := n.factorial / l ^ v
  have hfac : (n.factorial : bk.DA bk.ρ₀) = (l : bk.DA bk.ρ₀) ^ v * (m : bk.DA bk.ρ₀) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → bk.DA bk.ρ₀) (Nat.ordProj_mul_ordCompl_eq_self n.factorial l).symm
  have hm : ¬ l ∣ m := Nat.not_dvd_ordCompl hl.out (Nat.factorial_ne_zero n)
  have hv : v ≤ n := (Nat.factorization_factorial_le_div_pred hl.out n).trans (Nat.div_le_self _ _)
  rw [hfac, mul_assoc] at h1
  replace h1 := congrArg norm h1
  rw [norm_lpow_mul hL] at h1
  have h2 := le_norm_mul_coprime hL hm (locMap bk y)
  have hpos : (0 : ℝ) < (l : ℝ)⁻¹ ^ v := by
    have : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
    positivity
  have h3 : (l : ℝ)⁻¹ ^ v * ‖locMap bk y‖ ≤ (l : ℝ)⁻¹ ^ v * 1 := by
    calc (l : ℝ)⁻¹ ^ v * ‖locMap bk y‖ ≤ (l : ℝ)⁻¹ ^ v * ‖(m : bk.DA bk.ρ₀) * locMap bk y‖ :=
          mul_le_mul_of_nonneg_left h2 hpos.le
      _ = ‖bk.iA x ^ n‖ := h1
      _ ≤ (l : ℝ)⁻¹ ^ n := hxn
      _ = (l : ℝ)⁻¹ ^ v * (l : ℝ)⁻¹ ^ (n - v) := by rw [← pow_add, Nat.add_sub_cancel' hv]
      _ ≤ (l : ℝ)⁻¹ ^ v * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) inv_l_lt_one.le) hpos.le
  exact le_of_mul_le_mul_left h3 hpos

theorem norm_locMap_acris0 (hL : ∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖)
    (hθ : ∀ a : Ainf l, Per.θ l a = 0 → ‖bk.iA a‖ ≤ (l : ℝ)⁻¹)
    (y : Per.AinfP l) (hy : y ∈ Per.Acris0 l) : ‖locMap bk y‖ ≤ 1 := by
  let S : Subalgebra (Ainf l) (Per.AinfP l) :=
    { carrier := {y | ‖locMap bk y‖ ≤ 1}
      mul_mem' := fun {x y} a b => by
        change ‖locMap bk (x * y)‖ ≤ 1
        rw [map_mul]; exact (norm_mul_le _ _).trans (mul_le_one₀ a (norm_nonneg _) b)
      add_mem' := fun {x y} a b => by
        change ‖locMap bk (x + y)‖ ≤ 1
        rw [map_add]; exact (norm_add_le_max_disc _ _).trans (max_le a b)
      algebraMap_mem' := fun r => by
        change ‖locMap bk (algebraMap (Ainf l) (Per.AinfP l) r)‖ ≤ 1
        rw [locMap_alg]; exact norm_toDisc_le r }
  exact GlobalTheory.RingIface.Acris0_le_of_dividedPowers l S (fun x n y hx hn => norm_locMap_gen hL hθ y x hx n hn) hy

end Main

section Ext

theorem exists_acris_to_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ γ : Per.Acris l →+* bk.DA bk.ρ₀,
      (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) ∧ ∀ x, ‖γ x‖ ≤ 1 := by
  intro l _ K bk
  obtain ⟨-, hL, hθ⟩ := GlobalTheory.T.breuilKisin_seedDisc_norm_bounds l K bk
  let B := unitBall l (bk.ev X) bk.ρ₀
  haveI : IsAdicComplete (Ideal.span {(l : B)}) B := isAdicComplete_unitBall hL
  let f0 : Per.Acris0 l →+* B :=
    ((locMap bk).comp (Per.Acris0 l).val.toRingHom).codRestrict B
      (fun y => norm_locMap_acris0 hL hθ y y.2)
  have hbij : Function.Bijective (algebraMap B (GlobalTheory.AdicMaps.PHat l B)) := by
    have : ⇑(algebraMap B (GlobalTheory.AdicMaps.PHat l B)) = ⇑(AdicCompletion.of (Ideal.span {(l : B)}) B) := by
      funext b; rw [AdicCompletion.algebraMap_apply]; rfl
    rw [this]; exact AdicCompletion.of_bijective _ _
  let e := RingEquiv.ofBijective (algebraMap B (GlobalTheory.AdicMaps.PHat l B)) hbij
  obtain ⟨c, hc⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  let γ : Per.Acris l →+* bk.DA bk.ρ₀ :=
    B.subtype.comp (e.symm.toRingHom.comp ((GlobalTheory.AdicMaps.padicMap l f0).comp c.toRingHom))
  refine ⟨γ, fun a => ?_, fun x => (e.symm (GlobalTheory.AdicMaps.padicMap l f0 (c x))).2⟩
  have h1 : GlobalTheory.AdicMaps.padicMap l f0 (c (algebraMap (Ainf l) (Per.Acris l) a)) =
      algebraMap B (GlobalTheory.AdicMaps.PHat l B) (f0 (algebraMap (Ainf l) (Per.Acris0 l) a)) := by
    rw [GlobalTheory.RingIface.tower, hc]
    exact GlobalTheory.AdicMaps.padicMap_alg l f0 _
  show ((e.symm (GlobalTheory.AdicMaps.padicMap l f0 (c (algebraMap (Ainf l) (Per.Acris l) a))) : B) : bk.DA bk.ρ₀) = bk.iA a
  rw [h1]
  have h2 : e.symm (algebraMap B (GlobalTheory.AdicMaps.PHat l B) (f0 (algebraMap (Ainf l) (Per.Acris0 l) a))) =
      f0 (algebraMap (Ainf l) (Per.Acris0 l) a) := e.symm_apply_apply _
  rw [h2]
  exact locMap_alg bk a

end Ext

end GlobalTheory.AcrisDisc
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_acris_ring_hom_bounded : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ γ : Per.Acris l →+* bk.DA bk.ρ₀, (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) ∧ ∀ x, ‖γ x‖ ≤ 1 := by
  atlas_forward_decl GlobalTheory.AcrisDisc.exists_acris_to_disc
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisDisc

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem ev_alg (n : ℕ) (x : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
  GlobalTheory.RingIface.ev_alg l n x

theorem norm_l_le : ‖((l : ℕ) : bk.DA bk.ρ₀)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have e : ((l : ℕ) : bk.DA bk.ρ₀) = ofPre l (bk.ev X) bk.ρ₀
      (algebraMap (Ainf l) (PreDisc l (bk.ev X) bk.ρ₀) (((l : ℕ) : Ainf l) ^ 1 * (bk.ev X) ^ 0) *
        IsLocalization.Away.invSelf ((l : ℕ) : Ainf l) ^ 0) := by
    simp [map_natCast]
  rw [e, norm_ofPre]
  exact gauge_le l (bk.ev X) bk.ρ₀ (inv_pos.2 hl0) (Submodule.subset_span ⟨1, 0, 0, by
    rw [pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], rfl⟩)

theorem norm_l_pow_le (r : ℕ) : ‖((l : ℕ) : bk.DA bk.ρ₀) ^ r‖ ≤ ((l : ℝ)⁻¹) ^ r := by
  induction r with
  | zero => simpa using norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (1 : Ainf l)
  | succ r ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (norm_l_le bk) (norm_nonneg _) (by positivity))

def psi : Per.AinfP l →+* bk.DA bk.ρ₀ :=
  IsLocalization.Away.lift (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l) (g := bk.iA)
    (by rw [map_natCast]; exact isUnit_l_disc l (bk.ev X) bk.ρ₀)

theorem psi_alg_pt (a : Per.Ainf l) : psi bk (algebraMap (Per.Ainf l) (Per.AinfP l) a) = bk.iA a :=
  IsLocalization.Away.lift_eq _ _ a

theorem gamma_acris0 (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (s : Per.Acris0 l) :
    γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      psi bk (s : Per.AinfP l) := by
  set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hψa : ∀ a : Ainf l, ψ (algebraMap (Ainf l) (Per.AinfP l) a) = bk.iA a := psi_alg_pt bk
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
  have hs : s * ((l : ℕ) : Per.Acris0 l) ^ n = algebraMap (Per.Ainf l) (Per.Acris0 l) a := by
    apply Subtype.ext
    show (s : Per.AinfP l) * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a
    rw [← h, map_natCast]
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ n) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow n
  refine hu.mul_left_injective ?_
  have h1 := congrArg (fun t => γ (algebraMap (Per.Acris0 l) (Per.Acris l) t)) hs
  simp only [map_mul, map_pow, map_natCast] at h1
  have h2 := congrArg ψ h
  simp only [map_mul, map_pow, map_natCast] at h2
  rw [← GlobalTheory.RingIface.tower l a] at h1
  exact h1.trans ((hγ a).trans ((hψa a).symm.trans h2.symm))

end GlobalTheory.AcrisDisc

namespace GlobalTheory.AcrisDisc

theorem isClosed_range_E_pow {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (m : ℕ) :
    IsClosed (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hρ0 : 0 < bk.ρ₀ := NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)
  have hρ1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hl.out.one_lt)
    (neg_neg_of_pos (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hnorm := norm_E_mul_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ le_rfl hρ1
  set c : ℝ := (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree with hc_def
  have hc : 0 < c := pow_pos (by exact_mod_cast hρ0) _
  have hpow : ∀ (k : ℕ) (v : bk.DA bk.ρ₀), c ^ k * ‖v‖ ≤ ‖bk.iS bk.E ^ k * v‖ := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have e := hnorm (bk.iS bk.E ^ k * v)
      change ‖bk.iS bk.E * (bk.iS bk.E ^ k * v)‖ = c * ‖bk.iS bk.E ^ k * v‖ at e
      have e2 : bk.iS bk.E ^ (k + 1) * v = bk.iS bk.E * (bk.iS bk.E ^ k * v) := by rw [pow_succ', mul_assoc]
      rw [e2, e, pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih v) hc.le
  set f := AddMonoidHom.mulLeft (bk.iS bk.E ^ m) with hf
  have hcm : 0 < c ^ m := pow_pos hc m
  have hb : ∀ v, ‖v‖ ≤ ((Real.toNNReal (c ^ m)⁻¹ : ℝ≥0) : ℝ) * ‖f v‖ := fun v => by
    rw [Real.coe_toNNReal _ (inv_nonneg.2 hcm.le), hf, AddMonoidHom.coe_mulLeft, inv_mul_eq_div,
      le_div_iff₀ hcm, mul_comm]
    exact hpow m v
  exact (AddMonoidHomClass.antilipschitz_of_bound f hb).isClosed_range
    (AddMonoidHomClass.uniformContinuous_of_bound f ‖bk.iS bk.E ^ m‖ fun v => norm_mul_le _ _)

theorem mem_kerTheta_pow_of_mem_filtration {l : ℕ} [hl : Fact l.Prime] (C : Core l) (m N r : ℕ) (s : Per.Acris0 l) (z : Per.Acris l)
    (a : Per.Ainf l)
    (ha : Per.ev l m (((l : ℕ) : Per.BdRp l) ^ N * C.j z) =
      Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a))
    (hy : C.j (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) ∈ Per.FilP l m) :
    ((l : ℕ) : Per.AinfP l) ^ N * (s : Per.AinfP l) +
      ((l : ℕ) : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hmemF : C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) ∈ Per.FilP l m := by
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hy
  have h0 : Per.ev l m (C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z))) = 0 :=
    (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).1 hmemF
  have e : C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) =
      ((l : ℕ) : Per.BdRp l) ^ N * algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l) +
      ((l : ℕ) : Per.BdRp l) ^ r * (((l : ℕ) : Per.BdRp l) ^ N * C.j z) := by
    rw [map_mul, map_add, map_mul, map_pow, map_pow, map_natCast, C.j_cris.on0]
    ring
  rw [e, map_add, map_mul, map_mul, ha, map_pow, map_pow, map_natCast, ev_alg] at h0
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast]
  exact h0

theorem acris_dense {l : ℕ} [Fact l.Prime] (y : Per.Acris l) (r : ℕ) :
    ∃ (s : Per.Acris0 l) (z : Per.Acris l),
      y = algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨s, z, h⟩ := GlobalTheory.PerfectCompletion.dense ((l : ℕ) : Per.Acris0 l) (e y) r
  refine ⟨s, e.symm z, e.injective ?_⟩
  rw [map_add, map_mul, map_pow, map_natCast, he, e.apply_symm_apply,
    ← map_natCast (algebraMap (Per.Acris0 l) (AdicCompletion (Ideal.span {((l : ℕ) : Per.Acris0 l)}) (Per.Acris0 l)))]
  exact h

theorem approx {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (h1 : ∀ x, ‖γ x‖ ≤ 1)
    (m N r : ℕ) (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l) (w : Per.AinfP l)
    (hw : ((l : ℕ) : Per.AinfP l) ^ N * (s : Per.AinfP l) +
      ((l : ℕ) : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) a =
        algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E) ^ m * w) :
    ‖((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) -
      bk.iS bk.E ^ m * psi bk w‖ ≤ ((l : ℝ)⁻¹) ^ r * 2 := by
  set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hE : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)) = bk.iS bk.E := psi_alg_pt bk _
  have ha : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) a) = bk.iA a := psi_alg_pt bk _
  have hx := congrArg ψ hw
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, ha, map_mul, map_pow, hE] at hx
  have hdiff : ((l : ℕ) : bk.DA bk.ρ₀) ^ N *
      γ (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) - bk.iS bk.E ^ m * ψ w =
      ((l : ℕ) : bk.DA bk.ρ₀) ^ r * (γ (((l : ℕ) : Per.Acris l) ^ N * z) - bk.iA a) := by
    rw [← hx, map_add, gamma_acris0 bk γ hγ s, map_mul, map_mul, map_pow, map_pow, map_natCast]
    ring
  rw [hdiff]
  refine (norm_mul_le _ _).trans (mul_le_mul (norm_l_pow_le bk r) ?_ (norm_nonneg _) (by positivity))
  refine (norm_sub_le _ _).trans ?_
  have := norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) a
  have := h1 (((l : ℕ) : Per.Acris l) ^ N * z)
  change ‖bk.iA a‖ ≤ 1 at *
  linarith

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀),
    (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) →
    ∀ (m : ℕ) (y : Per.Acris l), C.j y ∈ Per.FilP l m → bk.iS bk.E ^ m ∣ γ y := by
  intro l hl K bk C γ hγ h1 m y hy
  have hker : Per.kerP l ^ m = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E) ^ m} := by
    rw [ker_localizedTheta_eq_span_of_dvd l (bk.ev bk.E) fun a => by
      rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton], Ideal.span_singleton_pow]
  obtain ⟨N, hN⟩ := C.j_cris.bdd m
  have hmem : ((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ y ∈ closure (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hlt : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hl.out.one_lt)
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (half_pos hε) hlt
    obtain ⟨s, z, hyz⟩ := acris_dense y r
    obtain ⟨a, ha⟩ := hN z
    have hx := mem_kerTheta_pow_of_mem_filtration C m N r s z a ha (hyz ▸ hy)
    rw [hker, Ideal.mem_span_singleton] at hx
    obtain ⟨w, hw⟩ := hx
    refine ⟨bk.iS bk.E ^ m * psi bk w, ⟨psi bk w, rfl⟩, ?_⟩
    rw [dist_eq_norm, hyz]
    have := approx bk γ hγ h1 m N r s z a w hw
    linarith
  rw [(isClosed_range_E_pow bk m).closure_eq] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ N) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow N
  rw [← hu.dvd_mul_left]
  exact ⟨v, hv.symm⟩

end GlobalTheory.AcrisDisc
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) → ∀ (m : ℕ) (y : Per.Acris l), C.j y ∈ Per.FilP l m → bk.iS bk.E ^ m ∣ γ y := by
  atlas_forward_decl GlobalTheory.AcrisDisc.main
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_disc_ringHom_ext_of_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (γ γ' : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = γ' (algebraMap (Ainf l) (Per.Acris l) a)) → (∀ x, ‖γ x‖ ≤ 1) → (∀ x, ‖γ' x‖ ≤ 1) → γ = γ' := by
  first | exact @GlobalTheory.AcrisDiscExt.acris_disc_ext | exact GlobalTheory.AcrisDiscExt.acris_disc_ext | (intros; apply GlobalTheory.AcrisDiscExt.acris_disc_ext <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.EpsilonAssociated

theorem isEps_bk {l : ℕ} [Fact l.Prime] {e : OCb l} (h : IsEps e) : GlobalTheory.BKGal.IsEps e :=
  ⟨h.1, (frobeniusEquiv (OCb l) l).symm e, frobeniusEquiv_symm_pow_p (OCb l) l e, h.2⟩

theorem mu_associated : ∀ (l : ℕ) [Fact l.Prime] (e e' : OCb l), IsEps e → IsEps e' →
    Associated (mu e) (mu e') := by
  intro l _ e e' he he'
  have h1 : mu e ∣ mu e' := GlobalTheory.MuOfEps.muOf_dvd (isEps_bk he) he'.1
  have h2 : mu e' ∣ mu e := GlobalTheory.MuOfEps.muOf_dvd (isEps_bk he') he.1
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hne : mu e ≠ 0 := GlobalTheory.MuOfEps.muOf_ne_zero (isEps_bk he)
  have hab : a * b = 1 := by
    have h3 : (a * b - 1) * mu e = 0 := by
      have : mu e = mu e * a * b := by rw [← ha]; exact hb
      linear_combination -this
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne)
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

end GlobalTheory.EpsilonAssociated
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmullerTiltMinusOne_associated : ∀ (l : ℕ) [Fact l.Prime] (e e' : OCb l), IsEps e → IsEps e' → Associated (mu e) (mu e') := by
  atlas_forward_decl GlobalTheory.EpsilonAssociated.mu_associated
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem norm_iA_mu_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (e : OCb l), IsEps e →
    ‖bk.iA (mu e)‖ ≤ (l : ℝ)⁻¹ ∧ (l = 2 → ‖bk.iA (mu e)‖ ≤ (4 : ℝ)⁻¹) := by
  intro l _ K bk e he
  have hker := (GlobalTheory.T.breuilKisin_seedDisc_norm_bounds l K bk).2.2
  have hθmu : Per.θ l (mu e) = 0 := by
    simp only [mu, map_sub, map_one]
    simp [he.1]
  refine ⟨hker _ hθmu, ?_⟩
  rintro rfl
  set δ := (frobeniusEquiv (Per.Fl 2) 2).symm e with hδ
  have hδ2 : δ ^ 2 = e := by
    rw [hδ]; exact frobenius_apply_frobeniusEquiv_symm (Per.Fl 2) 2 e
  have hu : δ.untilt ^ 2 = 1 := by
    rw [← map_pow, hδ2, he.1]
  have hu' : δ.untilt = -1 := by
    have h1 : (δ.untilt - 1) * (δ.untilt + 1) = 0 := by linear_combination hu
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) he.2
    · linear_combination h
  have hθa : Per.θ 2 (Per.tm δ + 1) = 0 := by
    simp [hu']
  have ha := hker _ hθa
  have hfac : mu e = (Per.tm δ + 1) * ((Per.tm δ + 1) - 2) := by
    simp only [mu]
    rw [← hδ2]
    show WittVector.teichmuller 2 (δ ^ 2) - 1 = _
    rw [map_pow]
    ring
  have h2 : ‖bk.iA ((Per.tm δ + 1) - 2)‖ ≤ (2 : ℝ)⁻¹ := by
    rw [map_sub]
    have hn2 : ‖bk.iA 2‖ ≤ (2 : ℝ)⁻¹ := by
      have := DiscBasic.norm_l_disc_le 2 (bk.ev X) bk.ρ₀
      rw [map_ofNat]; simpa using this
    rw [sub_eq_add_neg]
    refine (DiscBasic.norm_add_le_max_disc 2 (bk.ev X) bk.ρ₀ _ _).trans (max_le ?_ ?_)
    · simpa using ha
    · rw [norm_neg]; exact hn2
  rw [hfac, map_mul]
  refine (norm_mul_le _ _).trans ?_
  have : ((2 : ℕ) : ℝ)⁻¹ * (2 : ℝ)⁻¹ = (4 : ℝ)⁻¹ := by norm_num
  rw [← this]
  exact mul_le_mul ha h2 (norm_nonneg _) (by positivity)

end GlobalTheory.BSP.BK
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_teichmullerTiltMinusOne_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (e : OCb l), IsEps e → ‖bk.iA (mu e)‖ ≤ (l : ℝ)⁻¹ ∧ (l = 2 → ‖bk.iA (mu e)‖ ≤ (4 : ℝ)⁻¹) := by
  atlas_forward_decl GlobalTheory.BSP.BK.norm_iA_mu_le
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

open Filter Topology

namespace GlobalTheory.BSP.SeedT

section Gen

variable (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)

theorem norm_intCast_le (z : ℤ) : ‖(z : Disc l u ρ)‖ ≤ 1 := by
  have := norm_toDisc_le (l := l) (u := u) (ρ := ρ) (z : A)
  rwa [map_intCast] at this

theorem norm_natCast_le (z : ℕ) : ‖(z : Disc l u ρ)‖ ≤ 1 := by
  have := norm_toDisc_le (l := l) (u := u) (ρ := ρ) (z : A)
  rwa [map_natCast] at this

theorem norm_lpow_mul (e : ℕ) (y : Disc l u ρ) : ‖((l : Disc l u ρ)) ^ e * y‖ = ‖y‖ / (l : ℝ) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', mul_assoc, DiscBasic.norm_l_mul l u ρ, ih, pow_succ']
    field_simp

theorem norm_coprime_mul (n : ℕ) (h : Nat.Coprime l n) (x : Disc l u ρ) : ‖(n : Disc l u ρ) * x‖ = ‖x‖ := by
  haveI := DiscBasic.isUltrametricDist_disc l u ρ
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hc := congrArg (Int.cast : ℤ → Disc l u ρ) hab
  push_cast at hc
  have e : x = (a : Disc l u ρ) * ((l : Disc l u ρ) * x) + (b : Disc l u ρ) * ((n : Disc l u ρ) * x) := by
    linear_combination (-x) * hc
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  apply le_antisymm
  · exact (norm_mul_le _ _).trans (by nlinarith [norm_natCast_le l u ρ n, norm_nonneg x])
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : ‖(a : Disc l u ρ) * ((l : Disc l u ρ) * x)‖ ≤ ‖x‖ / l := by
      rw [← DiscBasic.norm_l_mul l u ρ x]
      exact (norm_mul_le _ _).trans (by nlinarith [norm_intCast_le l u ρ a, norm_nonneg ((l : Disc l u ρ) * x)])
    have h2 : ‖(b : Disc l u ρ) * ((n : Disc l u ρ) * x)‖ ≤ ‖(n : Disc l u ρ) * x‖ :=
      (norm_mul_le _ _).trans (by nlinarith [norm_intCast_le l u ρ b, norm_nonneg ((n : Disc l u ρ) * x)])
    have h3 := IsUltrametricDist.norm_add_le_max ((a : Disc l u ρ) * ((l : Disc l u ρ) * x))
      ((b : Disc l u ρ) * ((n : Disc l u ρ) * x))
    rw [← e] at h3
    have h0 := norm_nonneg ((n : Disc l u ρ) * x)
    rcases le_max_iff.1 h3 with h4 | h4
    · have : ‖x‖ ≤ ‖x‖ / l := h4.trans h1
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith
    · linarith

theorem isUnit_coprime (n : ℕ) (h : Nat.Coprime l n) : IsUnit (n : Disc l u ρ) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hc := congrArg (Int.cast : ℤ → Disc l u ρ) hab
  push_cast at hc
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hn : ‖(a : Disc l u ρ) * (l : Disc l u ρ)‖ < 1 := by
    rw [mul_comm, DiscBasic.norm_l_mul l u ρ, div_lt_one (by linarith)]
    linarith [norm_intCast_le l u ρ a]
  have hu : IsUnit ((b : Disc l u ρ) * (n : Disc l u ρ)) := by
    refine ⟨Units.oneSub _ hn, ?_⟩
    rw [Units.val_oneSub]
    linear_combination -hc
  exact isUnit_of_mul_isUnit_right hu

theorem isUnit_natCast (n : ℕ) (hn : n ≠ 0) : IsUnit (n : Disc l u ρ) := by
  obtain ⟨e, n', hd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  push_cast
  exact ((isUnit_l_disc l u ρ).pow e).mul (isUnit_coprime l u ρ n' ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hd))

theorem norm_le_natCast_mul (n : ℕ) (hn : n ≠ 0) (x : Disc l u ρ) : ‖x‖ ≤ n * ‖(n : Disc l u ρ) * x‖ := by
  obtain ⟨e, n', hd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have hn' : n' ≠ 0 := by rintro rfl; simp at hn
  have hle : (l : ℝ) ^ e ≤ ((l ^ e * n' : ℕ) : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ n' := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn'
    nlinarith [pow_pos (show (0 : ℝ) < l by exact_mod_cast hl.out.pos) e]
  have hpos : (0 : ℝ) < (l : ℝ) ^ e := pow_pos (by exact_mod_cast hl.out.pos) e
  have key : ‖((l ^ e * n' : ℕ) : Disc l u ρ) * x‖ = ‖x‖ / (l : ℝ) ^ e := by
    push_cast
    rw [mul_assoc, norm_lpow_mul, norm_coprime_mul l u ρ n' ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hd)]
  rw [key]
  calc ‖x‖ = (l : ℝ) ^ e * (‖x‖ / (l : ℝ) ^ e) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)

end Gen

end GlobalTheory.BSP.SeedT

namespace GlobalTheory.BSP.SeedT

theorem gamma_partial {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (μ : Ainf l) (n : ℕ) (s : Per.Acris0 l)
    (hs : ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) μ) ^ (k + 1)) :
    γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      ∑ k ∈ Finset.range n, (-1) ^ k * bk.iA μ ^ (k + 1) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
  set P : Ainf l := ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Ainf l) * μ ^ (k + 1) with hP
  have h1 : ((n.factorial : ℕ) : Per.Acris0 l) * s = algebraMap (Ainf l) (Per.Acris0 l) P := by
    apply Subtype.ext
    change ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) = algebraMap (Ainf l) (Per.AinfP l) P
    rw [hs, hP]
    simp [map_sum, map_mul, map_pow, map_natCast, map_neg, map_one]
  have h2 := congrArg (fun x => γ (algebraMap (Per.Acris0 l) (Per.Acris l) x)) h1
  simp only [map_mul, map_natCast] at h2
  rw [show algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Ainf l) (Per.Acris0 l) P) =
    algebraMap (Ainf l) (Per.Acris l) P from (GlobalTheory.RingIface.tower l P).symm, hγ, hP] at h2
  simp only [map_sum, map_mul, map_pow, map_natCast, map_neg, map_one] at h2
  have hu := isUnit_natCast l (bk.ev X) bk.ρ₀ n.factorial (Nat.factorial_ne_zero n)
  refine hu.mul_left_cancel (h2.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
  have hd : k + 1 ∣ n.factorial := Nat.dvd_factorial (Nat.succ_pos k) hk'
  have hv := isUnit_natCast l (bk.ev X) bk.ρ₀ (k + 1) (Nat.succ_ne_zero k)
  have hq : ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀) =
      ((n.factorial : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
    calc ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀)
        = ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀) *
            (((k + 1 : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀)) := by
          rw [Ring.mul_inverse_cancel _ hv, mul_one]
      _ = ((n.factorial / (k + 1) * (k + 1) : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
          push_cast; ring
      _ = _ := by rw [Nat.div_mul_cancel hd]
  rw [hq]
  ring

theorem t_assoc_mu : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l)
    (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) →
    (∀ x, ‖γ x‖ ≤ 1) → Associated (γ C.t) (bk.iA (mu C.ε)) := by
  intro l hl K bk C γ hγ hγn
  haveI := DiscBasic.isUltrametricDist_disc l (bk.ev X) bk.ρ₀
  set m := bk.iA (mu C.ε) with hm_def
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hm : ‖m‖ ≤ 1 / 3 := by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.norm_teichmullerTiltMinusOne_le l K bk C.ε (core_isEps l C)
    by_cases h : l = 2
    · exact (h2 h).trans (by norm_num)
    · have h3 : (3 : ℝ) ≤ l := by
        have := hl.out.two_le
        exact_mod_cast (show 3 ≤ l by omega)
      refine h1.trans ?_
      rw [one_div]
      exact inv_anti₀ (by norm_num) h3
  set f : ℕ → bk.DA bk.ρ₀ := fun k => (-m) ^ (k + 1) * Ring.inverse ((k + 2 : ℕ) : bk.DA bk.ρ₀) with hf_def
  have hf : ∀ k, ‖f k‖ ≤ (2 / 3 : ℝ) ^ (k + 1) := by
    intro k
    have hu := isUnit_natCast l (bk.ev X) bk.ρ₀ (k + 2) (by omega)
    have e : ((k + 2 : ℕ) : bk.DA bk.ρ₀) * f k = (-m) ^ (k + 1) := by
      rw [hf_def, mul_left_comm, Ring.mul_inverse_cancel _ hu, mul_one]
    have h1 := norm_le_natCast_mul l (bk.ev X) bk.ρ₀ (k + 2) (by omega) (f k)
    rw [e] at h1
    have h2 : ‖(-m) ^ (k + 1)‖ ≤ ‖m‖ ^ (k + 1) := by
      rw [← norm_neg m]; exact norm_pow_le' _ (Nat.succ_pos k)
    have h3 : ‖m‖ ^ (k + 1) ≤ (1 / 3 : ℝ) ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg _) hm _
    have h4 : ((k + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      have : k + 2 ≤ 2 ^ (k + 1) := Nat.lt_two_pow_self
      exact_mod_cast this
    calc ‖f k‖ ≤ ((k + 2 : ℕ) : ℝ) * ‖(-m) ^ (k + 1)‖ := h1
      _ ≤ (2 : ℝ) ^ (k + 1) * (1 / 3 : ℝ) ^ (k + 1) :=
          mul_le_mul h4 (h2.trans h3) (norm_nonneg _) (by positivity)
      _ = (2 / 3 : ℝ) ^ (k + 1) := by rw [← mul_pow]; norm_num
  have hsum : Summable f := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (2 / 3 : ℝ) < 1)).mul_left (2 / 3)) fun k => ?_
    rw [← pow_succ']
    exact hf k
  set y := ∑' k, f k with hy_def
  have hy : ‖y‖ ≤ 2 / 3 :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun k =>
      (hf k).trans (pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero k))
  have hunit : IsUnit (1 + y) := by
    refine ⟨Units.oneSub (-y) (by rw [norm_neg]; linarith), ?_⟩
    rw [Units.val_oneSub, sub_neg_eq_add]
  set S : ℕ → bk.DA bk.ρ₀ := fun n =>
    ∑ k ∈ Finset.range n, (-1) ^ k * m ^ (k + 1) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) with hS_def
  have hS : ∀ n, S (n + 1) = m * (1 + ∑ k ∈ Finset.range n, f k) := by
    intro n
    induction n with
    | zero => simp [hS_def]
    | succ n ih =>
      have e1 : S (n + 1 + 1) = S (n + 1) + (-1) ^ (n + 1) * m ^ (n + 1 + 1) *
          Ring.inverse ((n + 1 + 1 : ℕ) : bk.DA bk.ρ₀) := by
        simp only [hS_def]; rw [Finset.sum_range_succ]
      rw [e1, ih, Finset.sum_range_succ, hf_def]
      simp only
      rw [neg_pow]
      ring
  have hlim1 : Tendsto (fun n => S (n + 1)) atTop (𝓝 (m * (1 + y))) := by
    simp_rw [hS]
    exact (tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat).const_mul m
  have hlim2 : Tendsto (fun n => S (n + 1)) atTop (𝓝 (γ C.t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε hlinv
    obtain ⟨N, hN⟩ := C.t_log r
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨s, hs1, z, hz⟩ := hN (n + 1) (by omega)
    have key := gamma_partial bk γ hγ (mu C.ε) (n + 1) s hs1
    rw [dist_eq_norm, norm_sub_rev]
    have e2 : γ C.t - S (n + 1) = (l : bk.DA bk.ρ₀) ^ r * γ z := by
      rw [hS_def]
      simp only
      rw [← key, ← map_sub, hz, map_mul, map_pow, map_natCast]
    rw [e2, norm_lpow_mul]
    calc ‖γ z‖ / (l : ℝ) ^ r ≤ 1 / (l : ℝ) ^ r :=
          div_le_div_of_nonneg_right (hγn z) (by positivity)
      _ = (l : ℝ)⁻¹ ^ r := by rw [inv_pow, one_div]
      _ < ε := hr
  have heq : γ C.t = m * (1 + y) := tendsto_nhds_unique hlim2 hlim1
  refine ⟨hunit.unit⁻¹, ?_⟩
  rw [heq, mul_assoc, IsUnit.mul_val_inv, mul_one]

end GlobalTheory.BSP.SeedT
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_log_teichmuller_associated_sub_one_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) → Associated (γ C.t) (bk.iA (mu C.ε)) := by
  atlas_forward_decl GlobalTheory.BSP.SeedT.t_assoc_mu
end

section
attribute [local irreducible] Formalism.Per.σC Formalism.Per.σO Formalism.Per.φA Formalism.Per.zA Formalism.Per.AinfP Formalism.Per.zP Formalism.Per.toC Formalism.Per.θP Formalism.Per.kerP Formalism.Per.ev Formalism.Per.FilP Formalism.Per.θD Formalism.Per.pD Formalism.Per.zD Formalism.Per.FilD Formalism.Per.Acris0 Formalism.Per.Acris Formalism.Per.Bcris Formalism.Per.aB Formalism.Per.a0B Formalism.Per.zB Formalism.Per.φB Formalism.Per.σF Formalism.Per.σA Formalism.Per.extP Formalism.Per.σDp Formalism.Per.σD Formalism.Per.σB Formalism.Per.IsLog

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.SeedAsm

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem phiA_alg (a : Ainf l) : phiA l (algebraMap (Ainf l) (Per.Acris l) a) =
    algebraMap (Ainf l) (Per.Acris l) (WittVector.frobenius a) := by
  rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
  congr 1
  ext n
  rw [GlobalTheory.RingIface.phiA_coeff, WittVector.coeff_frobenius_charP]

theorem sigA_alg (g : Per.Gq l) (a : Ainf l) : sigA g (algebraMap (Ainf l) (Per.Acris l) a) =
    algebraMap (Ainf l) (Per.Acris l) (Per.σA g a) := by
  rw [(GlobalTheory.CrisMaps.sigA_extends g).alg]

theorem iA_injective : Function.Injective bk.iA := by
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk (Ainf l) bk.ev
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  exact (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1

theorem isDomain : IsDomain (bk.DA bk.ρ₀) := by
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk (Ainf l) bk.ev
  exact (discAinf_isDomain l K bk bk.ρ₀ h0 h1).1

variable {bk}

theorem comm_phi (γ : Per.Acris l →+* bk.DA bk.ρ₀) (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a)
    (hn : ∀ x, ‖γ x‖ ≤ 1) (Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hΦ : IsDiscMap WittVector.frobenius Φ) (x : Per.Acris l) :
    Φ (γ x) = γ (phiA l x) := by
  have h := GlobalTheory.T.acris_disc_ringHom_ext_of_ainf l K bk (Φ.comp γ) (γ.comp (phiA l)) (fun a => by
      simp only [RingHom.comp_apply, hγ, phiA_alg]
      exact hΦ.ext a) (fun x => (hΦ.norm_le _).trans (hn x)) (fun x => hn _)
  exact RingHom.congr_fun h x

theorem comm_sig (γ : Per.Acris l →+* bk.DA bk.ρ₀) (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a)
    (hn : ∀ x, ‖γ x‖ ≤ 1) (g : Per.Gq l) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hG : IsDiscMap (Per.σA g) G)
    (x : Per.Acris l) : G (γ x) = γ (sigA g x) := by
  have h := GlobalTheory.T.acris_disc_ringHom_ext_of_ainf l K bk (G.comp γ) (γ.comp (sigA g)) (fun a => by
      simp only [RingHom.comp_apply, hγ, sigA_alg]
      exact hG.ext a) (fun x => (hG.norm_le _).trans (hn x)) (fun x => hn _)
  exact RingHom.congr_fun h x

theorem acrisToDisc_image_t_eq_unit_mul_period (C : Core l) {τ : Ainf l} (hτ : bk.IsPer τ) (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (hn : ∀ x, ‖γ x‖ ≤ 1) :
    ∃ ν : (bk.DA bk.ρ₀)ˣ, γ C.t = ν * bk.iA (bk.ev bk.E * τ) := by
  obtain ⟨hE, ε, η, hε, hη⟩ := hτ
  obtain ⟨u, hu⟩ := GlobalTheory.T.acris_log_teichmuller_associated_sub_one_on_disc l K bk C γ hγ hn
  obtain ⟨v, hv⟩ := GlobalTheory.T.teichmullerTiltMinusOne_associated l ε C.ε hε (core_isEps l C)
  refine ⟨u⁻¹ * Units.map bk.iA.toMonoidHom v * (Units.map bk.iA.toMonoidHom η)⁻¹, ?_⟩
  have e1 : bk.ev bk.E * τ = η * mu ε := by rw [← hE, hη]; rfl
  have hu' : γ C.t * u = bk.iA (mu ε) * bk.iA v := by rw [hu, ← hv, map_mul]
  rw [e1, map_mul]
  simp only [Units.val_mul, Units.coe_map, Units.coe_map_inv, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  have hU : (u : bk.DA bk.ρ₀) * ((u⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀) = 1 := Units.mul_inv u
  have hH : bk.iA ((η⁻¹ : (Ainf l)ˣ) : Ainf l) * bk.iA η = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  linear_combination (-(γ C.t)) * hU + ((u⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀) * hu' -
    ((u⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀) * bk.iA v * bk.iA (mu ε) * hH

theorem map_smul_hom {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem smul_cancel {R : Type} [CommRing R] [IsDomain R] {m n : Type} {c : R} (hc : c ≠ 0)
    {M M' : Matrix m n R} (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

theorem evE_mul_ne_zero {τ : Ainf l} (hτ : bk.IsPer τ) : bk.ev bk.E * τ ≠ 0 := by
  obtain ⟨hE, ε, η, hε, hη⟩ := hτ
  rw [← hE, hη]
  intro h0
  have h1 : WittVector.teichmuller l ε - 1 = 0 := (Units.mul_right_eq_zero η).1 h0
  have h2 : ε = 1 := by
    have := congrArg (fun w => WittVector.coeff w 0) (sub_eq_zero.1 h1)
    simpa using this
  subst h2
  exact hε.2 (by simp)

end GlobalTheory.BSP.SeedAsm

open GlobalTheory.BSP.SeedAsm in

theorem GlobalTheory.BSP.seed_of_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (N c₁ c₂ c₃ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) → X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) → ∀ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), (Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), C.t ^ N • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • Z) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N))) → Nonempty (Seed bk d ρ τ) := by
  intro l _ K bk C τ hτ d ρ N c₁ c₂ c₃ F F' X X' hF hX hnp Z Z' hZ
  obtain ⟨hZZ, hφ, hg, hf1, hf2⟩ := hZ
  haveI := isDomain bk
  obtain ⟨γ, hγ, hn⟩ := GlobalTheory.T.exists_acris_ring_hom_bounded l K bk
  obtain ⟨ν, hν⟩ := acrisToDisc_image_t_eq_unit_mul_period C hτ γ hγ hn
  set a := bk.iA (bk.ev bk.E * τ) with ha_def
  have ha : a ≠ 0 := fun h => evE_mul_ne_zero hτ (iA_injective bk (h.trans (map_zero _).symm))
  set e := bk.iS bk.E with he_def
  have hae : a = e * bk.iA τ := by rw [ha_def, map_mul]; rfl
  have he : e ≠ 0 := fun h => ha (by rw [hae, h, zero_mul])
  have hγS : ∀ s : bk.S, γ (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) s) = bk.iS s := fun s => hγ _
  have hmapS : ∀ M : Matrix (Fin d) (Fin d) bk.S,
      (M.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map γ = M.map bk.iS := fun M => by
    ext i j; simp only [Matrix.map_apply]; exact hγS _
  choose w hw using fun i j => GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc l K bk C γ hγ hn (2 * N) _ (hf1 i j)
  choose w' hw' using fun i j => GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc l K bk C γ hγ hn (2 * N) _ (hf2 i j)
  set G := Z.map γ
  set G' := Z'.map γ
  set Xs := X.map bk.iS
  set X's := X'.map bk.iS
  have hW1 : G * Xs = e ^ (2 * N) • Matrix.of w := by
    ext i j
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hw i j, ← Matrix.map_apply (f := γ), Matrix.map_mul, hmapS]
  have hW1' : X's * G' = e ^ (2 * N) • Matrix.of w' := by
    ext i j
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hw' i j, ← Matrix.map_apply (f := γ), Matrix.map_mul, hmapS]
  have hXX : Xs * X's = ((l : bk.DA bk.ρ₀) ^ c₂ * e ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have := congrArg (Matrix.map · bk.iS) hX
    simp only [Matrix.map_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow, map_natCast] at this
    exact this
  have hGG : G * G' = (γ C.t) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have := congrArg (Matrix.map · γ) hZZ
    simp only [Matrix.map_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), map_pow] at this
    exact this
  obtain ⟨Lu, hLu⟩ := isUnit_l_disc l (bk.ev PowerSeries.X) bk.ρ₀
  set μ : bk.DA bk.ρ₀ := (ν : bk.DA bk.ρ₀)
  set μi : bk.DA bk.ρ₀ := ((ν⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀)
  set Li : bk.DA bk.ρ₀ := ((Lu⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀)
  have hμ : μi * μ = 1 := Units.inv_mul ν
  have hL : Li * (l : bk.DA bk.ρ₀) = 1 := by rw [← hLu]; exact Units.inv_mul Lu
  have c1 : Matrix.of w * X's = ((l : bk.DA bk.ρ₀) ^ c₂) • G := by
    apply smul_cancel (pow_ne_zero (2 * N) he)
    rw [← Matrix.smul_mul, ← hW1, Matrix.mul_assoc, hXX, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]
  have c2 : Matrix.of w * Matrix.of w' =
      ((l : bk.DA bk.ρ₀) ^ c₂ * μ ^ (2 * N) * bk.iA τ ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    apply smul_cancel (pow_ne_zero (2 * N) he)
    apply smul_cancel (pow_ne_zero (2 * N) he)
    calc e ^ (2 * N) • e ^ (2 * N) • (Matrix.of w * Matrix.of w')
        = (e ^ (2 * N) • Matrix.of w) * (e ^ (2 * N) • Matrix.of w') := by rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = G * (Xs * X's) * G' := by rw [← hW1, ← hW1', Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = ((l : bk.DA bk.ρ₀) ^ c₂ * e ^ (2 * N) * γ C.t ^ (2 * N)) • 1 := by
        rw [hXX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hGG, smul_smul]
      _ = _ := by
        rw [smul_smul, smul_smul, hν, hae]
        congr 1
        ring
  have hV : (μi ^ N • Matrix.of w) * X's = (μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂) • G := by
    rw [Matrix.smul_mul, c1, smul_smul]
  refine ⟨Seed.mk N c₁ c₂ c₃ F F' hF X X' hX (fun f g => hnp _ f g) (μi ^ N • Matrix.of w)
    ((Li ^ c₂ * μi ^ N) • Matrix.of w') ?_ ?_ ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, c2, smul_smul, smul_smul]
    congr 1
    have h1 : (μi * μ) ^ N = 1 := by rw [hμ, one_pow]
    have h2 : (Li * (l : bk.DA bk.ρ₀)) ^ c₂ = 1 := by rw [hL, one_pow]
    linear_combination (bk.iA τ ^ (2 * N)) * ((μi * μ) ^ N * (μi * μ) ^ N * h2 + (μi * μ) ^ N * h1 + h1)
  · intro Φ hΦ
    have hP : (Z.map γ).map Φ = (Z.map (phiA l)).map γ := by
      ext i j; simp only [Matrix.map_apply]; exact comm_phi γ hγ hn Φ hΦ _
    have hFm : (F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map γ =
        F.map (bk.iS.comp PowerSeries.C) := by
      ext i j; simp only [Matrix.map_apply, RingHom.comp_apply]; exact hγ _
    have htφ : γ (phiA l C.t) = Φ μ * (bk.iS (frobS l bk.a bk.E) * a) := by
      rw [← comm_phi γ hγ hn Φ hΦ, hν, map_mul]
      congr 1
      rw [ha_def, hΦ.ext, map_mul WittVector.frobenius, ← bk.ev_frob, hτ.1, map_mul bk.iA]
      rfl
    have hyp := congrArg (Matrix.map · γ) hφ
    simp only [Matrix.map_mul, map_smul_hom, map_mul, map_pow, map_natCast, hFm, hν, htφ] at hyp
    rw [hV, map_smul_hom, hP]
    ext i j
    have hij := congrFun (congrFun hyp i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.smul_mul, map_mul, map_pow, map_natCast] at hij ⊢
    apply mul_left_cancel₀ (pow_ne_zero N ha)
    have h1 : (μi * μ) ^ N = 1 := by rw [hμ, one_pow]
    have h3 : (Φ μi * Φ μ) ^ N = 1 := by rw [← map_mul, hμ, map_one, one_pow]
    rw [show Z.map γ = G from rfl] at hij
    linear_combination (μi ^ N * Φ μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂) * hij -
      (a ^ N * (l : bk.DA bk.ρ₀) ^ c₁ * Φ μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ * (Z.map (phiA l)).map γ i j) * h1 +
      (a ^ N * bk.iS (frobS l bk.a bk.E) ^ N * μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ *
        (G * F.map (bk.iS.comp PowerSeries.C)) i j) * h3
  · intro g Gm hG
    have hP : (Z.map γ).map Gm = (Z.map (sigA (g : GQ l))).map γ := by
      ext i j; simp only [Matrix.map_apply]; exact comm_sig γ hγ hn _ Gm hG _
    have hR : ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))).map γ =
        (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) := by
      ext i j; simp only [Matrix.map_apply, RingHom.comp_apply]; exact hγ _
    have hb : Gm a = bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) := by rw [ha_def]; exact hG.ext _
    have htσ : γ (sigA (g : GQ l) C.t) = Gm μ * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) := by
      rw [← comm_sig γ hγ hn _ Gm hG, hν, map_mul, hb]
    have hyp := congrArg (Matrix.map · γ) (hg g)
    simp only [Matrix.map_mul, map_smul_hom, map_mul, map_pow, hR, hν, htσ] at hyp
    rw [hV, map_smul_hom, hP]
    ext i j
    have hij := congrFun (congrFun hyp i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, map_mul, map_pow, map_natCast] at hij ⊢
    rw [show Z.map γ = G from rfl] at hij
    have h1 : (μi * μ) ^ N = 1 := by rw [hμ, one_pow]
    have h3 : (Gm μi * Gm μ) ^ N = 1 := by rw [← map_mul, hμ, map_one, one_pow]
    rw [ha_def, map_mul] at hij
    linear_combination (μi ^ N * Gm μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂) * hij -
      ((bk.iA (bk.ev bk.E) * bk.iA τ) ^ N * Gm μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ *
        ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (Z.map (sigA (g : GQ l))).map γ) i j) * h1 +
      ((bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) * bk.iA (Per.σA (g : GQ l) τ)) ^ N * μi ^ N *
        (l : bk.DA bk.ρ₀) ^ c₂ * G i j) * h3
end
end
