import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgTAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicIsogenyConstantOfIsogenyFormula
import BuildAid.ForwardExisting
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgStatus
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorStatus

section
section
noncomputable section

namespace GlobalTheory.CurveSigmaAlg

open NumberField Formalism.BasicNotions GlobalTheory.IsogConst

theorem hasCMBy_curve (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (L : PeriodPair)
    (hL : L.lattice.toAddSubgroup = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
  have hδ0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  obtain ⟨-, hCM⟩ := GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc.1 hδ0
  intro ω hω
  have h1 := hCM ω (by rw [← hL]; exact hω)
  rw [← hL] at h1
  have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
    unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
  rw [e]; exact h1

theorem secondEisensteinAlgebraic_of_invAlg : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic := by
  intro hInv D cc δ hcc hδ L hL
  obtain ⟨h2, h3⟩ := hInv D cc δ hcc hδ L hL
  have hcm := hasCMBy_curve D cc δ hcc hδ L hL
  have hd0 : 0 < D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).pos
  obtain ⟨S, -, -, hIso, -⟩ := Formalism.L2.Th1.F.hasCMByIsogeny D.host.d L hcm (-1) 2 (by simp) hd0
  have hαsq := alpha_sq D.host.d
  have hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))
  have hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0 := by
    intro h0
    rw [h0] at hαsq
    have : (D.host.d : ℂ) = 0 := by linear_combination hαsq
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have he : InQ (Formalism.L2.Th1.F.pSeries L) := by
    intro k
    rw [Formalism.L2.KerInert.AlgP.pSeries_eq_map Formalism.MainNotions.TaylorLogMetric.Qbar L h2 h3, PowerSeries.coeff_map]
    exact SetLike.coe_mem _
  have hc := algebraic_isogenyConstant_of_isogenyFormula _ he _ _ hα hα0 _ hIso
  rw [hαsq] at hc
  have hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) := by
    push_cast; ring
  rw [hN] at hc
  have hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card S + 1 + D.host.d ≠ 0)
  have e : Formalism.L2.Th1.F.s2 L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ *
      (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 L) := by
    rw [← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rw [e]
  exact mul_mem (inv_mem (natCast_mem _ _)) hc

end GlobalTheory.CurveSigmaAlg
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curveLattice_sigmaTwo_algebraic_of_invariants_algebraic : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic := by
  atlas_forward_decl GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg
end

section
open Filter Topology

namespace GlobalTheory.WittRootsOfUnity

theorem add_pow_of_cast_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (h0 : (p : A) = 0)
    (a b : A) (m : ℕ) : (a + b) ^ p ^ m = a ^ p ^ m + b ^ p ^ m := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  ·
    have : Fact p.Prime := ⟨hp⟩
    have : CharP A p := (CharP.charP_iff_prime_eq_zero hp).2 h0
    exact add_pow_char_pow ..

theorem neg_pow_of_cast_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (h0 : (p : A) = 0)
    (a : A) (m : ℕ) : (-a) ^ p ^ m = -a ^ p ^ m := by

  have h := add_pow_of_cast_eq_zero hp h0 a (-a) m
  rw [add_neg_cancel, zero_pow (pow_ne_zero _ hp.ne_zero)] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

def mu (K : Type*) [Field K] (p : ℕ) : Set K := {ζ | ∃ n, 0 < n ∧ n.Coprime p ∧ ζ ^ n = 1}

private theorem pow_pow_eq_self_of_pow_eq_self {A : Type*} [Monoid A] {q : ℕ} {a : A} (h : a ^ q = a) (k : ℕ) :
    a ^ q ^ k = a := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, h]

private theorem frobenius_periodic_add_and_mul {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (h0 : (p : A) = 0)
    {a b : A} (ha : ∃ f, 0 < f ∧ a ^ p ^ f = a) (hb : ∃ f, 0 < f ∧ b ^ p ^ f = b) :
    (∃ f, 0 < f ∧ (a + b) ^ p ^ f = a + b) ∧ (∃ f, 0 < f ∧ (a * b) ^ p ^ f = a * b) := by
  obtain ⟨f, hf, ha⟩ := ha
  obtain ⟨g, hg, hb⟩ := hb

  have ha' : a ^ p ^ (f * g) = a := by rw [pow_mul]; exact pow_pow_eq_self_of_pow_eq_self ha g
  have hb' : b ^ p ^ (f * g) = b := by rw [mul_comm, pow_mul]; exact pow_pow_eq_self_of_pow_eq_self hb f
  exact ⟨⟨f * g, Nat.mul_pos hf hg, by rw [add_pow_of_cast_eq_zero hp h0, ha', hb']⟩,
    ⟨f * g, Nat.mul_pos hf hg, by rw [mul_pow, ha', hb']⟩⟩

private theorem exists_frobenius_periodic_of_mem_mu {K : Type*} [Field K] {p : ℕ} {ζ : K} (hζ : ζ ∈ mu K p) :
    ∃ f, 0 < f ∧ ζ ^ p ^ f = ζ := by
  obtain ⟨n, hn, hcop, h1⟩ := hζ

  refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
  have hmod : p ^ n.totient % n = 1 % n := Nat.ModEq.pow_totient hcop.symm
  rw [pow_eq_pow_mod _ h1, hmod, ← pow_eq_pow_mod _ h1, pow_one]

theorem frob_periodic {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) {x : K}
    (hx : x ∈ Subring.closure (mu K p)) :
    ∃ f, 0 < f ∧ ∃ s ∈ Subring.closure (mu K p), x ^ p ^ f - x = p * s := by

  let I : Ideal (Subring.closure (mu K p)) := Ideal.span {((p : ℕ) : Subring.closure (mu K p))}
  have h0 : ((p : ℕ) : Subring.closure (mu K p) ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have key : ∀ (y : K) (hy : y ∈ Subring.closure (mu K p)),
      ∃ f, 0 < f ∧ (Ideal.Quotient.mk I ⟨y, hy⟩) ^ p ^ f = Ideal.Quotient.mk I ⟨y, hy⟩ := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
      obtain ⟨f, hf, hz'⟩ := exists_frobenius_periodic_of_mem_mu hz
      refine ⟨f, hf, ?_⟩
      rw [← map_pow]
      congr 1
      exact Subtype.ext (by simpa using hz')
    | zero =>
      refine ⟨1, one_pos, ?_⟩
      show (Ideal.Quotient.mk I 0) ^ p ^ 1 = Ideal.Quotient.mk I 0
      rw [map_zero, zero_pow (pow_ne_zero _ hp.ne_zero)]
    | one =>
      refine ⟨1, one_pos, ?_⟩
      show (Ideal.Quotient.mk I 1) ^ p ^ 1 = Ideal.Quotient.mk I 1
      rw [map_one, one_pow]
    | add z w hz hw ihz ihw =>
      obtain ⟨f, hf, h⟩ := (frobenius_periodic_add_and_mul hp h0 ihz ihw).1
      refine ⟨f, hf, ?_⟩
      show (Ideal.Quotient.mk I (⟨z, hz⟩ + ⟨w, hw⟩)) ^ p ^ f = Ideal.Quotient.mk I (⟨z, hz⟩ + ⟨w, hw⟩)
      rw [map_add]
      exact h
    | neg z hz ih =>
      obtain ⟨f, hf, h⟩ := ih
      refine ⟨f, hf, ?_⟩
      show (Ideal.Quotient.mk I (-⟨z, hz⟩)) ^ p ^ f = Ideal.Quotient.mk I (-⟨z, hz⟩)
      rw [map_neg, neg_pow_of_cast_eq_zero hp h0, h]
    | mul z w hz hw ihz ihw =>
      obtain ⟨f, hf, h⟩ := (frobenius_periodic_add_and_mul hp h0 ihz ihw).2
      refine ⟨f, hf, ?_⟩
      show (Ideal.Quotient.mk I (⟨z, hz⟩ * ⟨w, hw⟩)) ^ p ^ f = Ideal.Quotient.mk I (⟨z, hz⟩ * ⟨w, hw⟩)
      rw [map_mul]
      exact h
  obtain ⟨f, hf, h⟩ := key x hx
  rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨f, hf, c, c.2, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

section Normed

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {p : ℕ}

def W (K : Type*) [NormedField K] (p : ℕ) : Subring K :=
  (Subring.closure (mu K p)).topologicalClosure

omit [IsUltrametricDist K] in
theorem isClosed_divisorComponent : IsClosed (W K p : Set K) :=
  Subring.isClosed_topologicalClosure _

omit [IsUltrametricDist K] in
theorem mem_W_of_mem {x : K} (hx : x ∈ Subring.closure (mu K p)) : x ∈ W K p :=
  Subring.le_topologicalClosure _ hx

omit [IsUltrametricDist K] in
theorem mem_closure_roots_of_unity {x : K} (hx : x ∈ W K p) :
    x ∈ closure (Subring.closure (mu K p) : Set K) :=
  hx

theorem norm_le_one_of_mem {x : K} (hx : x ∈ Subring.closure (mu K p)) : ‖x‖ ≤ 1 := by
  induction hx using Subring.closure_induction with
  | mem z hz =>

    obtain ⟨n, hn, -, h1⟩ := hz
    have : ‖z‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 this).le
  | zero => simp
  | one => simp
  | add z w _ _ hz hw => exact (IsUltrametricDist.norm_add_le_max z w).trans (max_le hz hw)
  | neg z _ hz => rwa [norm_neg]
  | mul z w _ _ hz hw => rw [norm_mul]; exact mul_le_one₀ hz (norm_nonneg w) hw

theorem norm_le_one_of_mem_W {x : K} (hx : x ∈ W K p) : ‖x‖ ≤ 1 :=
  closure_minimal (fun y hy => norm_le_one_of_mem hy) (isClosed_le continuous_norm continuous_const)
    (mem_closure_roots_of_unity hx)

omit [IsUltrametricDist K] in
theorem inv_one_sub_mem {u : K} (hu : u ∈ W K p) (h1 : ‖u‖ < 1) : (1 - u)⁻¹ ∈ W K p := by
  have hu1 : (1 - u) ≠ 0 := by
    intro h
    rw [← sub_eq_zero.1 h, norm_one] at h1
    exact lt_irrefl _ h1

  have hsum : ∀ N, ∑ i ∈ Finset.range N, u ^ i = (1 - u)⁻¹ * (1 - u ^ N) := fun N =>
    (eq_inv_mul_iff_mul_eq₀ hu1).2 (mul_neg_geom_sum u N)
  have ht : Tendsto (fun N => ∑ i ∈ Finset.range N, u ^ i) atTop (𝓝 (1 - u)⁻¹) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1).const_sub 1).const_mul (1 - u)⁻¹
    simp only [sub_zero, mul_one] at this
    simpa only [hsum] using this
  exact (isClosed_divisorComponent (K := K) (p := p)).mem_of_tendsto ht
    (Eventually.of_forall fun N => sum_mem fun i _ => pow_mem hu i)

omit [IsUltrametricDist K] in
theorem div_mem_of_mem (hp : p.Prime) {r : K} (hr : r ∈ Subring.closure (mu K p)) (h1 : ‖r‖ < 1) :
    r / p ∈ W K p := by
  by_cases hp0 : (p : K) = 0
  · rw [hp0, div_zero]; exact zero_mem _
  obtain ⟨f, hf, s, hs, hfs⟩ := frob_periodic hp hr
  obtain ⟨t, ht⟩ : ∃ t, p ^ f = t + 2 := ⟨p ^ f - 2, by have := Nat.one_lt_pow hf.ne' hp.one_lt; omega⟩

  have hu1 : ‖r ^ (t + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) h1 (Nat.succ_ne_zero t)
  have h1u : (1 - r ^ (t + 1)) ≠ 0 := by
    intro h
    rw [← sub_eq_zero.1 h, norm_one] at hu1
    exact lt_irrefl _ hu1
  have e1 : r * (1 - r ^ (t + 1)) = -(p * s) := by
    rw [ht] at hfs
    linear_combination (-1 : K) * hfs
  have key : r / p = -s * (1 - r ^ (t + 1))⁻¹ := by
    refine div_eq_of_eq_mul hp0 ?_
    calc r = r * (1 - r ^ (t + 1)) * (1 - r ^ (t + 1))⁻¹ := (mul_inv_cancel_right₀ h1u r).symm
      _ = -(p * s) * (1 - r ^ (t + 1))⁻¹ := by rw [e1]
      _ = -s * (1 - r ^ (t + 1))⁻¹ * p := by ring
  rw [key]
  exact mul_mem (neg_mem (mem_W_of_mem hs)) (inv_one_sub_mem (mem_W_of_mem (pow_mem hr _)) hu1)

omit [IsUltrametricDist K] in

theorem div_mem (hp : p.Prime) {w : K} (hw : w ∈ W K p) (h1 : ‖w‖ < 1) : w / p ∈ W K p := by

  have hw' : w ∈ closure ({y : K | ‖y‖ < 1} ∩ (Subring.closure (mu K p) : Set K)) :=
    (isOpen_lt continuous_norm continuous_const).inter_closure ⟨h1, mem_closure_roots_of_unity hw⟩
  have := map_mem_closure (t := (W K p : Set K)) (continuous_id.div_const (p : K)) hw'
    fun y hy => div_mem_of_mem hp hy.2 hy.1
  rw [isClosed_divisorComponent.closure_eq] at this
  exact this

theorem inv_mem_of_mem (hp : p.Prime) (hpn : ‖(p : K)‖ < 1) {r : K}
    (hr : r ∈ Subring.closure (mu K p)) (h1 : ‖r‖ = 1) : r⁻¹ ∈ W K p := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at h1
  obtain ⟨f, hf, s, hs, hfs⟩ := frob_periodic hp hr
  obtain ⟨t, ht⟩ : ∃ t, p ^ f = t + 2 := ⟨p ^ f - 2, by have := Nat.one_lt_pow hf.ne' hp.one_lt; omega⟩
  have e1 : r * (r ^ (t + 1) - 1) = p * s := by
    rw [ht] at hfs
    linear_combination hfs

  have hn : ‖1 - r ^ (t + 1)‖ < 1 := by
    have h2 : ‖r‖ * ‖r ^ (t + 1) - 1‖ = ‖(p : K)‖ * ‖s‖ := by rw [← norm_mul, ← norm_mul, e1]
    rw [h1, one_mul] at h2
    rw [norm_sub_rev, h2]
    calc ‖(p : K)‖ * ‖s‖ ≤ ‖(p : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_le_one_of_mem hs) (norm_nonneg _)
      _ < 1 := by rwa [mul_one]
  have hinv : (r ^ (t + 1))⁻¹ ∈ W K p := by
    have := inv_one_sub_mem (sub_mem (one_mem _) (mem_W_of_mem (pow_mem hr (t + 1)))) hn
    rwa [sub_sub_cancel] at this
  have e2 : r⁻¹ = r ^ t * (r ^ (t + 1))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hr0), pow_succ', inv_mul_cancel_left₀ hr0]
  rw [e2]
  exact mul_mem (mem_W_of_mem (pow_mem hr t)) hinv

theorem inv_mem (hp : p.Prime) (hpn : ‖(p : K)‖ < 1) {w : K} (hw : w ∈ W K p) (h1 : ‖w‖ = 1) :
    w⁻¹ ∈ W K p := by

  obtain ⟨r, hr, hd⟩ := Metric.mem_closure_iff.1 (mem_closure_roots_of_unity hw) 1 one_pos
  have hd' : ‖r - w‖ < 1 := by rwa [dist_eq_norm, norm_sub_rev] at hd
  have hr1 : ‖r‖ = 1 := by
    apply le_antisymm
    · calc ‖r‖ = ‖w + (r - w)‖ := by rw [add_sub_cancel]
        _ ≤ max ‖w‖ ‖r - w‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ 1 := max_le h1.le hd'.le
    · by_contra hlt
      push_neg at hlt
      have : ‖w‖ < 1 :=
        calc ‖w‖ = ‖r + (w - r)‖ := by rw [add_sub_cancel]
          _ ≤ max ‖r‖ ‖w - r‖ := IsUltrametricDist.norm_add_le_max _ _
          _ < 1 := max_lt hlt (by rwa [norm_sub_rev])
      linarith
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr1
  have hri : r⁻¹ ∈ W K p := inv_mem_of_mem hp hpn hr hr1
  have ht : (r - w) * r⁻¹ ∈ W K p := mul_mem (sub_mem (mem_W_of_mem hr) hw) hri
  have htn : ‖(r - w) * r⁻¹‖ < 1 := by rw [norm_mul, norm_inv, hr1, inv_one, mul_one]; exact hd'
  have hweq : (1 - (r - w) * r⁻¹) * r = w := by
    rw [sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ hr0, mul_one, sub_sub_cancel]
  rw [← hweq, mul_inv]
  exact mul_mem (inv_one_sub_mem ht htn) hri

omit [IsUltrametricDist K] in
theorem mem_W_of_norm_le (hp : p.Prime) (hp0 : (p : K) ≠ 0) (hpn : ‖(p : K)‖ < 1) (k : ℕ) :
    ∀ {x : K}, (p : K) ^ k * x ∈ W K p → ‖x‖ ≤ 1 → x ∈ W K p := by

  induction k with
  | zero => intro x hx _; simpa using hx
  | succ k ih =>
    intro x hx hx1
    apply ih _ hx1
    have hn : ‖(p : K) ^ (k + 1) * x‖ < 1 := by
      rw [norm_mul, norm_pow]
      calc ‖(p : K)‖ ^ (k + 1) * ‖x‖ ≤ ‖(p : K)‖ ^ (k + 1) * 1 :=
            mul_le_mul_of_nonneg_left hx1 (by positivity)
        _ < 1 := by rw [mul_one]; exact pow_lt_one₀ (norm_nonneg _) hpn (Nat.succ_ne_zero k)
    have := div_mem hp hx hn
    rwa [pow_succ, mul_comm ((p : K) ^ k) (p : K), mul_assoc, mul_div_cancel_left₀ _ hp0] at this

theorem exists_unit (hp : p.Prime) (hp0 : (p : K) ≠ 0) (hpn : ‖(p : K)‖ < 1) {w : K}
    (hw : w ∈ W K p) (hw0 : w ≠ 0) : ∃ k : ℕ, w / p ^ k ∈ W K p ∧ ‖w / p ^ k‖ = 1 := by
  by_contra hcon
  push_neg at hcon

  have hall : ∀ k : ℕ, w / (p : K) ^ k ∈ W K p := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      have hlt : ‖w / (p : K) ^ k‖ < 1 := lt_of_le_of_ne (norm_le_one_of_mem_W ih) (hcon k ih)
      have := div_mem hp ih hlt
      rwa [div_div, ← pow_succ] at this
  have hle : ∀ k : ℕ, ‖w‖ ≤ ‖(p : K)‖ ^ k := by
    intro k
    have h := norm_le_one_of_mem_W (hall k)
    have hpos : 0 < ‖(p : K)‖ ^ k := pow_pos (norm_pos_iff.2 hp0) k
    rwa [norm_div, norm_pow, div_le_one hpos] at h
  have : ‖w‖ ≤ 0 := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hpn) hle
  exact hw0 (norm_le_zero_iff.1 this)

def F (hp : p.Prime) (hp0 : (p : K) ≠ 0) (hpn : ‖(p : K)‖ < 1) : Subfield K where
  carrier := {x | ∃ k : ℕ, (p : K) ^ k * x ∈ W K p}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have e : (p : K) ^ (k + l) * (a + b) = p ^ l * (p ^ k * a) + p ^ k * (p ^ l * b) := by ring
    rw [e]
    exact add_mem (mul_mem (pow_mem (natCast_mem _ _) _) hk) (mul_mem (pow_mem (natCast_mem _ _) _) hl)
  mul_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have e : (p : K) ^ (k + l) * (a * b) = (p ^ k * a) * (p ^ l * b) := by ring
    rw [e]
    exact mul_mem hk hl
  neg_mem' := by
    rintro a ⟨k, hk⟩
    exact ⟨k, by rw [mul_neg]; exact neg_mem hk⟩
  inv_mem' := by
    rintro a ⟨k, hk⟩
    by_cases ha : a = 0
    · exact ⟨0, by simp [ha]⟩
    obtain ⟨l, hl, hl1⟩ := exists_unit hp hp0 hpn hk (mul_ne_zero (pow_ne_zero _ hp0) ha)
    refine ⟨l, ?_⟩
    have e : (p : K) ^ l * a⁻¹ = p ^ k * (p ^ k * a / p ^ l)⁻¹ := by field_simp
    rw [e]
    exact mul_mem (pow_mem (natCast_mem _ _) _) (inv_mem hp hpn hl hl1)

theorem isClosed_F (hp : p.Prime) (hp0 : (p : K) ≠ 0) (hpn : ‖(p : K)‖ < 1) :
    IsClosed (F hp hp0 hpn : Set K) := by

  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / (‖x‖ + 1)) hpn
  have hx1 : 0 < ‖x‖ + 1 := by positivity
  rw [lt_div_iff₀ hx1] at hk
  have hx' : x ∈ closure ({y : K | ‖y - x‖ < 1} ∩ (F hp hp0 hpn : Set K)) :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).inter_closure ⟨by simp, hx⟩
  have hmap : Set.MapsTo (fun y => (p : K) ^ k * y) ({y : K | ‖y - x‖ < 1} ∩ (F hp hp0 hpn : Set K))
      (W K p : Set K) := by
    rintro y ⟨hy1, hy2⟩
    have hy1' : ‖y - x‖ < 1 := hy1
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (p : K) ^ j * y ∈ W K p := hy2
    have hyn : ‖y‖ ≤ ‖x‖ + 1 := by
      calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + 1 := by linarith
    apply mem_W_of_norm_le hp hp0 hpn j
    · have e : (p : K) ^ j * ((p : K) ^ k * y) = (p : K) ^ k * ((p : K) ^ j * y) := by ring
      rw [e]
      exact mul_mem (pow_mem (natCast_mem _ _) _) hj
    · rw [norm_mul, norm_pow]
      calc ‖(p : K)‖ ^ k * ‖y‖ ≤ ‖(p : K)‖ ^ k * (‖x‖ + 1) :=
            mul_le_mul_of_nonneg_left hyn (by positivity)
        _ ≤ 1 := hk.le
  have := map_mem_closure (continuous_const.mul continuous_id) hx' hmap
  rw [isClosed_divisorComponent.closure_eq] at this
  exact (show ∃ k : ℕ, (p : K) ^ k * x ∈ W K p from ⟨k, this⟩)

end Normed

theorem norm_p_lt_one {p : ℕ} [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by

  have h := PadicComplex.norm_extends' (p := p) (p : ℚ_[p])
  push_cast at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem inWf_of_mem_Kur {p : ℕ} [inst : Fact (Nat.Prime p)] {x : ℂ_[p]}
    (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) : Formalism.MainNotions.GL3Theta.InWf x := by

  have hp : p.Prime := inst.out
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hsub : Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ≤ F hp hp0 norm_p_lt_one := by
    refine Subfield.topologicalClosure_minimal _ ?_ (isClosed_F hp hp0 norm_p_lt_one)
    refine Subfield.closure_le.2 fun ζ hζ => ?_
    obtain ⟨n, hn, hnd, h1⟩ := hζ
    have hmu : ζ ∈ mu ℂ_[p] p := ⟨n, hn, ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm, h1⟩
    exact ⟨0, by simpa using mem_W_of_mem (Subring.subset_closure hmu)⟩
  exact hsub hx

end GlobalTheory.WittRootsOfUnity
end

section
section
noncomputable section

namespace GlobalTheory.CoefWfUnram

open Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime]

theorem inWf_of_kur {x : ℂ_[p]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) : InWf x := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | exact @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | (apply _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> assumption)
  | (intros; apply _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur ..)

theorem coefWf_phW_of_kur (W : WeierstrassCurve ℂ_[p]) (h1 : W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p)
    (h2 : W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h3 : W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h4 : W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p)
    (h6 : W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) {s2 : ℂ_[p]} (hs : s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) :
    CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) := by
  let K := Formalism.L2.Th1.CM.MaximalUnramifiedExtension p
  let W' : WeierstrassCurve K := ⟨⟨W.a₁, h1⟩, ⟨W.a₂, h2⟩, ⟨W.a₃, h3⟩, ⟨W.a₄, h4⟩, ⟨W.a₆, h6⟩⟩
  have hWW : W'.map K.subtype = W := rfl
  obtain ⟨hl, -, hwp, -, -⟩ := Formalism.L2.Th1.A.zMap K ℂ_[p] K.subtype W'
  obtain ⟨h0, h1', -, -⟩ := Formalism.L2.Th1.A.logSpec K W'
  have hB := (Formalism.L2.Th1.B.baseChange K ℂ_[p] K.subtype ⟨s2, hs⟩ 0 0 (Formalism.L2.Th1.A.wpReg W') 0
    (Formalism.L2.Th1.A.logSer W') 0 h0 h1' (by simp)).2.2.2.2.1
  have e : Formalism.L2.Th1.B.phW W s2 =
      PowerSeries.map K.subtype (Formalism.L2.Th1.B.phO ⟨s2, hs⟩ (Formalism.L2.Th1.A.wpReg W') (Formalism.L2.Th1.A.logSer W')) := by
    rw [hB, hl, hwp, hWW]
    rfl
  intro n
  rw [e]
  refine inWf_of_kur ?_
  rw [show MvPowerSeries.coeff n (PowerSeries.map K.subtype
      (Formalism.L2.Th1.B.phO ⟨s2, hs⟩ (Formalism.L2.Th1.A.wpReg W') (Formalism.L2.Th1.A.logSer W')) : MvPowerSeries Unit ℂ_[p]) =
      K.subtype (MvPowerSeries.coeff n (Formalism.L2.Th1.B.phO ⟨s2, hs⟩ (Formalism.L2.Th1.A.wpReg W')
        (Formalism.L2.Th1.A.logSer W') : MvPowerSeries Unit K)) from MvPowerSeries.coeff_map _ _ _]
  exact (MvPowerSeries.coeff n _ : K).2

theorem coefWf_phW : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) :=
  fun _ _ W h1 h2 h3 h4 h6 _ hs => coefWf_phW_of_kur W h1 h2 h3 h4 h6 hs

end GlobalTheory.CoefWfUnram
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedWeierstrassCurve_transform_coefficients_wellFormed : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) := by
  atlas_forward_decl GlobalTheory.CoefWfUnram.coefWf_phW
end

section
section
noncomputable section

namespace GlobalTheory.BeCoefficients

open Formalism.MainNotions.FormalGroupSystem
open Formalism.MainNotions.GL3Theta (G1 ModelOverW)
open Formalism.L2.G.Pend (k0ToC)

theorem beCoef : Formalism.L2.KerInert.BeCob.BeCoef := by
  intro l _ g hOk hM hph
  obtain ⟨P0, hP0⟩ := (Formalism.L2.G.Pend.coefWf_iff _).1 hph
  obtain ⟨E0, hE0⟩ := (Formalism.L2.G.Pend.coefWf_iff _).1 (Formalism.L2.G.Pend.exRat_of g hOk hM)
  obtain ⟨L0, hL0⟩ := Formalism.L2.G.Pend.l_mem_ratSub g hOk.2.1 hM
  have hP0' : PowerSeries.map (k0ToC l) P0 = g.ph := hP0
  have hE0' : PowerSeries.map (k0ToC l) E0 = g.ex := hE0
  have hL0' : PowerSeries.map (k0ToC l) L0 = g.l := hL0
  have hE00 : PowerSeries.constantCoeff E0 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply (map_eq_zero_iff _ (k0ToC l).injective).1
    rw [← PowerSeries.coeff_map, hE0', PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hOk.2.2.1
  have hL00 : PowerSeries.constantCoeff L0 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply (map_eq_zero_iff _ (k0ToC l).injective).1
    rw [← PowerSeries.coeff_map, hL0', PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Formalism.MainNotions.J.cc_l g
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hs0 : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) = 0 := by
    rw [map_add, PowerSeries.constantCoeff_subst_eq_zero (hX 0) _ hL00,
      PowerSeries.constantCoeff_subst_eq_zero (hX 1) _ hL00, add_zero]
  have hs1 : MvPowerSeries.constantCoeff (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) E0) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hs0 _ hE00
  refine (Formalism.L2.G.Pend.coefWf_iff _).2 ⟨PowerSeries.subst (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) E0) P0 -
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) P0 -
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) P0, ?_⟩
  rw [map_sub, map_sub, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs1),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 0)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 1)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs0), map_add,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 0)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 1)),
    MvPowerSeries.map_X, MvPowerSeries.map_X, hP0', hE0', hL0']
  rfl

end GlobalTheory.BeCoefficients
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_model_coefficients_invert_l : Formalism.L2.KerInert.BeCob.BeCoef := by
  atlas_forward_decl GlobalTheory.BeCoefficients.beCoef
end

section
section
noncomputable section

namespace GlobalTheory.CobExactProof

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.KerInert.BeCob (eLT vLT psiLT)
open GlobalTheory.CurveDictionary (map_cob lgF_eq_logF cc_lgF')

theorem cobExact : Formalism.L2.KerInert.BeCob.CobExact := by
  intro l _ g hLT hOk hb F hF
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  set Lc : PowerSeries ℂ_[l] := lgF ℂ_[l] l with hLc
  have hL0 : PowerSeries.constantCoeff Lc = 0 := cc_lgF' ℂ_[l] l
  have hlog0 : PowerSeries.constantCoeff (Formalism.MainNotions.FormalGroupSystem.logF l) = 0 := by
    have h1 : k0ToC l (PowerSeries.coeff 0 (Formalism.MainNotions.FormalGroupSystem.logF l)) = 0 := by
      rw [← PowerSeries.coeff_map, lgF_eq_logF, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact cc_lgF' ℂ_[l] l
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (map_eq_zero_iff _ (k0ToC l).injective).1 h1
  have hcK : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l)) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hlog0
  have hsK : MvPowerSeries.HasSubst (fun i : Fin 2 =>
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hcK
  set c : Fin 2 → MvPowerSeries (Fin 2) ℂ_[l] := fun i => PowerSeries.subst (MvPowerSeries.X i) Lc with hcdef
  have hcC : ∀ i, MvPowerSeries.constantCoeff (c i) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hL0
  have hsC : MvPowerSeries.HasSubst c := MvPowerSeries.hasSubst_of_constantCoeff_zero hcC
  have hB : MvPowerSeries.map (k0ToC l) (inParam l (beLT hLT)) =
      MvPowerSeries.subst c (Formalism.L2.G.Pend.beC g e) := by
    unfold inParam
    rw [MvPowerSeries.map_subst hsK]
    have hc' : (fun i : Fin 2 => MvPowerSeries.map (k0ToC l)
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l))) = c := by
      funext i
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)),
        MvPowerSeries.map_X, lgF_eq_logF]
    rw [hc']
    congr 1
    exact Formalism.L2.G.Pend.map_beOf hb
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (MvPowerSeries.C e⁻¹ * MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) = 0 := by
    intro i
    rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  unfold Formalism.L2.G.Pend.beC at hB
  rw [Formalism.MainNotions.J.be_subst g hex hsC (Formalism.MainNotions.J.cc_pt g hex (h0 0)) (Formalism.MainNotions.J.cc_pt g hex (h0 1)),
    Formalism.MainNotions.J.pt_subst g hsC (h0 0), Formalism.MainNotions.J.pt_subst g hsC (h0 1), MvPowerSeries.subst_mul hsC,
    MvPowerSeries.subst_mul hsC, MvPowerSeries.subst_C, MvPowerSeries.subst_X hsC, MvPowerSeries.subst_X hsC] at hB
  rw [hB]

  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * Lc) = 0 := by
    rw [map_mul, hL0, mul_zero]
  have hvS : PowerSeries.HasSubst (PowerSeries.C e⁻¹ * Lc) := PowerSeries.HasSubst.of_constantCoeff_zero' hv0
  have hvcc : PowerSeries.constantCoeff (vLT hLT) = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hcA : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.C e⁻¹ * c i) = 0 := by
    intro i; rw [map_mul, hcC i, mul_zero]
  have hat : ∀ i : Fin 2, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) (vLT hLT) =
      g.pt (MvPowerSeries.C e⁻¹ * c i) := by
    intro i
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply hvS
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))]
    unfold G1.pt
    congr 1
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X i), PowerSeries.subst_C]
  have hpsi : ∀ i : Fin 2, at1 i (psiLT hLT) = g.phAt (g.pt (MvPowerSeries.C e⁻¹ * c i)) := by
    intro i
    unfold at1 psiLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hvcc)
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)), hat i]
    rfl
  have hlgA : ∀ i, g.lg (g.pt (MvPowerSeries.C e⁻¹ * c i)) = MvPowerSeries.C e⁻¹ * c i := by
    intro i
    unfold G1.lg G1.pt
    rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex)
      (PowerSeries.HasSubst.of_constantCoeff_zero (hcA i)), hinv,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (hcA i))]
  set Fc := MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F with hFc
  have hFc0 : MvPowerSeries.constantCoeff Fc = 0 := by
    rw [hFc, MvPowerSeries.constantCoeff_map, hF.1, map_zero]
  have hLaw : PowerSeries.subst Fc Lc = c 0 + c 1 := by
    have h := congrArg (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype) hF.2.2
    rw [map_cob _ F hF.1, map_zero, Formalism.L2.Th1.E.Joints.map_lgF'] at h
    unfold cob at1 at h
    rw [← hFc] at h
    show _ = PowerSeries.subst (MvPowerSeries.X 0) Lc + PowerSeries.subst (MvPowerSeries.X 1) Lc
    linear_combination h
  have hadd : g.add (g.pt (MvPowerSeries.C e⁻¹ * c 0)) (g.pt (MvPowerSeries.C e⁻¹ * c 1)) =
      PowerSeries.subst Fc (vLT hLT) := by
    unfold G1.add
    rw [hlgA 0, hlgA 1, ← mul_add, ← hLaw]
    unfold vLT G1.pt
    rw [PowerSeries.subst_comp_subst_apply hvS (PowerSeries.HasSubst.of_constantCoeff_zero hFc0)]
    congr 1
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hFc0), PowerSeries.subst_C]
  unfold G1.be cob
  rw [hadd, ← hpsi 0, ← hpsi 1]
  unfold G1.phAt psiLT
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hvcc)
    (PowerSeries.HasSubst.of_constantCoeff_zero hFc0)]

end GlobalTheory.CobExactProof
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_coordinates_exponent_is_coboundary : Formalism.L2.KerInert.BeCob.CobExact := by
  atlas_forward_decl GlobalTheory.CobExactProof.cobExact
end

section
section
noncomputable section

namespace GlobalTheory.CobSimeqProof

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (cob)

theorem simeq_neg {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {f g : MvPowerSeries ι K}
    (h : Formalism.InvariantFactorPaths.G7.Simeq f g) : Formalism.InvariantFactorPaths.G7.Simeq (-f) (-g) := by
  have h' := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).2.1 f g h
  unfold Formalism.InvariantFactorPaths.G7.Simeq at h' ⊢
  rwa [show -f - -g = g - f by ring]

theorem integral_X {K ι : Type} [NormedField K] (i : ι) : Integral (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem cobSimeq : Formalism.L2.KerInert.BeCob.CobSimeq := by
  intro K _ _ _ F hF0 hFI f f' h
  have R := Formalism.InvariantFactorPaths.G7.Top.simeqRules K Unit
  have hs : ∀ (φ : Unit → MvPowerSeries (Fin 2) K), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
      (∀ i, Integral (φ i)) →
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.subst φ (f : MvPowerSeries Unit K))
        (MvPowerSeries.subst φ (f' : MvPowerSeries Unit K)) :=
    fun φ h0 hI => R.2.2.2.2 (Fin 2) f f' φ h0 hI h
  have h1 := hs (fun _ => F) (fun _ => hF0) (fun _ => hFI)
  have h2 := simeq_neg (hs (fun _ => MvPowerSeries.X 0) (fun _ => MvPowerSeries.constantCoeff_X _)
    (fun _ => integral_X _))
  have h3 := simeq_neg (hs (fun _ => MvPowerSeries.X 1) (fun _ => MvPowerSeries.constantCoeff_X _)
    (fun _ => integral_X _))
  have R2 := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Fin 2)
  have H := R2.2.2.2.1 _ _ _ _ (R2.2.2.2.1 _ _ _ _ h1 h2) h3
  have e : ∀ q : PowerSeries K, cob F q = MvPowerSeries.subst (fun _ => F) (q : MvPowerSeries Unit K) +
      -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (q : MvPowerSeries Unit K) +
      -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) (q : MvPowerSeries Unit K) := by
    intro q
    unfold cob Formalism.InvariantFactorPaths.G7.at1 PowerSeries.subst
    ring
  rw [e f, e f']
  exact H

end GlobalTheory.CobSimeqProof
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_integral_law_respects_simeq : Formalism.L2.KerInert.BeCob.CobSimeq := by
  atlas_forward_decl GlobalTheory.CobSimeqProof.cobSimeq
end

section
section
noncomputable section

namespace GlobalTheory.ShortModelTie

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.KerInert.BeCob
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.DworkPowerSeriesWeights (Integral)
open GlobalTheory.CurveDictionary (lgF_eq_logF cc_lgF')

theorem X_mul_lU {K : Type} [Field K] [CharZero K] (f : PowerSeries K) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.X * Formalism.L2.Th1.B.lU f = f := by
  ext n
  cases n with
  | zero => rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk]

theorem integral_ps {K : Type} [NormedField K] {f : PowerSeries K}
    (h : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1) : Integral (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by rcases u with ⟨⟩; simp
  rw [e]
  exact h (n ())

theorem exists_witt_series_inverse_formalGroup_iso {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (n : ℕ) :
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

theorem phTie : Formalism.L2.KerInert.BeCob.PhTie := by
  intro l _ g hLT hOk s2 hph
  have hp : l.Prime := Fact.out
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set Lc : PowerSeries ℂ_[l] := lgF ℂ_[l] l with hLc
  have hL0 : PowerSeries.constantCoeff Lc = 0 := cc_lgF' _ _
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * Lc) = 0 := by
    rw [map_mul, hL0, mul_zero]
  set v := vLT hLT with hvdef
  have hvcc : PowerSeries.constantCoeff v = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hvS : PowerSeries.HasSubst v := PowerSeries.HasSubst.of_constantCoeff_zero' hvcc
  set lW := Formalism.L2.Th1.A.logSer g.W with hlWdef
  have hgl : g.l = lW := Formalism.L2.KerInert.Dict.formal_logarithm_agree l g.W g.wq hOk.2.1
  have hlW0 : PowerSeries.constantCoeff lW = 0 := by rw [← hgl]; exact Formalism.MainNotions.J.cc_l g
  have hlW1 : PowerSeries.coeff 1 lW = 1 := (Formalism.L2.Th1.A.logSpec ℂ_[l] g.W).2.1
  have hvl : PowerSeries.subst v lW = PowerSeries.C e⁻¹ * Lc := by
    rw [← hgl]; exact Formalism.L2.G.Pend.lg_pt g hex hinv hv0
  set P := Formalism.L2.Th1.A.wpReg g.W with hPdef
  have hP : Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W)) = P := by
    rw [GlobalTheory.CurveDictionary.wpReg_eq, hPdef, GlobalTheory.CurveDictionary.wpReg_eq g.W, (Formalism.L2.Th1.A.shortInv ℂ_[l] _ _).2.1,
      (Formalism.L2.Th1.A.shortInv ℂ_[l] _ _).2.2.1]
  have hneg : ∀ f : PowerSeries ℂ_[l], PowerSeries.subst v (-f) = -PowerSeries.subst v f := fun f => by
    rw [← PowerSeries.coe_substAlgHom hvS, map_neg]
  have hlU1 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.lU lW : MvPowerSeries Unit ℂ_[l]) = 1 := by
    show PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU lW) = 1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, hlW1]
  set U := PowerSeries.subst v (Formalism.L2.Th1.B.lU lW) with hU
  have hψ : psiLT hLT = -PowerSeries.subst (PowerSeries.C e⁻¹ * Lc) (Formalism.L2.Th1.B.sigS P) +
      PowerSeries.C (s2 / 2) * (PowerSeries.C e⁻¹ * Lc) ^ 2 - Formalism.L2.Th1.B.fLog U := by
    unfold psiLT
    rw [hph]
    unfold Formalism.L2.Th1.B.phW Formalism.L2.Th1.B.phO
    rw [PowerSeries.subst_sub hvS, PowerSeries.subst_add hvS, hneg, PowerSeries.subst_mul hvS,
      PowerSeries.subst_pow hvS, PowerSeries.subst_C, hvl,
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlW0) hvS, hvl]
    have hfl : PowerSeries.subst v (Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU lW)) = Formalism.L2.Th1.B.fLog U := by
      rw [hU, PowerSeries.subst_def, PowerSeries.subst_def]
      exact Formalism.L2.Th1.B.subst_fLog (fun _ => hvcc) hlU1
    rw [← hfl]
    rfl
  have hFF : phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 e⁻¹ =
      -PowerSeries.subst (PowerSeries.C e⁻¹ * Lc) (Formalism.L2.Th1.B.sigS P) +
      PowerSeries.C (s2 / 2) * (PowerSeries.C e⁻¹ * Lc) ^ 2 - Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU Lc) := by
    unfold phFF
    rw [hP]

  have hvU : v * U = PowerSeries.C e⁻¹ * Lc := by
    have h1 : PowerSeries.subst v (PowerSeries.X * Formalism.L2.Th1.B.lU lW) = v * U := by
      rw [PowerSeries.subst_mul hvS, PowerSeries.subst_X hvS]
    rw [← h1, X_mul_lU lW hlW0, hvl]
  have hprod : Formalism.L2.Th1.B.lU Lc = (PowerSeries.C e * Formalism.L2.Th1.B.lU v) * U := by
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℂ_[l]))
    rw [X_mul_lU Lc hL0]
    calc Lc = PowerSeries.C e * (PowerSeries.C e⁻¹ * Lc) := by
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hene, map_one, one_mul]
      _ = PowerSeries.C e * (v * U) := by rw [hvU]
      _ = PowerSeries.X * (PowerSeries.C e * Formalism.L2.Th1.B.lU v * U) := by
          rw [show PowerSeries.C e * (v * U) = PowerSeries.C e * ((PowerSeries.X * Formalism.L2.Th1.B.lU v) * U) by
            rw [X_mul_lU v hvcc]]
          ring

  have hex1 : PowerSeries.coeff 1 g.ex = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hinv
    rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hex, Formalism.L2.G.Pend.coeff_one_l g hOk.2.1, one_mul,
      PowerSeries.coeff_one_X] at h
    exact h
  have hv1 : PowerSeries.coeff 1 v = e⁻¹ := by
    rw [hvdef]
    unfold vLT
    rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hv0, hex1, one_mul, PowerSeries.coeff_C_mul,
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF l hp.two_le, mul_one]
  have hA : MvPowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v : MvPowerSeries Unit ℂ_[l]) = 1 := by
    show PowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v) = 1
    rw [map_mul, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, hv1, mul_inv_cancel₀ hene]
  have hLU : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU Lc) = 1 := Formalism.L2.Th1.E.Joints.cc_lU hp.two_le
  have hUc : MvPowerSeries.constantCoeff (U : MvPowerSeries Unit ℂ_[l]) = 1 := by
    have h := congrArg PowerSeries.constantCoeff hprod
    rw [hLU, map_mul] at h
    have hA' : PowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v) = 1 := hA
    rw [hA', one_mul] at h
    exact h.symm
  have hdiff : (psiLT hLT : MvPowerSeries Unit ℂ_[l]) -
      phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 e⁻¹ =
      Formalism.L2.Th1.B.fLog (PowerSeries.C e * Formalism.L2.Th1.B.lU v : MvPowerSeries Unit ℂ_[l]) := by
    rw [hψ, hFF, hprod, Formalism.L2.Th1.B.ParO.fLog_mul hA hUc]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdiff]; exact Formalism.L2.Th1.B.constantCoeff_fLog hA
  · rw [hdiff]
    show Integral (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.fLog _))
    rw [Formalism.L2.Th1.B.fExp_fLog hA]
    apply integral_ps
    intro k
    rw [PowerSeries.coeff_C_mul, norm_mul, he1, one_mul]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk]
    exact v_integral hOk hLT (k + 1)

end GlobalTheory.ShortModelTie
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phEquiv_shortWeierstrassModel : Formalism.L2.KerInert.BeCob.PhTie := by
  atlas_forward_decl GlobalTheory.ShortModelTie.phTie
end

section
section
noncomputable section

namespace GlobalTheory.ShortModelTheta

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso epOf)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.L2.KerInert.BeCob (eLT vLT ThetaTie ShortIso)
open GlobalTheory.CurveDictionary (cc_lgF' lgF_eq_logF)

section IntPS

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem integral_ps' {K : Type} [NormedField K] {f : PowerSeries K}
    (h : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1) : Integral (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by rcases u with ⟨⟩; simp
  rw [e]
  exact h (n ())

theorem ips' {f : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K)) (k : ℕ) :
    ‖PowerSeries.coeff k f‖ ≤ 1 := hf _

theorem ips_add' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f + g : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ips' hf k) (ips' hg k))

theorem ips_sub' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f - g : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [map_sub, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ips' hf k) (by rw [norm_neg]; exact ips' hg k))

theorem ips_Cmul' {c : K} (hc : ‖c‖ ≤ 1) {f : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K)) :
    Integral ((PowerSeries.C c * f : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [PowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (ips' hf k)

theorem ips_X' : Integral ((PowerSeries.X : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp

theorem ips_mul' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f * g : PowerSeries K) : MvPowerSeries Unit K) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hf hg

end IntPS

theorem shortIso_holds : ShortIso := by
  intro K _ _ _ h2 h3 W hW
  obtain ⟨hxI, hx1, hA, -⟩ := Formalism.L2.Th1.A.bridgeCurve K W hW
  obtain ⟨hB, -⟩ := Formalism.L2.Th1.A.bridgeCurve3 K W hW
  obtain ⟨hnum, hden⟩ := Formalism.L2.Th1.A.wpNumEq K W
  rw [← Formalism.L2.Th1.A.uSerEq K _ _]
  obtain ⟨hl0, hl1, -, -⟩ := Formalism.L2.Th1.A.logSpec K W
  have hlS : PowerSeries.HasSubst (Formalism.L2.Th1.A.logSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have hl_ne : Formalism.L2.Th1.A.logSer W ≠ 0 := by
    intro h; rw [h, map_zero] at hl1; exact zero_ne_one hl1
  set lW := Formalism.L2.Th1.A.logSer W with hlW
  set P := Formalism.L2.Th1.A.wpReg W with hP
  set xs := Formalism.L2.Th1.A.xS W with hxs
  set N : PowerSeries K := xs + PowerSeries.C (W.b₂ / 12) * PowerSeries.X ^ 2 with hN
  set D : PowerSeries K := xs - PowerSeries.C (W.a₁ / 2) * PowerSeries.X * xs -
    PowerSeries.C (W.a₃ / 2) * PowerSeries.X ^ 3 with hD
  have hD1 : PowerSeries.constantCoeff D = 1 := by
    rw [hD]; simp [hx1]
  have hden1 : PowerSeries.constantCoeff (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) ≠ 0 := by
    rw [hden]; simp
  have hsn : PowerSeries.subst lW (Formalism.L2.Th1.CM.wpNum (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      1 + lW ^ 2 * PowerSeries.subst lW P := by
    rw [hnum, PowerSeries.subst_add hlS, PowerSeries.subst_mul hlS, PowerSeries.subst_pow hlS,
      PowerSeries.subst_X hlS, ← PowerSeries.coe_substAlgHom hlS, map_one]
  have hsd : PowerSeries.subst lW (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      1 - PowerSeries.C (1 / 2 : K) * lW ^ 3 * PowerSeries.subst lW (PowerSeries.derivative K P) := by
    rw [hden, PowerSeries.subst_sub hlS, PowerSeries.subst_mul hlS, PowerSeries.subst_mul hlS,
      PowerSeries.subst_pow hlS, PowerSeries.subst_X hlS, PowerSeries.subst_C, ← PowerSeries.coe_substAlgHom hlS,
      map_one]
    rfl
  set I := PowerSeries.subst lW (Formalism.L2.Th1.CM.uSer (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) with hI
  have hIB : I * PowerSeries.subst lW (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      lW * PowerSeries.subst lW (Formalism.L2.Th1.CM.wpNum (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) := by
    rw [hI, ← PowerSeries.subst_mul hlS]
    unfold Formalism.L2.Th1.CM.uSer
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hden1, mul_one, PowerSeries.subst_mul hlS, PowerSeries.subst_X hlS]
  rw [hsn, hsd] at hIB
  have hID : I * D = PowerSeries.X * N := by
    have h3ne : lW ^ 3 ≠ 0 := pow_ne_zero 3 hl_ne
    apply mul_left_cancel₀ h3ne
    have e2 : (2 : K) ≠ 0 := two_ne_zero
    have hB' : PowerSeries.X ^ 3 * (1 - PowerSeries.C (1 / 2 : K) * lW ^ 3 * PowerSeries.subst lW (PowerSeries.derivative K P)) =
        lW ^ 3 * D := by
      have hh : (PowerSeries.C (1 / 2 : K) : PowerSeries K) * (2 : PowerSeries K) = 1 := by
        rw [show (2 : PowerSeries K) = PowerSeries.C (2 : K) from (map_ofNat _ 2).symm, ← map_mul]; norm_num
      rw [hD]
      have ha1 : (PowerSeries.C (W.a₁ / 2) : PowerSeries K) = PowerSeries.C (1 / 2 : K) * PowerSeries.C W.a₁ := by
        rw [← map_mul]; ring_nf
      have ha3 : (PowerSeries.C (W.a₃ / 2) : PowerSeries K) = PowerSeries.C (1 / 2 : K) * PowerSeries.C W.a₃ := by
        rw [← map_mul]; ring_nf
      rw [ha1, ha3]
      linear_combination (-(PowerSeries.C (1 / 2 : K) : PowerSeries K)) * hB -
        (PowerSeries.X ^ 3 - lW ^ 3 * xs) * hh
    linear_combination PowerSeries.X ^ 3 * hIB - I * hB' + lW * PowerSeries.X * hA
  have hDinv : D⁻¹ * D = 1 := PowerSeries.inv_mul_cancel _ (by rw [hD1]; exact one_ne_zero)
  have hIe : I = PowerSeries.X * N * D⁻¹ := by
    calc I = I * D * D⁻¹ := by rw [mul_assoc, mul_comm D, hDinv, mul_one]
      _ = _ := by rw [hID]
  rw [hIe]
  have h12 : ‖(12 : K)‖ = 1 := by
    rw [show (12 : K) = 2 * 2 * 3 by norm_num, norm_mul, norm_mul, h2, h3]; norm_num
  have hi1 : ‖W.a₁‖ ≤ 1 := hW.1
  have hi2 : ‖W.a₂‖ ≤ 1 := hW.2.1
  have hi3 : ‖W.a₃‖ ≤ 1 := hW.2.2.1
  have hb2 : ‖W.b₂ / 12‖ ≤ 1 := by
    rw [norm_div, h12, div_one, WeierstrassCurve.b₂]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hi1
    · rw [norm_mul]
      refine mul_le_one₀ ?_ (norm_nonneg _) hi2
      rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]; norm_num
  have ha12 : ‖W.a₁ / 2‖ ≤ 1 := by rw [norm_div, h2, div_one]; exact hi1
  have ha32 : ‖W.a₃ / 2‖ ≤ 1 := by rw [norm_div, h2, div_one]; exact hi3
  have hX2 : Integral (((PowerSeries.X : PowerSeries K) ^ 2 : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [pow_two]; exact ips_mul' ips_X' ips_X'
  have hX3 : Integral (((PowerSeries.X : PowerSeries K) ^ 3 : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [pow_succ]; exact ips_mul' hX2 ips_X'
  have hNI : Integral ((N : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [hN]; exact ips_add' hxI (ips_Cmul' hb2 hX2)
  have hDI : Integral ((D : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [hD]
    exact ips_sub' (ips_sub' hxI (ips_mul' (ips_Cmul' ha12 ips_X') hxI)) (ips_Cmul' ha32 hX3)
  have hDiI : Integral ((D⁻¹ : PowerSeries K) : MvPowerSeries Unit K) :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_of_mul_eq_one hDI hD1 hDinv
  exact ips_mul' (ips_mul' ips_X' hNI) hDiI

theorem exists_witt_series_inverse_formalGroup_iso_short {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral' {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (n : ℕ) :
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso_short hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

theorem norm_nat_one' {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) (m : ℕ) (hm1 : 0 < m) (hm : m < 5) :
    ‖(m : ℂ_[l])‖ = 1 := by
  have hp : l.Prime := Fact.out
  refine Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one l) ?_
  intro h
  have := Nat.le_of_dvd hm1 h
  omega

theorem thetaTie_holds : ThetaTie := by
  intro l _ h5 g hLT hOk n
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hvcc : PowerSeries.constantCoeff (vLT hLT) = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hvS : PowerSeries.HasSubst (vLT hLT) := PowerSeries.HasSubst.of_constantCoeff_zero' hvcc
  have hgl : g.l = Formalism.L2.Th1.A.logSer g.W := Formalism.L2.KerInert.Dict.formal_logarithm_agree l g.W g.wq hOk.2.1
  have hlW0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer g.W) = 0 := by rw [← hgl]; exact Formalism.MainNotions.J.cc_l g
  have hvl : PowerSeries.subst (vLT hLT) (Formalism.L2.Th1.A.logSer g.W) = PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l := by
    rw [← hgl]; exact Formalism.L2.G.Pend.lg_pt g hex hinv hv0
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_nat_one' h5 2 (by norm_num) (by norm_num)
  have h3 : ‖(3 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_nat_one' h5 3 (by norm_num) (by norm_num)
  have hiso := shortIso_holds ℂ_[l] h2 h3 g.W (Formalism.L2.KerInert.Dict.intModel_of_ok hOk)
  have hθ : thetaS l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) (eLT hLT)⁻¹ =
      MvPowerSeries.subst (fun _ => vLT hLT) (PowerSeries.subst (Formalism.L2.Th1.A.logSer g.W)
        (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W)))) := by
    unfold thetaS
    rw [Formalism.L2.Th1.A.uSerEq ℂ_[l] _ _, ← PowerSeries.subst_def,
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlW0) hvS, hvl]
  rw [hθ]
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun _ => hvcc) (fun _ => integral_ps' (v_integral' hOk hLT)) hiso
    (Finsupp.single () n)

end GlobalTheory.ShortModelTheta
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaUnitFunction_shortModel_integral : Formalism.L2.KerInert.BeCob.ThetaTie := by
  atlas_forward_decl GlobalTheory.ShortModelTheta.thetaTie_holds
end

section
section
noncomputable section

namespace GlobalTheory.InverseSeriesIntegral

open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (wToC LTIso)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.L2.KerInert.BeCob (vLT eLT)
open GlobalTheory.CurveDictionary (cc_lgF' lgF_eq_logF)

theorem exists_witt_series_inverse_formalGroup_iso {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (Formalism.MainNotions.FormalGroupSystem.WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral : ∀ (l : ℕ) [Fact l.Prime] (g : G1 l), g.Ok → ∀ (hLT : LTIso g) (n : ℕ),
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  intro l _ g hOk hLT n
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

end GlobalTheory.InverseSeriesIntegral
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_series_formalGroup_iso_integral : ∀ (l : ℕ) [Fact l.Prime] (g : Formalism.MainNotions.GL3Theta.G1 l), g.Ok → ∀ (hLT : Formalism.L2.G.Pend.LTIso g) (n : ℕ), ‖PowerSeries.coeff n (Formalism.L2.KerInert.BeCob.vLT hLT)‖ ≤ 1 := by
  atlas_forward_decl GlobalTheory.InverseSeriesIntegral.v_integral
end

section
namespace GlobalTheory.CurveDictionary

theorem curveDict_of_cm : Formalism.L2.Th1.CM.CM2 → Formalism.L2.Th1.CM.CM3 → Formalism.L2.Th1.CM.CM4 →
    Formalism.L2.KerInert.Rep.CurveDict := fun hGood _ hTor =>
  curveDict_of_inputs hGood hTor GlobalTheory.T.curveLattice_sigmaTwo_algebraic_of_invariants_algebraic GlobalTheory.T.unramifiedWeierstrassCurve_transform_coefficients_wellFormed GlobalTheory.T.beta_model_coefficients_invert_l GlobalTheory.T.log_coordinates_exponent_is_coboundary GlobalTheory.T.coboundary_integral_law_respects_simeq
    GlobalTheory.T.phEquiv_shortWeierstrassModel GlobalTheory.T.thetaUnitFunction_shortModel_integral GlobalTheory.T.inverse_series_formalGroup_iso_integral

end GlobalTheory.CurveDictionary
end

section
namespace GlobalTheory.CurveThetaInert

theorem torsionTaylorAlgebraic_latticeExists_of_cm (h2 : Formalism.L2.Th1.CM.CM2) :
    Formalism.L2.KerInert.AlgTAll ∧ Formalism.L2.KerInert.GenusOneModelExistsLattice ∧ Formalism.L2.KerInert.Rep.CurveDict :=
  ⟨GlobalTheory.ThLoc.algTAll,
    GlobalTheory.InertGenusOne.datum_exists_lattice h2 ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree ReciprocityTheory.ChartRestriction.L1.cm4,
    GlobalTheory.CurveDictionary.curveDict_of_cm h2 ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree ReciprocityTheory.ChartRestriction.L1.cm4⟩

end GlobalTheory.CurveThetaInert
end
