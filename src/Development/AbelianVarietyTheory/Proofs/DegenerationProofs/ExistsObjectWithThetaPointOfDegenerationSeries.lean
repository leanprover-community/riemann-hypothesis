import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.MemOfIsIntegralElem
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionValuesNormsIntegralPositive
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTermsStatement
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPointComplexDegenerationSmall
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCountableModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransportStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.MemPuncturedRingIffPowerSeriesPart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTerms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependenceStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemThetaPointsOfClosureCosetCondition

section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.BddArc

section
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C]

def AbsSumAt (u : C) (f : PowerSeries C) (c : C) : Prop :=
  (Summable fun n => ‖PowerSeries.coeff n f * u ^ n‖) ∧ ∑' n, PowerSeries.coeff n f * u ^ n = c

omit [CompleteSpace C] in
theorem AbsSumAt.const (u a : C) : AbsSumAt u (PowerSeries.C a) a := by
  constructor
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp [PowerSeries.coeff_C, Finset.notMem_singleton.1 hn]
  · rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_C, hn]]
    simp

theorem AbsSumAt.add {u : C} {f g : PowerSeries C} {a b : C} (hf : AbsSumAt u f a) (hg : AbsSumAt u g b) :
    AbsSumAt u (f + g) (a + b) := by
  constructor
  · refine (hf.1.add hg.1).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rw [map_add, add_mul]
    exact norm_add_le _ _
  · rw [← hf.2, ← hg.2, ← hf.1.of_norm.tsum_add hg.1.of_norm]
    simp only [map_add, add_mul]

theorem AbsSumAt.mul {u : C} {f g : PowerSeries C} {a b : C} (hf : AbsSumAt u f a) (hg : AbsSumAt u g b) :
    AbsSumAt u (f * g) (a * b) := by
  have e : ∀ n, PowerSeries.coeff n (f * g) * u ^ n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl h => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
    ring
  constructor
  · simp only [e]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm (f := fun n => PowerSeries.coeff n f * u ^ n)
      (g := fun n => PowerSeries.coeff n g * u ^ n) hf.1 hg.1
  · rw [← hf.2, ← hg.2, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.1 hg.1]
    simp only [e]

open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
private theorem absSumAt_algebraMap (u a : C) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (algebraMap C (PowerSeries C) a) a := by
  have h : (fun n => PowerSeries.coeff n (algebraMap C (PowerSeries C) a) * u ^ n) =
      fun n => if n = 0 then a else 0 := by
    funext n
    rcases n with _ | n <;> simp [PowerSeries.coeff_C]
  refine ⟨?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    rw [congrFun h n, if_neg (by simpa using hn), norm_zero]
  · rw [h]
    simp

open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
private theorem absSumAt_add {u : C} {f g : PowerSeries C} {a b : C}
    (hf : _root_.GlobalTheory.BddArc.AbsSumAt u f a) (hg : _root_.GlobalTheory.BddArc.AbsSumAt u g b) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (f + g) (a + b) := by
  have h : ∀ n, PowerSeries.coeff n (f + g) * u ^ n =
      PowerSeries.coeff n f * u ^ n + PowerSeries.coeff n g * u ^ n := fun n => by
    rw [map_add, add_mul]
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (Summable.add hf.1 hg.1)
    rw [h]
    exact norm_add_le _ _
  · simp_rw [h]
    rw [(hf.1.of_norm).tsum_add hg.1.of_norm, hf.2, hg.2]

open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
private theorem absSumAt_mul {u : C} {f g : PowerSeries C} {a b : C}
    (hf : _root_.GlobalTheory.BddArc.AbsSumAt u f a) (hg : _root_.GlobalTheory.BddArc.AbsSumAt u g b) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (f * g) (a * b) := by
  have h : ∀ n, PowerSeries.coeff n (f * g) * u ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hkl, pow_add]
    ring
  refine ⟨?_, ?_⟩
  · exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hf.1 hg.1).congr fun n => by rw [h]
  · rw [tsum_congr h, ← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.1 hg.1, hf.2, hg.2]

open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
theorem _root_.GlobalTheory.BddArc.AbsSumAt.aeval {u : C} {ι : Type} {f : ι → PowerSeries C} {a : ι → C}
    (h : ∀ i, _root_.GlobalTheory.BddArc.AbsSumAt u (f i) (a i))
    (F : MvPolynomial ι C) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (MvPolynomial.aeval f F) (MvPolynomial.eval a F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.eval_C]
    exact absSumAt_algebraMap u c
  | add p q hp hq =>
    rw [map_add, map_add]
    exact absSumAt_add hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X]
    exact absSumAt_mul hp (h i)

end

end GlobalTheory.BddArc

open scoped BigOperators in
private theorem finite_setOf_bilin_self_le_of_posDef {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : LinearMap.BilinForm ℤ X) (hsymm : ∀ y z, B y z = B z y) (hpos : ∀ y, y ≠ 0 → 0 < B y y) (L : ℤ) :
    {y | B y y ≤ L}.Finite := by
  classical
  set b := Module.Free.chooseBasis ℤ X with hb
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℚ :=
    Matrix.of fun i j => (B (b i) (b j) : ℚ)
  let Bq := Matrix.toBilin' M
  let φ : X → Module.Free.ChooseBasisIndex ℤ X → ℚ := fun y i => (b.repr y i : ℚ)
  have hφ : ∀ y z, ((B y z : ℤ) : ℚ) = Bq (φ y) (φ z) := by
    intro y z
    rw [Matrix.toBilin'_apply]
    conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Int.cast_sum,
      Int.cast_mul, Finset.mul_sum, M, φ, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hBsymm : LinearMap.IsSymm Bq := by
    refine LinearMap.isSymm_iff_eq_flip.2 (LinearMap.ext₂ fun x y => ?_)
    rw [LinearMap.flip_apply, Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [M, Matrix.of_apply, hsymm (b i) (b j)]
    ring
  have hqpos : ∀ v, v ≠ 0 → 0 < Bq v v := by
    intro v hv
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ v
    choose n hn using fun i => hd i (Finset.mem_univ i)
    have hd0 : ((d : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    set y : X := b.equivFun.symm n
    have hy : φ y = ((d : ℤ) : ℚ) • v := by
      funext i
      have := hn i
      simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at this
      have hr : b.repr y i = n i := by rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
      simp only [φ, Pi.smul_apply, smul_eq_mul, hr]
      exact this
    have hy0 : y ≠ 0 := by
      intro h
      apply hv
      have h2 : ((d : ℤ) : ℚ) • v = 0 := by rw [← hy, h]; funext i; simp [φ]
      exact (smul_eq_zero.1 h2).resolve_left hd0
    have h1 := hpos y hy0
    have h2 : (0 : ℚ) < Bq (φ y) (φ y) := by rw [← hφ]; exact_mod_cast h1
    rw [hy] at h2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
    have h3 : 0 < ((d : ℤ) : ℚ) * ((d : ℤ) : ℚ) := mul_self_pos.2 hd0
    nlinarith
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, hw⟩ := LinearMap.BilinForm.exists_orthogonal_basis hBsymm
  have hexp : ∀ v, Bq v v = ∑ k, (w.repr v k) ^ 2 * Bq (w k) (w k) := by
    intro v
    conv_lhs => rw [← w.sum_repr v]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · ring
    · intro l _ hlk
      rw [hw hlk]
      ring
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hdpos : ∀ k, 0 < Bq (w k) (w k) := fun k => hqpos _ (w.ne_zero k)
  set A : ℚ := ∑ k, max 1 ((L : ℚ) / Bq (w k) (w k)) with hAdef
  set T : ℚ := ∑ i, A * ∑ k, |w k i| with hTdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun k _ => le_trans zero_le_one (le_max_left _ _)
  have hcoord : ∀ v, Bq v v ≤ L → ∀ i, |v i| ≤ T := by
    intro v hv i
    have hc : ∀ k, |w.repr v k| ≤ A := by
      intro k
      have h1 : (w.repr v k) ^ 2 * Bq (w k) (w k) ≤ L := by
        rw [hexp] at hv
        refine le_trans ?_ hv
        exact Finset.single_le_sum (f := fun k => (w.repr v k) ^ 2 * Bq (w k) (w k))
          (fun k _ => mul_nonneg (sq_nonneg _) (hdpos k).le) (Finset.mem_univ k)
      have h2 : |w.repr v k| ≤ max 1 ((L : ℚ) / Bq (w k) (w k)) := by
        rcases le_or_gt (|w.repr v k|) 1 with h | h
        · exact h.trans (le_max_left _ _)
        · refine le_trans ?_ (le_max_right _ _)
          rw [le_div_iff₀ (hdpos k)]
          have h3 : |w.repr v k| ≤ (w.repr v k) ^ 2 := by rw [← sq_abs]; nlinarith
          nlinarith [hdpos k]
      refine h2.trans ?_
      exact Finset.single_le_sum (f := fun k => max 1 ((L : ℚ) / Bq (w k) (w k)))
        (fun k _ => le_trans zero_le_one (le_max_left _ _)) (Finset.mem_univ k)
    have hvi : v i = ∑ k, w.repr v k * w k i := by
      conv_lhs => rw [← w.sum_repr v]
      simp [Finset.sum_apply]
    calc |v i| ≤ ∑ k, |w.repr v k * w k i| := by rw [hvi]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, A * |w k i| := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc k) (abs_nonneg _)
      _ = A * ∑ k, |w k i| := (Finset.mul_sum _ _ _).symm
      _ ≤ T := Finset.single_le_sum (f := fun i => A * ∑ k, |w k i|)
          (fun i _ => mul_nonneg hA (Finset.sum_nonneg fun k _ => abs_nonneg _)) (Finset.mem_univ i)
  let ψ : X → Module.Free.ChooseBasisIndex ℤ X → ℤ := fun y i => b.repr y i
  have hψ : Function.Injective ψ := by
    intro y z h
    apply b.repr.injective
    ext i
    exact congrFun h i
  refine ((Set.finite_Icc (fun _ => -⌈T⌉) (fun _ => ⌈T⌉)).preimage hψ.injOn).subset ?_
  intro y hy
  have hy' : Bq (φ y) (φ y) ≤ L := by rw [← hφ]; exact_mod_cast hy
  have h := hcoord _ hy'
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h4 := (abs_le.1 ((h i).trans (Int.le_ceil T))).1
    show -⌈T⌉ ≤ b.repr y i
    simp only [φ] at h4
    exact_mod_cast h4
  · have h4 := (abs_le.1 ((h i).trans (Int.le_ceil T))).2
    show b.repr y i ≤ ⌈T⌉
    simp only [φ] at h4
    exact_mod_cast h4

open scoped BigOperators in
private theorem injective_add_nsmul_of_ne_zero {X : Type} [AddCommGroup X] [Module.Free ℤ X] (a : X) {m : ℕ}
    (hm : m ≠ 0) : Function.Injective (fun χ : X => a + m • χ) := by
  intro x y h
  have h' : m • x = m • y := add_left_cancel h
  apply (Module.Free.chooseBasis ℤ X).repr.injective
  ext i
  have := congrArg (fun z => (Module.Free.chooseBasis ℤ X).repr z i) h'
  simp only [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (by exact_mod_cast hm) this

open scoped BigOperators in
private theorem tsum_subtype_eq_finsum_mem_of_finite {X M : Type} [AddCommMonoid M] [TopologicalSpace M]
    [T2Space M] (S : Set X) (hS : S.Finite) (g : X → M) : ∑' b : S, g b = ∑ᶠ x ∈ S, g x := by
  have h := Finset.tsum_subtype' hS.toFinset g
  rw [hS.coe_toFinset] at h
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, h]

open scoped BigOperators in
private theorem absSumAt_arcTx_twist_tx {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] (N : _root_.GlobalTheory.Ex.NumD C) {k : ℕ}
    (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k) (hodd : Odd m)
    (p : N.QT (m ^ 2))
    (hbd : ∀ χ, ‖N.txT m p χ‖ ≤ 1) (u : Cˣ) (hu : ‖(u : C)‖ < 1) :
    _root_.GlobalTheory.BddArc.AbsSumAt (u : C)
      (N.arcTx β.be m p)
      ((N.twist β u).tx m (N.twQ β u hm p)) := by
  classical
  set a : N.X := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with ha
  set q : N.X → ℤ := fun χ =>
    β.be (a + m • χ) (a + m • χ) / (2 * (m : ℤ) ^ 2) with hq
  have hm0 : m ≠ 0 := hodd.pos.ne'
  have hden : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
  have hq0 : ∀ χ, 0 ≤ q χ := by
    intro χ
    refine Int.ediv_nonneg ?_ hden.le
    by_cases h : a + m • χ = 0
    · rw [h]; simp
    · exact (β.pos _ h).le
  have hfin : ∀ K : ℤ, {χ | q χ ≤ K}.Finite := by
    intro K
    refine ((finite_setOf_bilin_self_le_of_posDef β.be β.symm β.pos
      ((K + 1) * (2 * (m : ℤ) ^ 2))).preimage (injective_add_nsmul_of_ne_zero a hm0).injOn).subset ?_
    intro χ hχ
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hχ ⊢
    have h1 := Int.lt_mul_ediv_self_add
      (x := β.be (a + m • χ) (a + m • χ)) hden
    have h2 : 2 * (m : ℤ) ^ 2 * (β.be (a + m • χ) (a + m • χ) / (2 * (m : ℤ) ^ 2))
        ≤ 2 * (m : ℤ) ^ 2 * K := mul_le_mul_of_nonneg_left hχ hden.le
    linarith
  have hfinS : ∀ n : ℕ, {χ | q χ = n}.Finite := fun n =>
    (hfin n).subset fun χ hχ => le_of_eq hχ
  set Q : N.X → ℕ := fun χ => (q χ).toNat with hQdef
  have hQ : ∀ χ, ((Q χ : ℕ) : ℤ) = q χ := fun χ => Int.toNat_of_nonneg (hq0 χ)
  have hpow : ∀ χ, ((u ^ q χ : Cˣ) : C) = (u : C) ^ Q χ := by
    intro χ
    conv_lhs => rw [← hQ χ]
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  set f : N.X → C := fun χ => (u : C) ^ Q χ * N.txT m p χ with hf
  have htw : (N.twist β u).tx m (N.twQ β u hm p)
      = ∑' χ, f χ := by
    unfold _root_.GlobalTheory.Ex.NumD.tx
    refine tsum_congr fun χ => ?_
    rw [N.twist_txT β u m hm hodd p χ]
    exact congrArg (· * N.txT m p χ) (hpow χ)
  have hcoeff' : ∀ n : ℕ, PowerSeries.coeff n (N.arcTx β.be m p)
      = ∑ᶠ χ ∈ {χ | q χ = n}, N.txT m p χ := by
    intro n
    unfold _root_.GlobalTheory.Ex.NumD.arcTx
    rw [PowerSeries.coeff_mk]
    rfl
  have hcn : ∀ n : ℕ,
      ‖PowerSeries.coeff n (N.arcTx β.be m p)‖ ≤ 1 := by
    intro n
    rw [hcoeff', finsum_mem_eq_finite_toFinset_sum _ (hfinS n)]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun χ _ => hbd χ
  have hnorm : ∀ χ, ‖f χ‖ ≤ ‖(u : C)‖ ^ Q χ := fun χ => by
    rw [hf, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hbd χ)
  have hQtend : Filter.Tendsto Q Filter.cofinite Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun K => Filter.eventually_cofinite.2 ?_
    refine (hfin K).subset fun χ hχ => ?_
    simp only [Set.mem_setOf_eq, not_le] at hχ ⊢
    have := hQ χ
    omega
  have hsum : Summable f := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun χ => norm_nonneg _) hnorm
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hu).comp hQtend)
  have hcoeff : ∀ n : ℕ, ∑' b : ↑(Q ⁻¹' {n}), f b =
      PowerSeries.coeff n (N.arcTx β.be m p) * (u : C) ^ n := by
    intro n
    have hset : Q ⁻¹' {n} = {χ | q χ = n} := by
      ext χ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      have := hQ χ
      omega
    have hterm : ∀ b : ↑(Q ⁻¹' {n}), f b = (u : C) ^ n * N.txT m p b := by
      intro b
      have hb : Q b = n := b.2
      rw [hf]
      simp only [hb]
    rw [tsum_congr hterm, tsum_mul_left, hset,
      tsum_subtype_eq_finsum_mem_of_finite _ (hfinS n), hcoeff', mul_comm]
  have hfib := hsum.hasSum.tsum_fiberwise Q
  rw [show (fun n => ∑' b : ↑(Q ⁻¹' {n}), f b) = fun n =>
      PowerSeries.coeff n (N.arcTx β.be m p) * (u : C) ^ n
      from funext hcoeff] at hfib
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (norm_nonneg _) hu)
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hcn n)
  · rw [htw]
    exact hfib.tsum_eq

open scoped BigOperators in

theorem _root_.GlobalTheory.eval_twist_tx_eq_zero_of_aeval_arcTx : ∀ (C : Type) [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] (N : _root_.GlobalTheory.Ex.NumD C) (k : ℕ)
    (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m →
    ∀ (ι : Type) (p : ι → N.QT (m ^ 2)),
    (∀ i χ, ‖N.txT m (p i) χ‖ ≤ 1) → ∀ (F : MvPolynomial ι C),
    MvPolynomial.aeval (fun i => N.arcTx β.be m (p i)) F = 0 →
    ∀ u : Cˣ, ‖(u : C)‖ < 1 →
    MvPolynomial.eval (fun i => (N.twist β u).tx m
      (N.twQ β u hm (p i))) F = 0 := by
  intro C _ _ _ N k β m hm hodd ι p hbd F hF u hu
  have h := _root_.GlobalTheory.BddArc.AbsSumAt.aeval (u := (u : C))
    (fun i => absSumAt_arcTx_twist_tx N β m hm hodd (p i) (hbd i) u hu) F
  rw [hF] at h
  rw [← h.2]
  simp
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory

theorem isAlgebraic_int_eval₂Hom_of_isAlgebraic {σ : Type} (y : σ → ℂ)
    (hy : ∀ i, IsAlgebraic ℚ (y i)) (c : MvPolynomial σ ℤ) :
    IsAlgebraic ℤ (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c) := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ]
  induction c using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (a : ℚ)
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp => rw [map_mul, MvPolynomial.eval₂Hom_X']; exact hp.mul (hy i)

theorem exists_ringHom_complex_of_countable_of_relations :
    ∀ (F : Type) [Field F] [CharZero F] [Countable F] (x : Fin 2 → F) (y : Fin 2 → ℂ), (∀ i, IsAlgebraic ℚ (y i)) → (∀ c : MvPolynomial (Fin 2) ℤ, MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c = 0 → MvPolynomial.eval₂Hom (Int.castRingHom F) x c = 0) → ∃ f : F →+* ℂ, ∀ i, f (x i) = y i := by
  intro F _ _ _ x y hy hrel
  set ey := MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y with hey
  set ex := MvPolynomial.eval₂Hom (Int.castRingHom F) x with hex
  let R := MvPolynomial (Fin 2) ℤ ⧸ RingHom.ker ey
  have hprime : (RingHom.ker ey).IsPrime := RingHom.ker_isPrime ey
  have : IsDomain R := Ideal.Quotient.isDomain _
  let em : R →+* ℂ := RingHom.kerLift ey
  have hem : Function.Injective em := RingHom.kerLift_injective ey
  let β : R →+* F := Ideal.Quotient.lift _ ex fun c hc => hrel c hc
  have halg : ∀ r : R, IsAlgebraic ℤ r := by
    intro r
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine (isAlgebraic_algHom_iff em.toIntAlgHom hem).1 ?_
    exact isAlgebraic_int_eval₂Hom_of_isAlgebraic y hy c
  have hβ : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker β) h0 hr (halg r) ?_
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker] at hn
    simpa using hn
  have hc : Countable R := hβ.countable
  let : Algebra R F := β.toAlgebra
  let : Algebra R ℂ := em.toAlgebra
  have : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective R F).2 hβ
  have : FaithfulSMul R ℂ := (faithfulSMul_iff_algebraMap_injective R ℂ).2 hem
  obtain ⟨j⟩ := nonempty_algHom_complex_of_countable R F
  refine ⟨j.toRingHom, fun i => ?_⟩
  have h := j.commutes (Ideal.Quotient.mk _ (MvPolynomial.X i))
  have h1 : algebraMap R F (Ideal.Quotient.mk _ (MvPolynomial.X i)) = x i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom F) x i
  have h2 : algebraMap R ℂ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = y i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom ℂ) y i
  rw [h1, h2] at h
  exact h

end GlobalTheory
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ArcExt
open GlobalTheory.TorusExt

theorem exists_arcF_over : Laws → BrGtSt → BrWpSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), (∀ x, f (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ A : ArcF D R F, ∃ A' : ArcF D R F', A'.D₀ = A.D₀ ∧ A.Over f A' := by
  intro hL hGt hWp E _ _ _ H D R _ _ F F' _ _ _ _ _ _ _ f hf₀ A
  have hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext hf₀
  obtain ⟨J', hg, hJ₀⟩ := exists_gauge f A.D₀.P.isLB A.ν.good
  obtain ⟨N', ν', e₁, hth⟩ := GlobalTheory.GaugeValues.exists_numOf hL R A.D₀ A.even A.bimult F' J' hg A.ν.th A.ν.th_gen
  have hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = A.ν.J ψ := e₁ ▸ hJ₀
  have G := (hGt R A.D₀ A.even A.bimult F A.N A.ν).2.2.2.2
  have G' := (hGt R A.D₀ A.even A.bimult F' N' ν').2.2.2.2
  let I := numHom f hf A.ν ν' hJ hth
  have hw : ∀ k, 1 ≤ k → ∀ (p p' : QkPt A.D₀ F k) (z : F), WeilQkIs A.D₀ F k p p' z →
      WeilQkIs A.D₀ F' k (qkExt A.bimult f hf p) (qkExt A.bimult f hf p') (f z) := fun k hk p p' z h => by
    obtain ⟨q, hq, -⟩ := (G k).1 p
    obtain ⟨q', hq', -⟩ := (G k).1 p'
    obtain ⟨r, hr, -⟩ := (G' k).1 (qkExt A.bimult f hf p)
    obtain ⟨r', hr', -⟩ := (G' k).1 (qkExt A.bimult f hf p')
    have a := numHom_qPt f hf A.bimult A.ν ν' hJ hth hq hr
    have a' := numHom_qPt f hf A.bimult A.ν ν' hJ hth hq' hr'
    rw [hWp R A.D₀ A.even A.bimult F' N' ν' k hk _ _ _ _ _ hr hr',
      (GlobalTheory.T.hom_transport_alt F F' f A.N N' I).2.2.2.1 k q q' r r' a.1 a.2 a'.1 a'.2,
      (hWp R A.D₀ A.even A.bimult F A.N A.ν k hk _ _ _ _ _ hq hq').1 h]
    rfl
  choose q' hq' using fun (n : ℕ) (a : D.La) => ((G' n).1 (qkExt A.bimult f hf (A.I.ev n a))).exists
  refine ⟨{ D₀ := A.D₀, oa := A.oa, even := A.even, bimult := A.bimult, w0 := A.w0, ρ := f A.ρ
            ρ_sq := by rw [← map_pow, A.ρ_sq, map_neg]; simp
            det := fun σ => ?_
            I := tateExt f hf A.bimult hL A.I hw, N := N', ν := ν', q := q', hq := hq', closed := inferInstance },
    rfl, I, rfl, fun _ _ => rfl, fun a y => ?_, fun n a _ => ?_⟩
  · obtain ⟨τ, rfl⟩ := DetExtend.exists_factor f σ
    obtain ⟨n, h₁, h₂⟩ := A.det τ
    have := A.D₀.P.isAb.smooth
    refine ⟨n, ?_, h₂.trans (by
      by_cases h : τ H.rt = A.ρ
      · rw [if_pos h, if_pos (show f.comp τ H.rt = f A.ρ from congrArg f h)]
      · rw [if_neg h, if_neg (show ¬ f.comp τ H.rt = f A.ρ from fun e => h (f.injective e))])⟩
    have e : spMap ((algebraMap (FractionRing R) F').comp (algebraMap R _)) =
        spMap f ≫ spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) := by
      rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hf]
    rw [e]
    exact (DetExtend.lieMult_extend f _ _ τ n).2 h₁
  · refine ν'.eX.injective ((eX_numHom f hf A.ν ν' hJ hth _).trans ?_)
    show A.ν.eX (A.ν.eX.symm _) = ν'.eX (ν'.eX.symm (a • ν'.eX (I.e y)))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, eX_numHom]
  · have h := numHom_qPt f hf A.bimult A.ν ν' hJ hth (A.hq n a) (hq' n a)
    exact ⟨q' n a, h.1, h.2, (N'.qEq_equivalence n).refl _⟩

end GlobalTheory.ArcExt
end
end

section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators Topology

namespace GlobalTheory.Ex.ArcForm

theorem hasSum_regroup {X : Type} (e : X → ℤ) (h0 : ∀ χ, 0 ≤ e χ) (hf : ∀ n : ℤ, {χ | e χ = n}.Finite)
    (a : X → ℂ) (u x : ℂ) (h : HasSum (fun χ => u ^ e χ * a χ) x) :
    HasSum (fun n : ℕ => (∑ᶠ (χ : X) (_ : e χ = n), a χ) * u ^ n) x := by
  have h1 := h.tsum_fiberwise fun χ => (e χ).toNat
  refine h1.congr_fun fun n => ?_
  have hs : (fun χ => (e χ).toNat) ⁻¹' {n} = ((hf n).toFinset : Set X) := by
    ext χ
    have := h0 χ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    omega
  rw [hs, Finset.tsum_subtype' (hf n).toFinset fun χ => u ^ e χ * a χ]
  have h2 : (∑ᶠ (χ : X) (_ : e χ = n), a χ) = ∑ χ ∈ (hf n).toFinset, a χ :=
    finsum_mem_eq_finite_toFinset_sum a (hf n)
  rw [h2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have : e χ = n := by simpa using hχ
  rw [this, zpow_natCast, mul_comm]

theorem finite_fibre {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ≠ 0)
    (y : N.X) (n : ℤ) : {χ : N.X | β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = n}.Finite := by
  have h := GlobalTheory.ClassMin.finite_sublevel
    (GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef β.symm β.pos) (((n + 1) * (2 * m ^ 2) : ℤ) / 2 : ℝ)
  have hinj : Function.Injective fun χ : N.X => y + m • χ := fun a b hab =>
    smul_right_injective N.X (Int.natCast_ne_zero.2 hm) (by
      simpa only [natCast_zsmul] using add_left_cancel hab)
  refine (h.preimage hinj.injOn).subset fun χ hχ => ?_
  have hχ' : β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = n := hχ
  have hpos : (0 : ℤ) < 2 * m ^ 2 := by positivity
  have h2 := Int.lt_ediv_add_one_mul_self (β.be (y + m • χ) (y + m • χ)) hpos
  rw [hχ'] at h2
  simp only [Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.ClassMin.ofIntBilin_apply]
  have h3 : ((β.be (y + m • χ) (y + m • χ) : ℤ) : ℝ) ≤ (((n + 1) * (2 * m ^ 2) : ℤ) : ℝ) := by
    exact_mod_cast h2.le
  linarith

theorem exponent_nonneg {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (m : ℕ) (y : N.X) :
    0 ≤ β.be y y / (2 * m ^ 2) := by
  refine Int.ediv_nonneg ?_ (by positivity)
  by_cases h : y = 0
  · simp [h]
  · exact (β.pos y h).le

theorem hasSum_arcTx (N : NumD ℂ) {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k) (ho : Odd m)
    (p : N.QT (m ^ 2)) (u : ℂˣ) (h : Summable fun χ => ‖(N.twist β u).txT m (N.twQ β u hm p) χ‖) :
    HasSum (fun n => PowerSeries.coeff n (N.arcTx β.be m p) * (u : ℂ) ^ n)
      ((N.twist β u).tx m (N.twQ β u hm p)) := by
  have h1 : HasSum (fun χ : N.X => (N.twist β u).txT m (N.twQ β u hm p) χ)
      ((N.twist β u).tx m (N.twQ β u hm p)) := h.of_norm.hasSum
  have h2 := hasSum_regroup _ (fun χ => exponent_nonneg β m (p.1.1.toAdd + m • χ))
    (finite_fibre β ho.pos.ne' p.1.1.toAdd) (N.txT m p) u _ (h1.congr_fun fun χ => by
      rw [(GlobalTheory.Ex.twist_terms ℂ N k β u m hm ho p χ).1, Units.val_zpow_eq_zpow_val])
  simpa only [NumD.arcTx, PowerSeries.coeff_mk] using h2

theorem aeval_eq_zero {ι : Type} (f : ι → PowerSeries ℂ) (F : MvPolynomial ι ℂ) {ε : ℝ} (hε : 0 < ε)
    (v : ℂˣ → ι → ℂ) (hs : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → ∀ i,
      HasSum (fun n => PowerSeries.coeff n (f i) * (u : ℂ) ^ n) (v u i))
    (hF : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → MvPolynomial.eval (v u) F = 0) : MvPolynomial.aeval f F = 0 := by
  have hmem : ∀ i, f i ∈ GlobalTheory.Conv.discSeries ε := fun i u hu => by
    rcases eq_or_ne u 0 with rfl | h0
    · exact summable_of_ne_finset_zero (s := {0}) fun n hn => by
        simp [show n ≠ 0 by simpa using hn]
    · exact (hs (Units.mk0 u h0) hu i).summable
  set G : GlobalTheory.Conv.discSeries ε := MvPolynomial.aeval (fun i => (⟨f i, hmem i⟩ : GlobalTheory.Conv.discSeries ε)) F with hG
  have hGv : (G : PowerSeries ℂ) = MvPolynomial.aeval f F :=
    MvPolynomial.comp_aeval_apply _ (GlobalTheory.Conv.discSeries ε).val F
  rw [← hGv]
  refine GlobalTheory.Conv.eq_zero_of_frequently_sum_eq_zero (GlobalTheory.Conv.discSeries_le_convSeries hε G.2)
    (Filter.Eventually.frequently ?_)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hε)] with u h0 hu
  have h0' : u ≠ 0 := h0
  have hu' : ‖u‖ < ε := by simpa using hu
  rw [← GlobalTheory.Conv.evalDisc_apply hu', hG, MvPolynomial.comp_aeval_apply, ← hF (Units.mk0 u h0') hu',
    MvPolynomial.aeval_eq_eval]
  congr 2
  funext i
  exact (hs (Units.mk0 u h0') hu' i).tsum_eq

theorem aeval_arcTx_eq_zero : ∀ (N : NumD ℂ) (k : ℕ) (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (ι : Type) (p : ι → N.QT (m ^ 2)) (F : MvPolynomial ι ℂ) (ε : ℝ), 0 < ε → (∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ i, Summable fun χ => ‖(N.twist β u).txT m (N.twQ β u hm (p i)) χ‖) ∧ MvPolynomial.eval (fun i => (N.twist β u).tx m (N.twQ β u hm (p i))) F = 0) → MvPolynomial.aeval (fun i => N.arcTx β.be m (p i)) F = 0 :=
  fun N _ β m hm ho _ p F _ hε h =>
    aeval_eq_zero _ F hε (fun u i => (N.twist β u).tx m (N.twQ β u hm (p i)))
      (fun u hu i => hasSum_arcTx N β hm ho (p i) u ((h u hu).1 i)) fun u hu => (h u hu).2

end GlobalTheory.Ex.ArcForm
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ArcIdentity

theorem exists_form {O O' : Type} [CommRing O] [CommRing O'] {N : NumD O} {N' : NumD O'} (e : N.X ≃+ N'.X) {k : ℕ}
    (β : N'.Form k) : ∃ b : N.Form k, ∀ y z, b.be y z = β.be (e y) (e z) := by
  refine ⟨⟨β.be.compl₁₂ e.toIntLinearEquiv.toLinearMap e.toIntLinearEquiv.toLinearMap, fun y z => ?_,
    fun y hy => ?_, fun y z => ?_⟩, fun y z => ?_⟩
  · simpa using β.symm (e y) (e z)
  · simpa using β.pos (e y) (fun h => hy (e.injective (by rw [h, map_zero])))
  · simpa using β.dvd (e y) (e z)
  · simp

theorem arcTx_qEq {O : Type} [CommRing O] (N : NumD O) (be : LinearMap.BilinForm ℤ N.X) {m : ℕ} (ho : Odd m)
    {p p' : N.QT (m ^ 2)} (h : N.QEq p p') : N.arcTx be m p' = N.arcTx be m p := by
  obtain ⟨z, h1, h2⟩ := h
  ext n
  simp only [NumD.arcTx, PowerSeries.coeff_mk]
  conv_rhs => rw [← finsum_comp_equiv (Equiv.addRight (m • z))]
  refine finsum_congr fun χ => ?_
  have hx : p'.1.1.toAdd + m • χ = p.1.1.toAdd + m • (χ + m • z) := by
    rw [h1, smul_add, smul_smul, ← pow_two]
    abel
  simp only [Equiv.coe_addRight, hx, (GlobalTheory.T.thetaConstantTerm_representative_dependence O N m ho p p' χ).1 z h1 h2]

private theorem map_finsum_of_injective' {α M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (φ : M →+ M')
    (hφ : Function.Injective φ) (g : α → M) : φ (∑ᶠ a, g a) = ∑ᶠ a, φ (g a) := by
  by_cases h : (Function.support g).Finite
  · exact map_finsum φ h
  · have hs : Function.support (fun a => φ (g a)) = Function.support g := by
      ext a
      simp only [Function.mem_support, ne_eq]
      exact ⟨fun h1 h2 => h1 (by rw [h2, map_zero]), fun h1 h2 => h1 (hφ (by rw [h2, map_zero]))⟩
    have h' : (Function.support (fun a => φ (g a))).Infinite := by
      rw [hs]
      exact h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', map_zero]

private theorem unit_mul_map_finsum {α F F' : Type*} [Field F] [Field F'] (f : F →+* F') (c : F'ˣ) (g : α → F) :
    (c : F') * f (∑ᶠ a, g a) = ∑ᶠ a, (c : F') * f (g a) := by
  refine map_finsum_of_injective' ((AddMonoidHom.mulLeft (c : F')).comp f.toAddMonoidHom) ?_ g
  intro a b hab
  have hab' : (c : F') * f a = (c : F') * f b := hab
  exact f.injective (mul_left_cancel₀ c.ne_zero hab')

private theorem unit_mul_map_finsum_prop {F F' : Type*} [Field F] [Field F'] (f : F →+* F') (c : F'ˣ) (P : Prop)
    (x : F) : (c : F') * f (∑ᶠ (_ : P), x) = ∑ᶠ (_ : P), (c : F') * f x := by
  classical
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp

theorem arcTx_hom {F F' : Type} [Field F] [Field F'] {f : F →+* F'} {N : NumD F} {N' : NumD F'} (I : NumD.Hom f N N')
    (be : LinearMap.BilinForm ℤ N.X) (be' : LinearMap.BilinForm ℤ N'.X) (hb : ∀ y z, be y z = be' (I.e y) (I.e z))
    {m : ℕ} (ho : Odd m) {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h1 : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (h2 : I.Rel p.1.2 p'.1.2) :
    N'.arcTx be' m p' = PowerSeries.C (I.lam : F') * PowerSeries.map f (N.arcTx be m p) := by
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  simp only [NumD.arcTx, PowerSeries.coeff_mk, unit_mul_map_finsum f I.lam, unit_mul_map_finsum_prop f I.lam]
  conv_lhs => rw [← finsum_comp_equiv I.e.toEquiv]
  refine finsum_congr fun χ => ?_
  have hx : p'.1.1.toAdd + m • I.e χ = I.e (p.1.1.toAdd + m • χ) := by
    rw [h1, map_add, map_nsmul]
  have hχ : I.e.toEquiv χ = I.e χ := rfl
  rw [hχ]
  simp only [hx, ← hb, I.txT_eq ho p p' h1 h2 χ]

private theorem eval2_smul_of_isHomogeneous {J S T : Type*} [CommSemiring S] [CommSemiring T] (g : S →+* T) (c : T)
    (w : J → T) {G : MvPolynomial J S} {d : ℕ} (hG : G.IsHomogeneous d) :
    MvPolynomial.eval₂ g (fun x => c * w x) G = c ^ d * MvPolynomial.eval₂ g w G := by
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hG.degree_eq_sum_deg_support hs]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem aeval_smul_map {J S F F' : Type} [CommRing S] [CommRing F] [CommRing F'] (f : F →+* F') (c : S →+* F)
    (l : F') (v : J → PowerSeries F) {G : MvPolynomial J S} {d : ℕ} (hG : G.IsHomogeneous d) :
    MvPolynomial.aeval (fun x => PowerSeries.C l * PowerSeries.map f (v x)) (MvPolynomial.map (f.comp c) G) =
      PowerSeries.C l ^ d * PowerSeries.map f (MvPolynomial.aeval v (MvPolynomial.map c G)) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map,
    eval2_smul_of_isHomogeneous _ _ (fun x => PowerSeries.map f (v x)) hG, MvPolynomial.eval₂_comp_left]
  have hr : (PowerSeries.map f).comp ((algebraMap F (PowerSeries F)).comp c) =
      (algebraMap F' (PowerSeries F')).comp (f.comp c) :=
    RingHom.ext fun a => by simp [PowerSeries.map_C]
  rw [hr]
  rfl

theorem cf_comp {F F' : Type} [CommRing F] [CommRing F'] (f : F →+* F') (a b : F) :
    cf (f a) (f b) = f.comp (cf a b) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    fin_cases i <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
  {R' : Type} [CommRing R'] [IsDomain R'] {F' : Type} [Field F'] [Algebra (FractionRing R') F']

theorem over_iff {f : F →+* F'} {A : ArcF D R F} {A' : ArcF D R' F'} (h : A.Over f A') :
    ∃ e : A.N.X ≃+ A'.N.X, ∀ (k : ℕ) (β : A.N.Form k) (β' : A'.N.Form k), (∀ y z, β.be y z = β'.be (e y) (e z)) →
      (A.Bal β ↔ A'.Bal β') ∧ ∀ m : ℕ, Odd m → ∀ (G : MvPolynomial D.La (MvPolynomial (Fin 2) ℤ)) (d : ℕ),
        G.IsHomogeneous d →
        (MvPolynomial.aeval (fun x => A.N.arcTx β.be m (A.q _ x))
            (MvPolynomial.map (cf (A.I.ζ (m ^ 2) : F) A.ρ) G) = 0 ↔
          MvPolynomial.aeval (fun x => A'.N.arcTx β'.be m (A'.q _ x))
            (MvPolynomial.map (cf (A'.I.ζ (m ^ 2) : F') A'.ρ) G) = 0) := by
  obtain ⟨I, hρ, hζ, hact, hq⟩ := h
  refine ⟨I.e, fun k β β' hbe => ⟨?_, fun m hm G d hG => ?_⟩⟩
  · constructor
    · intro hB a y' z'
      obtain ⟨y, rfl⟩ := I.e.surjective y'
      obtain ⟨z, rfl⟩ := I.e.surjective z'
      have h1 := hB a y z
      rw [hbe, hbe, hact, hact] at h1
      exact h1
    · intro hB a y z
      rw [hbe, hbe, hact, hact]
      exact hB _ _ _
  · have hpos : 0 < m ^ 2 := pow_pos hm.pos 2
    have hv : ∀ x, A'.N.arcTx β'.be m (A'.q _ x) =
        PowerSeries.C (I.lam : F') * PowerSeries.map f (A.N.arcTx β.be m (A.q (m ^ 2) x)) := by
      intro x
      obtain ⟨p', h1, h2, h3⟩ := hq (m ^ 2) x hpos
      rw [arcTx_qEq A'.N β'.be hm h3]
      exact arcTx_hom I β.be β'.be hbe hm h1 h2
    have hcf : cf (A'.I.ζ (m ^ 2) : F') A'.ρ = f.comp (cf (A.I.ζ (m ^ 2) : F) A.ρ) := by
      rw [← hρ, ← hζ _ hpos, cf_comp]
    simp only [hv, hcf]
    rw [aeval_smul_map f (cf (A.I.ζ (m ^ 2) : F) A.ρ) (I.lam : F') (fun x => A.N.arcTx β.be m (A.q (m ^ 2) x)) hG]
    have hC : PowerSeries.C (I.lam : F') ^ d ≠ 0 :=
      pow_ne_zero _ ((map_ne_zero_iff _ PowerSeries.C_injective).mpr I.lam.ne_zero)
    constructor
    · intro h0
      rw [h0, map_zero, mul_zero]
    · intro h0
      have h0' := (mul_eq_zero.mp h0).resolve_left hC
      exact PowerSeries.map_injective f f.injective (by rw [h0', map_zero])

theorem aeval_arcTx_eq_zero_of_vanishC : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (A : ArcF D R F) (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ m : ℕ, m ^ 2 ∣ k → Odd m → Compat H (m ^ 2) (A.I.ζ (m ^ 2) : F) A.ρ → ∀ G, VanishC D m G → MvPolynomial.aeval (fun x => A.N.arcTx β.be m (A.q _ x)) (MvPolynomial.map (cf (A.I.ζ (m ^ 2) : F) A.ρ) G) = 0 := by
  intro hHV h6 hU hE hT hEnd hTU
  have hHV' := hHV
  obtain ⟨⟨hL, hL2, -⟩, -⟩ := hHV'
  have hGt := GlobalTheory.Ex.GtValues.points_correspond
  have hWp := GlobalTheory.WeilValues.weil_eq_values hGt (GlobalTheory.Ex.brFam hL hL2)
  have hC4400 := GlobalTheory.T.exists_thetaPoint_complexDegeneration_small hHV h6 hU hE hT hEnd hTU
  have hdown := GlobalTheory.FieldPull.exists_countable_model hL hGt hWp
  have hup := GlobalTheory.ArcExt.exists_arcF_over hL hGt hWp
  unfold AllD at hC4400 hdown hup ⊢
  intro E _ _ _ H D R _ _ F _ _ _ _ A k β hB m hmk hm hC G hV
  obtain ⟨-, ⟨d, hG⟩, hVan⟩ := hV
  have hpos : 0 < m ^ 2 := pow_pos hm.pos 2
  obtain ⟨R₁, F₁, _, _, _, _, _, _, f, A₁, hA₁⟩ := hdown E H D R F A
  haveI : CharZero F₁ := A₁.charZero
  obtain ⟨e₁, he₁⟩ := over_iff hA₁
  obtain ⟨β₁, hβ₁⟩ := exists_form e₁ β
  have h1 := he₁ k β₁ β hβ₁
  rw [← h1.2 m hm G d hG]
  obtain ⟨I₁, hρ₁, hζ₁, _, _⟩ := hA₁
  have hC₁ : Compat H (m ^ 2) (A₁.I.ζ (m ^ 2) : F₁) A₁.ρ := by
    intro c hc
    have h0 := hC c hc
    rw [← hρ₁, ← hζ₁ _ hpos, cf_comp, RingHom.comp_apply] at h0
    exact f.injective (by rw [h0, map_zero])
  have halg : ∀ i, IsAlgebraic ℚ (![zeta (m ^ 2), H.rt0] i) := by
    intro i
    fin_cases i
    · show IsAlgebraic ℚ (zeta (m ^ 2))
      have hz : IsPrimitiveRoot (zeta (m ^ 2)) (m ^ 2) := by
        unfold zeta
        exact Complex.isPrimitiveRoot_exp _ hpos.ne'
      refine IsIntegral.isAlgebraic (IsIntegral.of_pow hpos ?_)
      rw [hz.pow_eq_one]
      exact isIntegral_one
    · show IsAlgebraic ℚ H.rt0
      refine IsIntegral.isAlgebraic (IsIntegral.of_pow (n := 2) two_pos ?_)
      rw [H.sqrt_neg_disc_sq]
      have hd := isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := -(H.d : ℚ))
      simpa using hd
  obtain ⟨g, hg⟩ := GlobalTheory.exists_ringHom_complex_of_countable_of_relations F₁
    ![(A₁.I.ζ (m ^ 2) : F₁), A₁.ρ] ![zeta (m ^ 2), H.rt0] halg hC₁
  have hg0 : g (A₁.I.ζ (m ^ 2) : F₁) = zeta (m ^ 2) := by simpa using hg 0
  have hg1 : g A₁.ρ = H.rt0 := by simpa using hg 1
  letI : Algebra (FractionRing R₁) ℂ := (g.comp (algebraMap (FractionRing R₁) F₁)).toAlgebra
  obtain ⟨A₂, -, hA₂⟩ := hup E H D R₁ F₁ ℂ g (fun x => rfl) A₁
  obtain ⟨e₂, he₂⟩ := over_iff hA₂
  obtain ⟨β₂, hβ₂⟩ := exists_form e₂.symm β₁
  have hb12 : ∀ y z, β₁.be y z = β₂.be (e₂ y) (e₂ z) := by
    intro y z
    rw [hβ₂]
    simp
  have h2 := he₂ k β₁ β₂ hb12
  rw [h2.2 m hm G d hG]
  obtain ⟨I₂, hρ₂, hζ₂, _, _⟩ := hA₂
  have hρ₂' : A₂.ρ = H.rt0 := by rw [← hρ₂, hg1]
  have hζ₂' : (A₂.I.ζ (m ^ 2) : ℂ) = zeta (m ^ 2) := by rw [← hζ₂ _ hpos, hg0]
  have hB₂ : A₂.Bal β₂ := h2.1.mp (h1.1.mpr hB)
  obtain ⟨ε, hε, hsmall⟩ := hC4400 E H D R₁ A₂ hρ₂' k β₂ hB₂ m hmk hm
  rw [hζ₂', hρ₂']
  refine GlobalTheory.Ex.ArcForm.aeval_arcTx_eq_zero A₂.N k β₂ m hmk hm D.La (fun x => A₂.q _ x) _ ε hε
    fun u hu => ⟨(hsmall u hu).1, ?_⟩
  obtain ⟨o, hoρ, hoζ, hθ⟩ := (hsmall u hu).2
  rw [MvPolynomial.eval_map]
  exact hVan o hoρ (by rw [hoζ]; exact hζ₂') _ hθ

end GlobalTheory.ArcIdentity
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_identity_principle_complex_points : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (A : ArcF D R F) (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ m : ℕ, m ^ 2 ∣ k → Odd m → Compat H (m ^ 2) (A.I.ζ (m ^ 2) : F) A.ρ → ∀ G, VanishC D m G → MvPolynomial.aeval (fun x => A.N.arcTx β.be m (A.q _ x)) (MvPolynomial.map (cf (A.I.ζ (m ^ 2) : F) A.ρ) G) = 0 := by
  atlas_forward_decl GlobalTheory.ArcIdentity.aeval_arcTx_eq_zero_of_vanishC
end

section
section
namespace GlobalTheory.Ex.OneLevel
section Arith
open Polynomial

theorem dvd_pow_sub {z : ℂ} {d k : ℕ} (hd : d.Prime) (hz : z ^ d ^ k = z) (y : Algebra.adjoin ℤ {z}) :
    (d : Algebra.adjoin ℤ {z}) ∣ y ^ d ^ k - y := by
  obtain ⟨y, hy⟩ := y
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl : x = z := hx
    exact ⟨0, Subtype.ext (by simp [hz])⟩
  | algebraMap r =>
    haveI := Fact.mk hd
    have h : (d : ℤ) ∣ r ^ d ^ k - r := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.pow_card_pow, sub_self]
    have := map_dvd (algebraMap ℤ (Algebra.adjoin ℤ {z})) h
    rwa [map_natCast, map_sub, map_pow] at this
  | add x y hx hy ihx ihy =>
    change _ ∣ ((⟨x, hx⟩ + ⟨y, hy⟩ : Algebra.adjoin ℤ {z})) ^ _ - (⟨x, hx⟩ + ⟨y, hy⟩)
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hd (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) ⟨y, hy⟩ k
    rw [hr]
    generalize (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) = a at *
    generalize (⟨y, hy⟩ : Algebra.adjoin ℤ {z}) = b at *
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    exact ⟨s + t + a * b * r, by linear_combination hs + ht⟩
  | mul x y hx hy ihx ihy =>
    change _ ∣ ((⟨x, hx⟩ * ⟨y, hy⟩ : Algebra.adjoin ℤ {z})) ^ _ - (⟨x, hx⟩ * ⟨y, hy⟩)
    generalize (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) = a at *
    generalize (⟨y, hy⟩ : Algebra.adjoin ℤ {z}) = b at *
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    exact ⟨s * b ^ d ^ k + a * t, by rw [mul_pow]; linear_combination b ^ d ^ k * hs + a * ht⟩

theorem dvd_of_dvd_sq {z : ℂ} {d N : ℕ} (hd : d.Prime) (hN : 0 < N) (hdN : ¬ d ∣ N) (hz : z ^ N = 1)
    (y : Algebra.adjoin ℤ {z}) (h : (d : Algebra.adjoin ℤ {z}) ∣ y ^ 2) : (d : Algebra.adjoin ℤ {z}) ∣ y := by
  have hc : d.Coprime N := (Nat.Prime.coprime_iff_not_dvd hd).2 hdN
  have h1 : z ^ d ^ N.totient = z := by
    have := pow_eq_pow_of_modEq (Nat.ModEq.pow_totient hc) hz
    rwa [pow_one] at this
  have h2 : 2 ≤ d ^ N.totient := hd.two_le.trans (Nat.le_self_pow (Nat.totient_pos.2 hN).ne' d)
  have h3 := dvd_sub (h.trans (pow_dvd_pow y h2)) (dvd_pow_sub hd h1 y)
  rwa [sub_sub_cancel] at h3

theorem eq_zero_of_sq {z : ℂ} {d N : ℕ} (hd : d.Prime) (hN : 0 < N) (hdN : ¬ d ∣ N) (hz : z ^ N = 1)
    (B : Algebra.adjoin ℤ {z}) : ∀ A : Algebra.adjoin ℤ {z}, A ^ 2 = -d * B ^ 2 → B = 0 := by
  have hi : IsIntegral ℤ z := IsIntegral.of_pow hN (hz ▸ isIntegral_one)
  haveI : Module.Finite ℤ (Algebra.adjoin ℤ {z}) := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : IsNoetherianRing (Algebra.adjoin ℤ {z}) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hd0 : (d : Algebra.adjoin ℤ {z}) ≠ 0 := Nat.cast_ne_zero.2 hd.ne_zero
  have hu : ¬ IsUnit (d : Algebra.adjoin ℤ {z}) := fun hu => by
    rw [← map_natCast (algebraMap ℤ (Algebra.adjoin ℤ {z}))] at hu
    exact (Nat.prime_iff_prime_int.1 hd).not_unit (IsUnit.of_map _ _ hu)
  induction B using (wellFounded_dvdNotUnit (α := Algebra.adjoin ℤ {z})).induction with
  | _ B ih =>
    intro A hA
    obtain ⟨A', rfl⟩ := dvd_of_dvd_sq hd hN hdN hz A ⟨-B ^ 2, by rw [hA]; ring⟩
    have h1 : B ^ 2 = d * -A' ^ 2 := mul_left_cancel₀ hd0 (by linear_combination hA)
    obtain ⟨B', rfl⟩ := dvd_of_dvd_sq hd hN hdN hz B ⟨_, h1⟩
    by_contra h0
    have hB' : B' ≠ 0 := right_ne_zero_of_mul h0
    exact hB' (ih B' ⟨hB', d, hu, mul_comm _ _⟩ A' (mul_left_cancel₀ hd0 (by linear_combination h1)))

theorem exists_linear (d : ℕ) (c : MvPolynomial (Fin 2) ℤ) : ∃ a b : ℤ[X], ∀ (K : Type) [CommRing K] (ζ ρ : K),
    ρ ^ 2 = -(d : K) → cf ζ ρ c = aeval ζ a + ρ * aeval ζ b := by
  induction c using MvPolynomial.induction_on with
  | C r => exact ⟨C r, 0, fun K _ ζ ρ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨a, b, h⟩ := hp
    obtain ⟨a', b', h'⟩ := hq
    exact ⟨a + a', b + b', fun K _ ζ ρ e => by rw [map_add, h K ζ ρ e, h' K ζ ρ e, map_add, map_add]; ring⟩
  | mul_X p i hp =>
    obtain ⟨a, b, h⟩ := hp
    fin_cases i
    · exact ⟨a * X, b * X, fun K _ ζ ρ e => by rw [map_mul, h K ζ ρ e]; simp; ring⟩
    · exact ⟨-d * b, a, fun K _ ζ ρ e => by
        rw [map_mul, h K ζ ρ e]; simp; linear_combination aeval ζ b * e⟩

theorem compat_of_not_dvd {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {N : ℕ} (hN : 0 < N) (hdN : ¬ H.d ∣ N) {K : Type} [Field K] {ζ ρ : K}
    (hζ : IsPrimitiveRoot ζ N) (hρ : ρ ^ 2 = -(H.d : K)) : Compat H N ζ ρ := by
  intro c hc
  obtain ⟨a, b, h⟩ := exists_linear H.d c
  have hz : IsPrimitiveRoot (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N) N := Complex.isPrimitiveRoot_exp N hN.ne'
  generalize ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N = z at hc hz
  rw [h ℂ _ _ H.sqrt_neg_disc_sq] at hc
  have hb : aeval z b = 0 := congrArg Subtype.val (eq_zero_of_sq H.d_prime hN hdN hz.pow_eq_one
    ⟨aeval z b, aeval_mem_adjoin_singleton _ _⟩ ⟨aeval z a, aeval_mem_adjoin_singleton _ _⟩ (Subtype.ext (by
      have := H.sqrt_neg_disc_sq
      push_cast
      linear_combination (aeval z a - H.rt0 * aeval z b) * hc + aeval z b ^ 2 * this)))
  have ha : aeval z a = 0 := by rwa [hb, mul_zero, add_zero] at hc
  have key : ∀ p : ℤ[X], aeval z p = 0 → aeval ζ p = 0 := fun p hp => by
    have h1 := minpoly.isIntegrallyClosed_dvd (hz.isIntegral hN) hp
    rw [← cyclotomic_eq_minpoly hz hN] at h1
    refine aeval_eq_zero_of_dvd_aeval_eq_zero h1 ?_
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hN
  rw [h K _ _ hρ, key a ha, key b hb, mul_zero, add_zero]
end Arith

def scaleForm {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (j : ℕ) (hj : 0 < j) : N.Form j where
  be := (j : ℤ) • β.be
  symm y z := congrArg ((j : ℤ) * ·) (β.symm y z)
  pos y hy := mul_pos (Int.natCast_pos.2 hj) (β.pos y hy)
  dvd y z := by
    change _ ∣ (j : ℤ) * β.be y z
    rw [mul_comm 2]
    exact mul_dvd_mul_left _ ((Dvd.intro _ rfl).trans (β.dvd y z))

theorem tx_congr {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O) (ψ ψ' : N.X → Oˣ) (e b e' b') (h : ψ = ψ')
    (m : ℕ) (p : ({ N with ψ := ψ, even := e, bimult := b } : NumD O).QT (m ^ 2))
    (p' : ({ N with ψ := ψ', even := e', bimult := b' } : NumD O).QT (m ^ 2))
    (h1 : p.1.1 = p'.1.1) (h2 : p.1.2.b = p'.1.2.b) (h3 : p.1.2.s = p'.1.2.s) :
    NumD.tx _ m p = NumD.tx _ m p' := by
  subst h
  rw [show p = p' from Subtype.ext (Prod.ext h1 (NumD.Gt.ext h2 h3))]

theorem tx_scale {O : Type} [CommRing O] [TopologicalSpace O] {N : NumD O} {k : ℕ} (β : N.Form k) (m : ℕ)
    (hm : 0 < m ^ 2) (u r : Oˣ) (hr : r ^ m ^ 2 = u) (q : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2))
    (h : TwRel β u r q p) :
    (N.twist β u).tx m p =
      (N.twist (scaleForm β _ hm) r).tx m (N.twQ (scaleForm β _ hm) r dvd_rfl q) := by
  refine tx_congr N _ _ _ _ _ _ (funext fun χ => ?_) m _ _ h.1 h.2.1 (funext fun χ => (h.2.2 χ).trans ?_)
  · change _ = _ * r ^ (((m ^ 2 : ℕ) : ℤ) * β.be χ χ / 2)
    rw [Int.mul_ediv_assoc _ ((Dvd.intro _ rfl).trans (β.dvd χ χ)), zpow_mul, zpow_natCast, hr]
  · change _ = q.1.2.s χ * r ^ (((m ^ 2 : ℕ) : ℤ) * β.be q.1.1.toAdd χ / ((m ^ 2 : ℕ) : ℤ))
    rw [Int.mul_ediv_cancel_left _ (Int.natCast_pos.2 hm).ne']

theorem eval_mul_of_isHomogeneous {ι C : Type} [CommRing C] {G : MvPolynomial ι C} {d : ℕ} (hG : G.IsHomogeneous d)
    (s : C) (v : ι → C) : MvPolynomial.eval (fun i => s * v i) G = s ^ d * MvPolynomial.eval v G := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have h := hG (MvPolynomial.mem_support_iff.1 he)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← h, Finsupp.weight_apply]
  simp only [Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one]
  ring
end GlobalTheory.Ex.OneLevel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.OneLevel

theorem exists_full_theta : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n j : ℕ), n.Prime → Odd n → IsUnit (n : O') → ¬ n ∣ H.d → 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  intro h1 h2 h3 h4 h5 h6 h7 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb K _ _ _ _ _ _ _ S n j hn ho hu hd hj
  haveI : CharZero K := S.A.arc.charZero
  have hm : Odd (n ^ j) := ho.pow
  have hm2 : 0 < (n ^ j) ^ 2 := pow_pos hm.pos 2
  have hdN : ¬ H.d ∣ (n ^ j) ^ 2 := fun h => hd (by
    rw [(Nat.prime_dvd_prime_iff_eq H.d_prime hn).1 (H.d_prime.dvd_of_dvd_pow (H.d_prime.dvd_of_dvd_pow h))])
  obtain ⟨o, e1, e2, e3⟩ := GlobalTheory.T.mem_thetaPoints_of_closure_coset_condition h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K n j S.A.ρ
    (S.A.I.ζ ((n ^ j) ^ 2)) (S.v (n ^ j)) hn ho hj
    (compat_of_not_dvd H hm2 hdN (IsPrimitiveRoot.coe_units_iff.2 (S.A.I.ζ_prim _ hm2)) S.A.ρ_sq)
    (fun G hG => by_contra fun hne => S.base.not_allC_false fun C _ _ _ _ _ gam u c1 c2 c3 c4 => hne (by
      obtain ⟨A', r', i1, ⟨_, o1, o2, -⟩, i3, i4⟩ := S.val C gam u c1 c2 c3 c4
      haveI : CharZero C := A'.arc.charZero
      have hr : r' ((n ^ j) ^ 2) ^ (n ^ j) ^ 2 = u := Units.ext (by
        rw [Units.val_pow_eq_pow_val, i3, ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.pow hm2, S.r_one, c3]; rfl)
      have hr1 : ‖(r' ((n ^ j) ^ 2) : C)‖ < 1 := by
        rw [← hr, Units.val_pow_eq_pow_val, norm_pow] at c4
        exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hm2.ne').1 c4
      choose p hp using fun x => (existsUnique_twRel A'.be u _ hr (A'.q _ x)).exists
      obtain ⟨⟨s, hs⟩, -⟩ := i4 _ hm p hp
      have hbal : A'.arc.Bal (scaleForm A'.be _ hm2) := fun x y z => by
        refine congrArg ((((n ^ j) ^ 2 : ℕ) : ℤ) * ·) ((A'.be_eq _ _).trans (Eq.trans ?_ (A'.be_eq _ _).symm))
        refine (congrArg (a.be · _) (A'.ν.eX.apply_symm_apply _)).trans ((a.be_adj _ _ _).trans ?_)
        exact congrArg (a.be _ ·) (A'.ν.eX.apply_symm_apply _).symm
      have k1 := GlobalTheory.T.theta_series_identity_principle_complex_points h1 h2 h3 h4 h5 h6 h7 E H D O' C A'.arc _ (scaleForm A'.be _ hm2) hbal _ dvd_rfl hm
        (compat_of_not_dvd H hm2 hdN (IsPrimitiveRoot.coe_units_iff.2 (A'.I.ζ_prim _ hm2)) A'.ρ_sq) G hG
      have hC : CExt O' ⊥ C := ⟨fun x => by rw [c1]; exact c2 _, fun x hx => by
        rw [(Submodule.mem_bot _).1 hx, map_zero, map_zero, norm_zero]; exact one_pos⟩
      have k2 := GlobalTheory.eval_twist_tx_eq_zero_of_aeval_arcTx C A'.N _ (scaleForm A'.be _ hm2) _ dvd_rfl hm D.La (A'.q _)
        (fun x => (GlobalTheory.Ex.UnitNorm.norms_of_arc_input E H D l Xo c W₀ Y O' b ϖ a hb C hC A' i1).2.1 _ hm _) _ k1 _ hr1
      obtain ⟨d, hGd⟩ := hG.2.1
      apply gam.injective
      have ec : gam.comp (cf (S.A.I.ζ ((n ^ j) ^ 2) : K) S.A.ρ) = cf (A'.I.ζ ((n ^ j) ^ 2) : C) A'.ρ := by
        refine MvPolynomial.ringHom_ext (fun x => by simp) fun i => ?_
        fin_cases i
        · simpa [Lift.arc] using o2 _ hm2
        · simpa [Lift.arc] using o1
      rw [map_zero, MvPolynomial.eval₂_comp_left, ec, MvPolynomial.eval₂_eq_eval_map]
      have ev : gam ∘ S.v (n ^ j) = fun x => (s : C) * (A'.N.twist (scaleForm A'.be _ hm2) (r' ((n ^ j) ^ 2))).tx (n ^ j)
          (A'.N.twQ (scaleForm A'.be _ hm2) (r' ((n ^ j) ^ 2)) dvd_rfl (A'.q _ x)) := funext fun x =>
        (hs x).trans (congrArg _ (tx_scale A'.be _ hm2 u _ hr _ _ (hp x)))
      rw [ev, eval_mul_of_isHomogeneous (hGd.map _)]
      exact mul_eq_zero_of_right _ k2))
    (fun x => by
      have hX : algebraMap (PowerSeries O') K PowerSeries.X ≠ 0 := by rw [← S.r_one]; exact Units.ne_zero _
      obtain ⟨h, hh⟩ := (S.int n j hn ho hu (by omega) ⊤ fun _ => trivial).2.2
        ((ValuationSubring.valuation_eq_one_iff (⊤ : ValuationSubring K) ⟨_, trivial⟩).1
          (IsUnit.of_mul_eq_one ⟨_⁻¹, trivial⟩ (Subtype.ext (mul_inv_cancel₀ hX)))) x
      exact ⟨h, fun e => by rw [e, map_zero] at hh; exact zero_ne_one hh⟩)
  exact ⟨o, e1, Units.ext e2, e3⟩
end GlobalTheory.Ex.OneLevel
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_object_with_thetaPoint_of_degenerationSeries : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n j : ℕ), n.Prime → Odd n → IsUnit (n : O') → ¬ n ∣ H.d → 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  atlas_forward_decl GlobalTheory.Ex.OneLevel.exists_full_theta
end
