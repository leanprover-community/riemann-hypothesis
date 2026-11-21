import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalTF
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHRel
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.EmbeddedArchimedeanIdentityEqOne
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicTailEstimateProof
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AffOneZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Qminor
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHFinC
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.FixGlob
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.ExChi
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicKernelAlgebraProof
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.LoweringOperatorRelationHolomorphic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.AutomorphicFormsLeSm
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHolWC
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHRep
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfPropMV
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.DenseRangeUnitsR

section
noncomputable section

open scoped NNReal

namespace UpperTheory.Esk.CharacterExpansionLemmas

theorem key (ν : Valuation ℂ ℝ≥0) (τ δ : ℂ) (hτ : ν τ ≤ 1) (hδ : ν δ ≤ 1) :
    ∀ n, ν (ch τ δ n) ≤ 1 ∧ ν (ch τ δ (n + 1)) ≤ 1 ∧ ν (ch τ δ (n + 1) - τ ^ n) ≤ ν δ
  | 0 => by simp [ch]
  | n + 1 => by
    obtain ⟨h0, h1, h2⟩ := key ν τ δ hτ hδ n
    have e : ch τ δ (n + 2) = τ * ch τ δ (n + 1) - δ * ch τ δ n := rfl
    have e2 : ch τ δ (n + 2) - τ ^ (n + 1) = τ * (ch τ δ (n + 1) - τ ^ n) - δ * ch τ δ n := by
      rw [e]; ring
    refine ⟨h1, ?_, ?_⟩
    · rw [e]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [Valuation.map_mul]
      · calc ν τ * ν (ch τ δ (n + 1)) ≤ 1 * 1 := mul_le_mul' hτ h1
          _ = 1 := one_mul _
      · calc ν δ * ν (ch τ δ n) ≤ 1 * 1 := mul_le_mul' hδ h0
          _ = 1 := one_mul _
    · rw [e2]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [Valuation.map_mul]
      · calc ν τ * ν (ch τ δ (n + 1) - τ ^ n) ≤ 1 * ν δ := mul_le_mul' hτ h2
          _ = ν δ := one_mul _
      · calc ν δ * ν (ch τ δ n) ≤ ν δ * 1 := mul_le_mul' le_rfl h0
          _ = ν δ := mul_one _

end UpperTheory.Esk.CharacterExpansionLemmas

theorem UpperTheory.Esk.pf_GCh : UpperTheory.Esk.GCh := fun ν τ δ hτ hδ n =>
  ⟨(UpperTheory.Esk.CharacterExpansionLemmas.key ν τ δ hτ hδ n).2.1, (UpperTheory.Esk.CharacterExpansionLemmas.key ν τ δ hτ hδ n).2.2⟩
end
end

section
noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Sd.Wc
open scoped NNReal

namespace UpperTheory.Esk.NormOneUnitsLemmas

theorem pow_sub (ν : Valuation ℂ ℝ≥0) {b : ℂ} (hb : ν b ≤ 1) (m : ℕ) : ν (b ^ m - 1) ≤ ν (b - 1) := by
  rw [← geom_sum_mul, Valuation.map_mul]
  refine mul_le_of_le_one_left zero_le ?_
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [Valuation.map_pow]
  exact pow_le_one₀ zero_le hb

theorem pow_l (ν : Valuation ℂ ℝ≥0) (l : ℕ) {b : ℂ} (hb : ν b ≤ 1) (hbp : ν (b - 1) ≤ ν (l : ℂ)) :
    ν (b ^ l - 1) ≤ ν (l : ℂ) * ν (b - 1) := by
  rw [← geom_sum_mul, Valuation.map_mul]
  refine mul_le_mul_of_nonneg_right ?_ zero_le
  have e : ∑ i ∈ Finset.range l, b ^ i = ∑ i ∈ Finset.range l, (b ^ i - 1) + (l : ℂ) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ le_rfl)
  exact Valuation.map_sum_le _ fun i _ => (pow_sub ν hb i).trans hbp

theorem pow_lN (ν : Valuation ℂ ℝ≥0) (l : ℕ) {b : ℂ} (hb : ν b ≤ 1) (hbp : ν (b - 1) ≤ ν (l : ℂ)) :
    ∀ N : ℕ, ν (b ^ (l ^ N) - 1) ≤ ν (l : ℂ) ^ N * ν (b - 1)
  | 0 => by simp
  | N + 1 => by
    have hb' : ν (b ^ (l ^ N)) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hb
    have e : b ^ (l ^ (N + 1)) = (b ^ (l ^ N)) ^ l := by rw [pow_succ, pow_mul]
    rw [e]
    refine (pow_l ν l hb' ((pow_sub ν hb _).trans hbp)).trans ?_
    calc ν (l : ℂ) * ν (b ^ (l ^ N) - 1) ≤ ν (l : ℂ) * (ν (l : ℂ) ^ N * ν (b - 1)) :=
          mul_le_mul_of_nonneg_left (pow_lN ν l hb hbp N) zero_le
      _ = ν (l : ℂ) ^ (N + 1) * ν (b - 1) := by ring

theorem lt_one_le (a : WithZero (Multiplicative ℤ)) (h : a < 1) : a ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : a = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

end UpperTheory.Esk.NormOneUnitsLemmas

open UpperTheory.Esk.NormOneUnitsLemmas in
theorem UpperTheory.Esk.pf_GUnit : UpperTheory.Esk.GUnit := by
  intro F _ _ l _ ι D v x hx N t ht
  obtain ⟨m, rfl⟩ := ht
  set L : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) with hL
  have hLv : Valued.v L = WithZero.exp (-1 : ℤ) := D.unif v
  have hL0 : L ≠ 0 := fun h => by rw [h, map_zero] at hLv; exact WithZero.exp_ne_zero hLv.symm
  have hemL : D.em v L = (l : ℂ) := map_natCast _ l
  have hxle : nu ι (D.em v x) ≤ 1 := (D.le v x).2 hx.le
  set y := x ^ (l - 1) - 1 with hy
  have hemy : D.em v y = D.em v x ^ (l - 1) - 1 := by rw [hy, map_sub, map_pow, map_one]
  have hylt : Valued.v y < 1 := (D.lt v y).1 (by rw [hemy]; exact D.res v x hx)
  have hyL : Valued.v (y / L) ≤ 1 := by
    rw [map_div₀, hLv, div_le_one₀ (by simp)]
    exact lt_one_le _ hylt
  have hnuy : nu ι (D.em v y) ≤ nu ι (l : ℂ) := by
    have e : y = L * (y / L) := by field_simp
    rw [e, map_mul, map_mul, hemL]
    exact mul_le_of_le_one_right zero_le ((D.le v _).2 hyL)
  rw [hemy] at hnuy
  set a := D.em v x ^ (l - 1) with ha
  have hale : nu ι a ≤ 1 := by rw [ha, Valuation.map_pow]; exact pow_le_one₀ zero_le hxle
  have ha1 : nu ι (a - 1) ≤ 1 := by rw [← hemy]; exact ((D.lt v y).2 hylt).le
  have e : D.em v x ^ ((l - 1) * l ^ N * m) = (a ^ (l ^ N)) ^ m := by rw [ha, ← pow_mul, ← pow_mul, mul_assoc]
  rw [e]
  have hb : nu ι (a ^ (l ^ N)) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hale
  refine (pow_sub _ hb m).trans ((pow_lN _ l hale hnuy N).trans ?_)
  exact mul_le_of_le_one_right zero_le ha1
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped NNReal

namespace UpperTheory.Esk.ModulusCharacterLemmas

variable {F : Type} [Field F] [NumberField F]

theorem tnn {e : ℝ≥0} (he : e ≠ 0) (m : ℤ) : WithZeroMulInt.toNNReal he (WithZero.exp m) = e ^ m := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]; rfl

theorem exp_mul_pow (m : ℤ) :
    WithZero.exp m * (WithZero.exp (-1 : ℤ)) ^ m = (1 : WithZero (Multiplicative ℤ)) := by
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_zpow, ← WithZero.coe_mul,
    ← ofAdd_zsmul, ← ofAdd_add]
  simp

theorem val_exp {w : Pl F} {x : w.adicCompletion F} (hx : x ≠ 0) : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
  ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm⟩

theorem norm_eq (w : Pl F) {x : w.adicCompletion F} {m : ℤ} (hm : Valued.v x = WithZero.exp m) :
    ‖x‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ m := by
  rw [FinitePlace.norm_def (x := x), hm, tnn, NNReal.coe_zpow, NNReal.coe_natCast]

theorem normV_eq (w : Pl F) : normV w = Ideal.absNorm w.asIdeal := by
  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem nu_nat {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (h : ¬ l ∣ n) : nu ι (n : ℂ) = 1 := by
  have e : ι.symm (n : ℂ) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l]) := by rw [map_natCast, map_natCast]
  apply NNReal.coe_injective
  rw [nu_apply, coe_nnnorm, e, norm_algebraMap',
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h), NNReal.coe_one]

theorem not_dvd (w : Pl F) {l : ℕ} [hl : Fact l.Prime] (h : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) : ¬ l ∣ normV w := by
  intro hd
  haveI := w.isPrime
  have hne : normV w ≠ 0 := by
    rw [normV_eq]; have := HeightOneSpectrum.one_lt_absNorm w; omega
  haveI : Finite (𝓞 F ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero hne
  haveI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  have hd' : l ∣ Fintype.card (𝓞 F ⧸ w.asIdeal) := by rw [Fintype.card_eq_nat_card]; exact hd
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card l hd'
  have h1 : (l : 𝓞 F ⧸ w.asIdeal) * a = 0 := by rw [← nsmul_eq_mul, ← ha, addOrderOf_nsmul_eq_zero]
  have h2 : (l : 𝓞 F ⧸ w.asIdeal) ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ne, Ideal.Quotient.eq_zero_iff_mem]; exact h
  have h3 : a = 0 := (mul_eq_zero.1 h1).resolve_left h2
  rw [h3, addOrderOf_zero] at ha
  exact hl.out.one_lt.ne ha

theorem away {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : Pl F) (h : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    {x : w.adicCompletion F} (hx : x ≠ 0) : nu ι (‖x‖ : ℂ) = 1 := by
  obtain ⟨m, hm⟩ := val_exp hx
  rw [norm_eq w hm, Complex.ofReal_zpow, Complex.ofReal_natCast, map_zpow₀, ← normV_eq, nu_nat ι (not_dvd w h),
    one_zpow]

theorem atL {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι) (v : InfinitePlace F)
    {x : (D.pl v).adicCompletion F} (hx : x ≠ 0) : nu ι ((‖x‖ : ℂ) * D.em v x) = 1 := by
  obtain ⟨m, hm⟩ := val_exp hx
  set L : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) with hL
  have hLv : Valued.v L = WithZero.exp (-1 : ℤ) := D.unif v
  have hL0 : L ≠ 0 := fun h => by rw [h, map_zero] at hLv; exact WithZero.exp_ne_zero hLv.symm
  have hemL : D.em v L = (l : ℂ) := map_natCast _ l
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hy : Valued.v (x * L ^ m) = 1 := by rw [map_mul, map_zpow₀, hLv, hm, exp_mul_pow]
  have hnu : nu ι (D.em v (x * L ^ m)) = 1 :=
    le_antisymm ((D.le v _).2 hy.le) (not_lt.1 fun h => ((D.lt v _).1 h).ne hy)
  have hn : ‖x‖ = (l : ℝ) ^ m := by rw [norm_eq _ hm, ← normV_eq, D.norm v]
  have e : (‖x‖ : ℂ) * D.em v x = D.em v (x * L ^ m) := by
    rw [hn, map_mul, map_zpow₀, hemL, Complex.ofReal_zpow, Complex.ofReal_natCast]
    ring
  rw [e, hnu]

theorem nrm_unit {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem fin_supp (y : (Af F)ˣ) : (Function.mulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖).Finite := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (nrm_unit (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

end UpperTheory.Esk.ModulusCharacterLemmas

open UpperTheory.Esk.ModulusCharacterLemmas in
theorem UpperTheory.Esk.pf_GMod : UpperTheory.Esk.GMod := by
  intro F _ _ l _ ι D z
  have hz : ∀ w, pLoc F w (z : Af F) ≠ 0 := fun w => (z.isUnit.map (pLoc F w)).ne_zero
  have habs : absF z = ∏ᶠ w : Pl F, ‖pLoc F w (z : Af F)‖ := rfl
  refine ⟨?_, ?_⟩
  · rw [habs]
    exact finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w => norm_pos_iff.2 (hz w)
  classical
  have hfin := fin_supp z
  set s : Finset (Pl F) := hfin.toFinset ∪ Finset.univ.image D.pl with hs_def
  have hs : absF z = ∏ w ∈ s, ‖pLoc F w (z : Af F)‖ := by
    rw [habs]
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_
    rw [hs_def, Finset.coe_union]
    exact Or.inl (hfin.mem_toFinset.2 hw)
  have hprod : ∏ v, D.ea v (z : Af F) = ∏ w ∈ s, ∏ v ∈ Finset.univ.filter (fun v => D.pl v = w), D.ea v (z : Af F) :=
    (Finset.prod_fiberwise_of_maps_to (fun v _ => by simp [hs_def]) _).symm
  rw [hs, hprod, Complex.ofReal_prod, ← Finset.prod_mul_distrib, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  by_cases hw : ∃ v, D.pl v = w
  · obtain ⟨v, rfl⟩ := hw
    have e : Finset.univ.filter (fun u => D.pl u = D.pl v) = {v} := by
      ext u; simp [D.inj.eq_iff]
    rw [e, Finset.prod_singleton]
    exact atL D v (hz _)
  · have e : Finset.univ.filter (fun u => D.pl u = w) = ∅ := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hw ⟨u, h⟩
    rw [e, Finset.prod_empty, mul_one]
    exact away ι w (fun h => hw (D.surj w h)) (hz w)
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc Matrix

namespace UpperTheory.Esk.HyperbolicSetupLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

omit [IsTotallyReal F] in
theorem pow_char {ω : HChar F} (h : IsOfFinOrder ω) : ∃ n, 0 < n ∧ ∀ x, ω.1 x ^ n = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact ⟨n, hn, fun x => by rw [← MonoidHom.pow_apply, e2, MonoidHom.one_apply]⟩

theorem exp_triv {ω : HChar F} (h : IsOfFinOrder ω) (z : TR.Rinf F) : ω.1 (TR.infId F (TR.expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : TR.expU z = TR.expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, TR.expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

def pU : (TR.Rinf F)ˣ ≃* (InfinitePlace F → ℝˣ) := MulEquiv.piUnits

omit [NumberField F] [IsTotallyReal F] in
theorem pU_symm_val (f : InfinitePlace F → ℝˣ) (w : InfinitePlace F) :
    (((pU.symm f : (TR.Rinf F)ˣ) : TR.Rinf F) w) = (f w : ℝ) := rfl

omit [NumberField F] [IsTotallyReal F] in
theorem pU_val (s : (TR.Rinf F)ˣ) (w : InfinitePlace F) : ((pU s w : ℝˣ) : ℝ) = (s : TR.Rinf F) w := rfl

open Classical in

def atV (v : InfinitePlace F) (x : ℝˣ) : (TR.Rinf F)ˣ := pU.symm (Pi.mulSingle v x : InfinitePlace F → ℝˣ)

open Classical in
omit [NumberField F] [IsTotallyReal F] in
theorem atV_val (v w : InfinitePlace F) (x : ℝˣ) :
    ((atV v x : (TR.Rinf F)ˣ) : TR.Rinf F) w = (((Pi.mulSingle v x : InfinitePlace F → ℝˣ) w : ℝˣ) : ℝ) := pU_symm_val _ w

theorem atV_neg (v : InfinitePlace F) :
    TR.infId F (atV v (-1)) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1) := by
  classical
  refine Units.ext (Prod.ext (funext fun w => ?_) ?_)
  · change (1 - TR.infEq F 1 + TR.infEq F ((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F)) w =
      Pi.mulSingle (M := fun w : InfinitePlace F => w.Completion) v (-1) w
    rw [map_one, sub_self, zero_add]
    change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      (((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w) = _
    by_cases h : w = v
    · subst h
      have : ((atV w (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w = -1 := by rw [atV_val]; simp
      rw [this]
      simp
    · have : ((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w = 1 := by rw [atV_val, Pi.mulSingle_eq_of_ne h]; simp
      rw [this]
      simp [h]
  · change (1 : Af F) - 0 + 0 = 1
    simp

open Classical in
omit [IsTotallyReal F] in
theorem prod_atV (s : (TR.Rinf F)ˣ) : s = ∏ v, atV v (pU s v) := by
  simp only [atV]
  rw [← map_prod, Finset.univ_prod_mulSingle, MulEquiv.symm_apply_apply]

theorem inf_sign {k : InfinitePlace F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) (hs : Sgn k ω) (u : (TR.Rinf F)ˣ) :
    ((ω.1 (TR.infId F u) : ℂˣ) : ℂ) = ∏ v, ((SignType.sign (u.val v) : ℝ) : ℂ) ^ k v := by
  obtain ⟨s, hss, e⟩ := TR.exists_sign_mul_expU u
  have hsv : ∀ v, (s : TR.Rinf F) v = 1 ∨ (s : TR.Rinf F) v = -1 := fun v => by
    have := congrArg (fun x : (TR.Rinf F)ˣ => (x : TR.Rinf F) v) hss
    simp only [Units.val_mul, Pi.mul_apply, Units.val_one, Pi.one_apply] at this
    exact mul_self_eq_one_iff.1 this
  have hsign : ∀ v, ((SignType.sign (u.val v) : ℝ)) = (s : TR.Rinf F) v := fun v => by
    have hu : u.val v = (s : TR.Rinf F) v * Real.exp (Real.log |u.val v|) := by
      conv_lhs => rw [e]
      simp [TR.expU_val]
    rw [hu, sign_mul, sign_pos (Real.exp_pos _), mul_one]
    rcases hsv v with h | h <;> rw [h] <;> simp
  have hL : ((ω.1 (TR.infId F u) : ℂˣ) : ℂ) = ∏ v, ((ω.1 (TR.infId F (atV v (pU s v))) : ℂˣ) : ℂ) := by
    have h1 : ω.1 (TR.infId F u) = ω.1 (TR.infId F s) := by
      rw [e, map_mul, map_mul, exp_triv hω, mul_one]
    rw [h1]
    conv_lhs => rw [prod_atV s]
    rw [map_prod, map_prod, Units.coe_prod]
  rw [hL]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hsign v]
  have hpv : ((pU s v : ℝˣ) : ℝ) = (s : TR.Rinf F) v := pU_val s v
  rcases hsv v with h | h
  · have : pU s v = 1 := Units.ext (hpv.trans h)
    rw [this, h]
    simp [atV]
  · have : pU s v = -1 := Units.ext (by rw [hpv, h]; simp)
    rw [this, h, atV_neg]
    have := hs v
    rw [HChar.locInf] at this
    simpa using this

theorem pInf_alg (x : F) (v : InfinitePlace F) :
    TR.pInf F (algebraMap F (Ad F) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap F (InfiniteAdeleRing F) x v) = _
  simp

theorem fin_rat {k : InfinitePlace F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) (hs : Sgn k ω) (a : Fˣ) :
    ((ω.1 (finId F (ratU F a)) : ℂˣ) : ℂ) =
      ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v := by
  let φ : F →+* TR.Rinf F := (TR.pInf F).comp (algebraMap F (AdeleRing (𝓞 F) F))
  have e : TR.infId F (Units.map φ.toMonoidHom a) * finId F (ratU F a) =
      Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a := by
    refine Units.ext (TR.ad_ext ?_ ?_)
    · rw [Units.val_mul, map_mul]
      change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F (φ a)) *
        TR.pInf F (1 - GlobalTheory.CuspRep.sFin F 1 + GlobalTheory.CuspRep.sFin F _) = φ a
      have h1 : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
      have h2 : ∀ x, TR.pInf F (GlobalTheory.CuspRep.sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
      simp only [map_add, map_sub, map_one, h1, h2, sub_self, zero_add, sub_zero, add_zero, mul_one]
    · rw [Units.val_mul, map_mul]
      change ((1 : Af F) - 0 + 0) * ((1 : Af F) - 1 + algebraMap F (Af F) a) = algebraMap F (Af F) a
      simp only [sub_self, zero_add, sub_zero, add_zero, one_mul]
  have h1 : ω.1 (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1 := ω.2.2 a
  rw [← e, map_mul] at h1
  have h2 := congrArg Units.val h1
  rw [Units.val_mul, Units.val_one, inf_sign hω hs] at h2
  have h3 : ∀ v, ((Units.map φ.toMonoidHom a : (TR.Rinf F)ˣ) : TR.Rinf F) v =
      InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F) := fun v => pInf_alg (a : F) v
  simp only [h3] at h2
  have hP : (∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
      ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [← mul_pow]
    have : ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) *
        ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) = 1 := by
      have ha : InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F) ≠ 0 :=
        (map_ne_zero _).2 a.ne_zero
      rcases lt_or_gt_of_ne ha with h | h
      · rw [sign_neg h]; simp
      · rw [sign_pos h]; simp
    rw [this, one_pow]
  calc _ = (∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
        ((∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
          ((ω.1 (finId F (ratU F a)) : ℂˣ) : ℂ)) := by rw [← mul_assoc, hP, one_mul]
    _ = _ := by rw [h2, mul_one]

end UpperTheory.Esk.HyperbolicSetupLemmas

open UpperTheory.Esk.HyperbolicSetupLemmas in
theorem UpperTheory.Esk.hyperbolic_orbit_integral_proof : UpperTheory.Esk.H0b := by
  intro F _ _ _ k c ω χ hω hχ
  refine ⟨?_, fun hs => ⟨?_, inf_sign hω hs⟩⟩
  · obtain ⟨n, hn, hp⟩ := pow_char hω
    refine ⟨n, hn, fun h => ?_⟩
    obtain ⟨⟨k', hk', z, hz⟩, h2⟩ := hχ h
    rw [h2 k' hk' z hz]
    exact hp _
  · intro γ h
    obtain ⟨h1, h2, h3⟩ := center_entries h
    have h0 : γ 0 0 ≠ 0 := fun e => γ.det_ne_zero (by rw [Matrix.det_fin_two, e, h1]; simp)
    set a : Fˣ := Units.mk0 _ h0 with ha
    have hz : jF F γ = zc F (ratU F a) := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      change algebraMap F (Af F) (γ i j) = Matrix.scalar (Fin 2) (algebraMap F (Af F) (γ 0 0)) i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2, ← h3]
    obtain ⟨-, hχ2⟩ := hχ ⟨jF F γ, (mkDat c χ).cenH γ h⟩
    have e := hχ2 1 (one_mem _) (ratU F a) (by rw [one_mul]; exact hz)
    change ((χ ⟨jF F γ, _⟩ : ℂˣ) : ℂ) = ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (γ 0 0)) : ℝ) : ℂ) ^ k v
    rw [e, fin_rat hω hs a]
    rfl
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.IdeleSplittingLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def zg (g : GL (Fin 2) (TR.Rinf F)) : InfinitePlace F → P := fun v => gv v g • iP

def Jg (k : InfinitePlace F → ℕ) (g : GL (Fin 2) (TR.Rinf F)) : ℂ := ∏ v, j1 (k v) (gv v g) iP

theorem Jg_ne (hB : B1b) (k : InfinitePlace F → ℕ) (g : GL (Fin 2) (TR.Rinf F)) : Jg k g ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => hB.2.1 _ _ _

theorem pInf_alg (x : F) (v : InfinitePlace F) :
    TR.pInf F (algebraMap F (Ad F) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  have h : algebraMap F (InfiniteAdeleRing F) x = TR.infEq F (fun w => InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x) := by
    funext w
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).injective
    show _ = (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w))
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
        (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x))
    rw [RingEquiv.apply_symm_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal w) _
  change (TR.infEq F).symm (algebraMap F (InfiniteAdeleRing F) x) v = _
  rw [h, RingEquiv.symm_apply_apply]

theorem gv_rat (γ : GL (Fin 2) F) (v : InfinitePlace F) :
    gv v (Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ)) =
      Matrix.GeneralLinearGroup.map (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)) γ :=
  Units.ext (Matrix.ext fun i j => pInf_alg (γ i j) v)

omit [IsTotallyReal F] in
theorem pFin_rat (γ : GL (Fin 2) F) : Matrix.GeneralLinearGroup.map (pFin F) (ratGL F 2 γ) = jF F γ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem val_eq (hB : B1b) {k : InfinitePlace F → ℕ} {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ}
    (hr : Rel k f φ) (h : GA F 2) :
    φ h = f (zg (Matrix.GeneralLinearGroup.map (TR.pInf F) h), Matrix.GeneralLinearGroup.map (pFin F) h) /
      Jg k (Matrix.GeneralLinearGroup.map (TR.pInf F) h) := by
  rw [eq_div_iff (Jg_ne hB k _)]
  have := hr (Matrix.GeneralLinearGroup.map (TR.pInf F) h) (Matrix.GeneralLinearGroup.map (pFin F) h)
  rwa [TR.infGL_mul_finGL] at this

theorem part1 (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {χ : Hc c →* ℂˣ} {f : (InfinitePlace F → P) × GF F → ℂ}
    {φ : GA F 2 → ℂ} (hf : (mkDat c χ).IsForm k f) (hr : Rel k f φ) (γ : GL (Fin 2) F) (g : GA F 2) :
    φ (ratGL F 2 γ * g) = φ g := by
  rw [val_eq hB hr, val_eq hB hr, map_mul, map_mul, pFin_rat]
  set a := Matrix.GeneralLinearGroup.map (TR.pInf F) g
  set x := Matrix.GeneralLinearGroup.map (pFin F) g
  have hz : zg (Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) * a) = (mkDat c χ).act γ (zg a) := by
    funext v
    simp only [zg, map_mul, gv_rat, mul_smul]
    rfl
  have hJ : Jg k (Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) * a) = (mkDat c χ).J k γ (zg a) * Jg k a := by
    simp only [Jg, Dat.J, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_mul, hB.1, gv_rat]
    rfl
  have hne : (mkDat c χ).J k γ (zg a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hB.2.1 _ _ _
  rw [hz, hJ, show jF F γ * x = (mkDat c χ).j γ * x from rfl, hf.aut, mul_div_mul_left _ _ hne]

theorem part2 (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ}
    {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ} (hχ : IsChi c ω χ) (hf : (mkDat c χ).IsForm k f)
    (hr : Rel k f φ) (u : GF F) (hu : u ∈ Kc c) (g : GA F 2) : φ (g * finGL F 2 u) = φ g := by
  rw [val_eq hB hr, val_eq hB hr, map_mul, map_mul, TR.pInf_finGL, mul_one, pFin_finGL]
  have hH : u ∈ Hc c := Subgroup.mem_sup_left hu
  have h1 := hf.lev (zg (Matrix.GeneralLinearGroup.map (TR.pInf F) g)) (Matrix.GeneralLinearGroup.map (pFin F) g)
    (⟨u, hH⟩ : (mkDat c χ).H)
  have h2 : χ ⟨u, hH⟩ = 1 := by
    rw [(hχ ⟨u, hH⟩).2 u hu 1 (by simp [zc]), map_one, map_one]
  change f (_, _ * u) = (χ ⟨u, hH⟩ : ℂ) * _ at h1
  rw [h1, h2, Units.val_one, one_mul]

theorem idele_split (z : Ideles F) :
    TR.infId F (Units.map (TR.pInf F).toMonoidHom z) * finId F (Units.map (pFin F).toMonoidHom z) = z := by
  have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
  have h2 : ∀ x, TR.pInf F (sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
  have h3 : ∀ x, pFin F (TR.sInf F x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin F (sFin F x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F z.val)) * (1 - sFin F 1 + sFin F (pFin F z.val))) = _
    simp [h, h2]
  · change pFin F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F z.val)) * (1 - sFin F 1 + sFin F (pFin F z.val))) = _
    simp [h3, h4]

theorem map_scalar {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map p (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map p.toMonoidHom z) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map]

theorem sign_pow (k : ℕ) {s : ℝ} (hs : s ≠ 0) :
    s ^ k * |s * s| ^ (-(k : ℝ) / 2) = (SignType.sign s : ℝ) ^ k := by
  have ha : 0 < |s| := abs_pos.2 hs
  have e1 : |s * s| ^ (-(k : ℝ) / 2) = (|s| ^ k)⁻¹ := by
    rw [abs_mul, ← sq, ← Real.rpow_natCast |s| 2, ← Real.rpow_mul ha.le, ← Real.rpow_natCast, ← Real.rpow_neg ha.le]
    congr 1
    push_cast
    ring
  rw [e1]
  calc s ^ k * (|s| ^ k)⁻¹ = ((SignType.sign s : ℝ) * |s|) ^ k * (|s| ^ k)⁻¹ := by rw [sign_mul_abs]
    _ = _ := by rw [mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), mul_one]

theorem automorphy_factor_scalar_matrix (k : ℕ) (g : GL (Fin 2) ℝ) (s : ℝ) (hs : s ≠ 0) (h10 : g 1 0 = 0) (h01 : g 0 1 = 0) (h00 : g 0 0 = s)
    (h11 : g 1 1 = s) (w : P) : j1 k g w = ((SignType.sign s : ℝ) : ℂ) ^ k := by
  rw [j1, den, det_eq, h10, h01, h00, h11, ← Complex.ofReal_pow, ← sign_pow k hs]
  simp [Complex.ofReal_mul]

theorem gv_scalar (t : (TR.Rinf F)ˣ) (v : InfinitePlace F) :
    (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 1 0 = 0 ∧ (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 0 1 = 0 ∧
      (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 0 0 = t.val v ∧
      (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 1 1 = t.val v := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [gv, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map]

theorem part3 (hB : B1b) (h0 : H0b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ}
    {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ} (hω : IsOfFinOrder ω) (hχ : IsChi c ω χ) (hs : Sgn k ω)
    (hf : (mkDat c χ).IsForm k f) (hr : Rel k f φ) (z : Ideles F) (g : GA F 2) :
    φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ g := by
  set zi := Units.map (TR.pInf F).toMonoidHom z
  set zf := Units.map (pFin F).toMonoidHom z
  have hω' : ((ω.1 z : ℂˣ) : ℂ) = ((ω.1 (TR.infId F zi) : ℂˣ) : ℂ) * ((ω.1 (finId F zf) : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, ← map_mul, idele_split]
  have hS := ((h0 F k c ω χ hω hχ).2 hs).2 zi
  rw [val_eq hB hr, val_eq hB hr g, map_mul, map_mul, map_scalar, map_scalar]
  set a := Matrix.GeneralLinearGroup.map (TR.pInf F) g
  set x := Matrix.GeneralLinearGroup.map (pFin F) g
  set S : ℂ := ∏ v, ((SignType.sign (zi.val v) : ℝ) : ℂ) ^ k v
  have hz : zg (Matrix.GeneralLinearGroup.scalar (Fin 2) zi * a) = zg a := by
    funext v
    obtain ⟨e1, e2, e3, e4⟩ := gv_scalar zi v
    simp only [zg, map_mul, mul_smul]
    exact center_smul _ e2 e1 (e3.trans e4.symm) _
  have hJ : Jg k (Matrix.GeneralLinearGroup.scalar (Fin 2) zi * a) = S * Jg k a := by
    simp only [Jg, S, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    obtain ⟨e1, e2, e3, e4⟩ := gv_scalar zi v
    rw [map_mul, hB.1, automorphy_factor_scalar_matrix _ _ (zi.val v) (TR.unit_ne_zero zi v) e1 e2 e3 e4]
  have hH : zc F zf ∈ Hc c := Subgroup.mem_sup_right ⟨zf, rfl⟩
  have hc : χ ⟨zc F zf, hH⟩ = ω.1 (finId F zf) := (hχ ⟨zc F zf, hH⟩).2 1 (one_mem _) zf (one_mul _).symm
  have hl := hf.lev (zg a) x (⟨zc F zf, hH⟩ : (mkDat c χ).H)
  change f (_, x * zc F zf) = (χ ⟨zc F zf, hH⟩ : ℂ) * _ at hl
  have hcomm : Matrix.GeneralLinearGroup.scalar (Fin 2) zf * x = x * zc F zf :=
    (Subgroup.mem_center_iff.1 (zc_center zf) x).symm
  have hSS : S * S = 1 := by
    simp only [S, ← Finset.prod_mul_distrib, ← mul_pow]
    refine Finset.prod_eq_one fun v _ => ?_
    rcases lt_or_gt_of_ne (TR.unit_ne_zero zi v) with h | h
    · simp [h]
    · simp [h]
  have hSne : S ≠ 0 := left_ne_zero_of_mul_eq_one hSS
  rw [hz, hJ, hcomm, hl, hc, hω', hS, div_eq_iff (mul_ne_zero hSne (Jg_ne hB k a))]
  rw [show S * ((ω.1 (finId F zf) : ℂˣ) : ℂ) * (f (zg a, x) / Jg k a) * (S * Jg k a) =
    (S * S) * ((ω.1 (finId F zf) : ℂˣ) : ℂ) * f (zg a, x) * ((Jg k a)⁻¹ * Jg k a) by ring, hSS,
    inv_mul_cancel₀ (Jg_ne hB k a)]
  ring

theorem part4 (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {χ : Hc c →* ℂˣ}
    {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ} (hf : (mkDat c χ).IsForm k f) (hr : Rel k f φ) :
    ∃ C, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.bdd
  refine ⟨C, fun h => ?_⟩
  rw [val_eq hB hr h, norm_div]
  set a := Matrix.GeneralLinearGroup.map (TR.pInf F) h
  have hn : ‖Jg k a‖ * nrm k (zg a) = 1 := by
    rw [Jg, nrm, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [zg, hB.2.2.2.2.1]
    simp [iP]
  have hpos : 0 < ‖Jg k a‖ := norm_pos_iff.2 (Jg_ne hB k a)
  rw [div_le_iff₀ hpos]
  have := hC (zg a) (Matrix.GeneralLinearGroup.map (pFin F) h)
  calc _ = ‖f (zg a, Matrix.GeneralLinearGroup.map (pFin F) h)‖ * nrm k (zg a) * ‖Jg k a‖ := by
        rw [mul_assoc, mul_comm (nrm k _), hn, mul_one]
    _ ≤ C * ‖Jg k a‖ := mul_le_mul_of_nonneg_right this hpos.le

end UpperTheory.Esk.IdeleSplittingLemmas

theorem UpperTheory.Esk.hyperbolic_relation_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.H0b → UpperTheory.Esk.H2a := by
  intro hB h0 F _ _ _ k c _ ω χ hω hχ hs _ f φ hf hr
  exact ⟨UpperTheory.Esk.IdeleSplittingLemmas.part1 hB hf hr, UpperTheory.Esk.IdeleSplittingLemmas.part2 hB hχ hf hr,
    UpperTheory.Esk.IdeleSplittingLemmas.part3 hB h0 hω hχ hs hf hr, UpperTheory.Esk.IdeleSplittingLemmas.part4 hB hf hr⟩
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped ContDiff

namespace UpperTheory.Esk.ImaginaryUnitActionLemmas

open UpperTheory.Esk

open Classical in

def Fx {I : Type} (f : X I → ℂ) (w : I → ℂ) : ℂ :=
  if h : ∀ v, (w v).im ≠ 0 then f (fun v => ⟨w v, h v⟩) else 0

theorem Fx_eq {I : Type} (f : X I → ℂ) {w : I → ℂ} (h : ∀ v, (w v).im ≠ 0) :
    Fx f w = f (fun v => ⟨w v, h v⟩) := by
  rw [Fx, dif_pos h]

theorem Fx_val {I : Type} (f : X I → ℂ) (z : X I) : Fx f (fun v => (z v).1) = f z :=
  Fx_eq f (fun v => (z v).2)

theorem isOpen_U (I : Type) [Finite I] : IsOpen {w : I → ℂ | ∀ v, (w v).im ≠ 0} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun v =>
    isOpen_ne_fun (Complex.continuous_im.comp (continuous_apply v)) continuous_const

theorem analytic_Fx (hO : Osg) {I : Type} [Fintype I] (f : X I → ℂ) (hf : SepHol f) :
    AnalyticOnNhd ℂ (Fx f) {w : I → ℂ | ∀ v, (w v).im ≠ 0} := by
  classical
  obtain ⟨hc, hh⟩ := hf
  refine hO I _ (isOpen_U I) (Fx f) ?_ ?_
  · rw [continuousOn_iff_continuous_domRestrict]
    have e : Set.domRestrict {w : I → ℂ | ∀ v, (w v).im ≠ 0} (Fx f) = fun w => f (fun v => ⟨w.1 v, w.2 v⟩) := by
      funext w
      exact Fx_eq f w.2
    rw [e]
    refine hc.comp (continuous_pi fun v => ?_)
    exact Continuous.subtype_mk ((continuous_apply v).comp continuous_subtype_val) _
  · intro w hw v
    have hw' : ∀ u, (w u).im ≠ 0 := hw
    let z : X I := fun u => ⟨w u, hw' u⟩
    have hd := hh z v
    have hopen : IsOpen {t : ℂ | t.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
    have hmem : {t : ℂ | t.im ≠ 0} ∈ nhds (w v) := hopen.mem_nhds (hw' v)
    refine (DifferentiableOn.differentiableAt hd hmem).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with t ht
    have ht' : t.im ≠ 0 := ht
    have hu : ∀ u, (Function.update w v t u).im ≠ 0 := by
      intro u
      by_cases huv : u = v
      · subst huv
        simpa using ht'
      · simpa [Function.update_of_ne huv] using hw' u
    rw [Fx_eq f hu]
    unfold ext1
    rw [dif_pos ht']
    congr 1
    funext u
    apply Subtype.ext
    exact (Function.apply_update (fun _ (p : P) => p.1) z v ⟨t, ht'⟩ u).symm

def dn (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ((M 1 0 : ℝ) : ℂ) * Complex.I + ((M 1 1 : ℝ) : ℂ)

def nm (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ((M 0 0 : ℝ) : ℂ) * Complex.I + ((M 0 1 : ℝ) : ℂ)

def dt (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := M 0 0 * M 1 1 - M 0 1 * M 1 0

def jj (k : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := dn M ^ k * ((|dt M| ^ (-(k : ℝ) / 2) : ℝ) : ℂ)

theorem smul_iP (g : GL (Fin 2) ℝ) : (g • iP).1 = nm g.val * (dn g.val)⁻¹ := by
  rw [coe_smul, div_eq_mul_inv]
  rfl

theorem automorphy_factor_at_i_eq (k : ℕ) (g : GL (Fin 2) ℝ) : j1 k g iP = jj k g.val := by
  unfold j1 jj dt
  rw [det_eq]
  rfl

theorem dn_ne {M : Matrix (Fin 2) (Fin 2) ℝ} (h : dt M ≠ 0) : dn M ≠ 0 := by
  intro e
  have h1 := congrArg Complex.re e
  have h2 := congrArg Complex.im e
  simp [dn] at h1 h2
  apply h
  simp [dt, h1, h2]

theorem cd_parts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (M : E → Matrix (Fin 2) (Fin 2) ℝ) (m0 : E)
    (hM : ∀ i j, ContDiffAt ℝ ∞ (fun m => M m i j) m0) (h0 : dt (M m0) ≠ 0) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun m => nm (M m) * (dn (M m))⁻¹) m0 ∧ ContDiffAt ℝ ∞ (fun m => jj k (M m)) m0 := by
  have hC : ∀ i j, ContDiffAt ℝ ∞ (fun m => ((M m i j : ℝ) : ℂ)) m0 := fun i j =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp m0 (hM i j)
  have hdn : ContDiffAt ℝ ∞ (fun m => dn (M m)) m0 := by
    unfold dn
    exact ((hC 1 0).mul contDiffAt_const).add (hC 1 1)
  have hnm : ContDiffAt ℝ ∞ (fun m => nm (M m)) m0 := by
    unfold nm
    exact ((hC 0 0).mul contDiffAt_const).add (hC 0 1)
  have hdt : ContDiffAt ℝ ∞ (fun m => dt (M m)) m0 := by
    unfold dt
    exact ((hM 0 0).mul (hM 1 1)).sub ((hM 0 1).mul (hM 1 0))
  refine ⟨hnm.mul (hdn.inv (dn_ne h0)), ?_⟩
  unfold jj
  exact (hdn.pow k).mul (Complex.ofRealCLM.contDiff.contDiffAt.comp m0
    ((hdt.abs h0).rpow_const_of_ne (p := -(k : ℝ) / 2) (abs_ne_zero.2 h0)))

theorem chart_smooth (hO : Osg) (hB : B1b) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (k : InfinitePlace F → ℕ) (f : X (InfinitePlace F) × GF F → ℂ) (φ : GA F 2 → ℂ)
    (hf : ∀ x, SepHol fun z => f (z, x)) (hR : Rel k f φ) (g0 : GA F 2) :
    ContDiffOn ℝ ∞ (TR.chart φ g0) (TR.invSet F 2) := by
  obtain ⟨-, hj1, -⟩ := hB
  obtain ⟨y0, x0, rfl⟩ : ∃ (y0 : GL (Fin 2) (TR.Rinf F)) (x0 : GF F), g0 = TR.infGL F 2 y0 * finGL F 2 x0 :=
    ⟨_, _, (TR.infGL_mul_finGL g0).symm⟩
  have hj : ∀ g : GL (Fin 2) (TR.Rinf F), ∏ v, j1 (k v) (gv v g) iP ≠ 0 :=
    fun g => Finset.prod_ne_zero_iff.2 fun v _ => hj1 _ _ _
  have key : ∀ y : GL (Fin 2) (TR.Rinf F), TR.chart φ (TR.infGL F 2 y0 * finGL F 2 x0) (TR.toL y.val) =
      f (fun v => gv v (y0 * y) • iP, x0) * (∏ v, j1 (k v) (gv v (y0 * y)) iP)⁻¹ := by
    intro y
    have e : TR.infGL F 2 y0 * finGL F 2 x0 * TR.infGL F 2 y = TR.infGL F 2 (y0 * y) * finGL F 2 x0 := by
      rw [mul_assoc, ← TR.infGL_comm, ← mul_assoc, ← map_mul]
    rw [TR.chart_val, e, eq_mul_inv_iff_mul_eq₀ (hj _)]
    exact hR (y0 * y) x0
  let A : Matrix (Fin 2) (Fin 2) (TR.Rinf F) := y0.val
  let M : InfinitePlace F → TR.Lie F 2 → Matrix (Fin 2) (Fin 2) ℝ := fun v m i j => ∑ l, A i l v * m l j v
  have hM : ∀ (y : GL (Fin 2) (TR.Rinf F)) v, M v (TR.toL y.val) = (gv v (y0 * y)).val := by
    intro y v
    ext i j
    simp only [M, A]
    change _ = ((y0 * y).val i j) v
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_apply]
    rfl
  let G : TR.Lie F 2 → ℂ := fun m => Fx (fun z => f (z, x0)) (fun v => nm (M v m) * (dn (M v m))⁻¹) *
    (∏ v, jj (k v) (M v m))⁻¹
  have hG : ∀ y : GL (Fin 2) (TR.Rinf F),
      TR.chart φ (TR.infGL F 2 y0 * finGL F 2 x0) (TR.toL y.val) = G (TR.toL y.val) := by
    intro y
    rw [key]
    simp only [G, hM, ← smul_iP, ← automorphy_factor_at_i_eq]
    rw [Fx_val]
  have hA := analytic_Fx hO (fun z => f (z, x0)) (hf x0)
  refine ContDiffOn.congr (f := G) (fun m hm => ?_) (fun m hm => ?_)
  · obtain ⟨y, rfl⟩ := id hm
    have hE : ∀ v i j, ContDiffAt ℝ ∞ (fun m : TR.Lie F 2 => M v m i j) (TR.toL y.val) := by
      intro v i j
      have hc : ∀ l, ContDiff ℝ ∞ (fun m : TR.Lie F 2 => m l j v) := fun l =>
        (contDiff_apply ℝ ℝ v).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ l))
      exact (ContDiff.sum fun l _ => contDiff_const.mul (hc l)).contDiffAt
    have hdt : ∀ v, dt (M v (TR.toL y.val)) ≠ 0 := by
      intro v
      rw [hM]
      have h := (gv v (y0 * y)).det_ne_zero
      rw [det_eq] at h
      exact h
    have hP : ∀ v, ContDiffAt ℝ ∞ (fun m => nm (M v m) * (dn (M v m))⁻¹) (TR.toL y.val) ∧
        ContDiffAt ℝ ∞ (fun m => jj (k v) (M v m)) (TR.toL y.val) := fun v => cd_parts (M v) _ (hE v) (hdt v) (k v)
    have hw : ∀ v, (nm (M v (TR.toL y.val)) * (dn (M v (TR.toL y.val)))⁻¹).im ≠ 0 := by
      intro v
      rw [hM, ← smul_iP]
      exact (gv v (y0 * y) • iP).2
    have h1 : ContDiffAt ℝ ∞ (fun m => Fx (fun z => f (z, x0)) (fun v => nm (M v m) * (dn (M v m))⁻¹))
        (TR.toL y.val) :=
      ContDiffAt.comp (g := Fx (fun z => f (z, x0))) (TR.toL y.val)
        ((hA (fun v => nm (M v (TR.toL y.val)) * (dn (M v (TR.toL y.val)))⁻¹) hw).contDiffAt.restrict_scalars ℝ)
        ((contDiffAt_pi (Φ := fun m v => nm (M v m) * (dn (M v m))⁻¹)).2 fun v => (hP v).1)
    have h2 : ContDiffAt ℝ ∞ (fun m => ∏ v, jj (k v) (M v m)) (TR.toL y.val) :=
      contDiffAt_prod fun v _ => (hP v).2
    have h3 : (∏ v, jj (k v) (M v (TR.toL y.val))) ≠ 0 := by
      simp only [hM, ← automorphy_factor_at_i_eq]
      exact hj (y0 * y)
    exact (h1.mul (h2.inv h3)).contDiffWithinAt
  · obtain ⟨y, rfl⟩ := id hm
    exact hG y

end UpperTheory.Esk.ImaginaryUnitActionLemmas

theorem UpperTheory.Esk.hyperbolic_orbit_bound_proof : UpperTheory.Esk.Osg → UpperTheory.Esk.B1b → UpperTheory.Esk.H2b := by
  intro hO hB F _ _ _ k c _ om χ _ _ _ _ f φ hf hR g
  exact UpperTheory.Esk.ImaginaryUnitActionLemmas.chart_smooth hO hB F k f φ hf.hol hR g
end
end

section
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

namespace UpperTheory.Esk.CasimirEigenvalueLemmas

theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {k c} {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : UpperTheory.Esk.IsHolV k c ω φ) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ.cent, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

theorem casimir {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = 0)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  _root_.UpperTheory.Reformulated.B.Qf10.casimir E hE k φ h0 h1 h2 u

end UpperTheory.Esk.CasimirEigenvalueLemmas

open UpperTheory.Esk.CasimirEigenvalueLemmas in
theorem UpperTheory.Esk.pf_HCap : UpperTheory.Esk.HCap := by
  intro F _ _ _ k c ω hω φ hφ
  refine ⟨by simpa using lie_scalar hω hφ 1, fun v u => ?_⟩
  have h0 : Eop v 0 0 φ + Eop v 1 1 φ = 0 := by
    classical
    rw [← lie_scalar hω hφ (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have := casimir _ (TR.glRel_Eop v) (k v) φ h0 (hφ.wt v) (hφ.low v) u
  rw [← this, TR.cap]
  norm_num
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.FiniteLevelGroupLemmas

def Gm (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) :
    (X (InfinitePlace F) × GF F → ℂ) →ₗ[ℂ] (GA F 2 → ℂ) where
  toFun f := Classical.choose ((h F k).1 f)
  map_add' f f' := by
    have e := (h F k).2.2.2.1 f f' _ _ 1 (Classical.choose_spec ((h F k).1 f)) (Classical.choose_spec ((h F k).1 f'))
    simp only [one_smul] at e
    exact (h F k).2.1 _ _ _ (Classical.choose_spec ((h F k).1 (f + f'))) e
  map_smul' s f := by
    have e := (h F k).2.2.2.1 0 f 0 _ s (h F k).2.2.2.2.1 (Classical.choose_spec ((h F k).1 f))
    simp only [zero_add] at e
    exact (h F k).2.1 _ _ _ (Classical.choose_spec ((h F k).1 (s • f))) e

theorem rel (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ)
    (f : X (InfinitePlace F) × GF F → ℂ) : Rel k f (Gm h F k f) :=
  Classical.choose_spec ((h F k).1 f)

theorem inj (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) :
    Function.Injective (Gm h F k) := by
  intro f f' e
  have h2 := rel h F k f'
  rw [← e] at h2
  exact (h F k).2.2.1 f f' _ (rel h F k f) h2

end UpperTheory.Esk.FiniteLevelGroupLemmas

theorem UpperTheory.Esk.pf_HFin : UpperTheory.Esk.HRel → UpperTheory.Esk.H2a → UpperTheory.Esk.H2d → UpperTheory.Esk.H2e → UpperTheory.Esk.HFinC → UpperTheory.Esk.HFin := by
  intro hR h2a h2d h2e hC F _ _ _ k c hc ω χ hω hχ hS hk
  classical
  let S : Set (TR.Sm F 2) := {φ | IsHolV k c ω φ ∧ TR.IsCuspForm φ}
  have : FiniteDimensional ℂ (Submodule.span ℂ S) := hC F k c hc ω hω
  let W : Submodule ℂ (GA F 2 → ℂ) := (Submodule.span ℂ S).map (TR.Sm F 2).subtype
  have : FiniteDimensional ℂ W := inferInstance
  let p := Submodule.span ℂ {f | (mkDat c χ).IsForm k f}
  have hle : p.map (FiniteLevelGroupLemmas.Gm hR F k) ≤ W := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hrel := FiniteLevelGroupLemmas.rel hR F k f
    obtain ⟨hs, hhol⟩ := h2d F k c hc ω χ hω hχ hS hk f _ hf hrel
    have hb := (h2a F k c hc ω χ hω hχ hS hk f _ hf hrel).2.2.2
    have hcusp := h2e F k c ω ⟨_, hs⟩ hω hk hhol hb
    exact ⟨⟨_, hs⟩, Submodule.subset_span ⟨hhol, hcusp⟩, rfl⟩
  have : FiniteDimensional ℂ (p.map (FiniteLevelGroupLemmas.Gm hR F k)) := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (FiniteLevelGroupLemmas.inj hR F k) p).symm
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc Matrix

namespace UpperTheory.Esk.HyperbolicSetupLemmas

section Gen

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem stab_open (ρ : Representation ℂ G V) (x : V) (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U)
    (hx : ∀ g ∈ U, ρ g x = x) : IsOpen {g | ρ g x = x} := by
  rw [isOpen_iff_mem_nhds]
  intro g₀ hg₀
  have ho : IsOpen ((fun g => g₀⁻¹ * g) ⁻¹' U) := hU.preimage (by fun_prop)
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using h1)) fun g hg => ?_
  have h2 : ρ (g₀⁻¹ * g) x = x := hx _ hg
  have hg₀' : ρ g₀ x = x := hg₀
  change ρ g x = x
  calc ρ g x = ρ g₀ (ρ (g₀⁻¹ * g) x) := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = x := by rw [h2, hg₀']

def smV (ρ : Representation ℂ G V) : Submodule ℂ V where
  carrier := {x | IsOpen {g | ρ g x = x}}
  add_mem' := fun {x y} hx hy => stab_open ρ _ _ (IsOpen.inter hx hy) ⟨by simp, by simp⟩
    fun g hg => by
      have h1 : ρ g x = x := hg.1
      have h2 : ρ g y = y := hg.2
      rw [map_add, h1, h2]
  zero_mem' := by
    change IsOpen {g | ρ g 0 = 0}
    simp only [map_zero, Set.setOf_true]
    exact isOpen_univ
  smul_mem' := fun a x hx => stab_open ρ _ _ hx (by simp) fun g hg => by
    have h1 : ρ g x = x := hg
    rw [map_smul, h1]

theorem smV_stable (ρ : Representation ℂ G V) (g : G) : smV ρ ≤ Submodule.comap (ρ g) (smV ρ) := by
  intro x hx
  change IsOpen {h | ρ h (ρ g x) = ρ g x}
  refine stab_open ρ _ ((fun h => g⁻¹ * h * g) ⁻¹' {h | ρ h x = x}) ((show IsOpen {h | ρ h x = x} from hx).preimage (by fun_prop))
    (by simp) fun h hh => ?_
  have e : ρ (g⁻¹ * h * g) x = x := hh
  calc ρ h (ρ g x) = ρ g (ρ (g⁻¹ * h * g) x) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc, mul_inv_cancel_left]
    _ = ρ g x := by rw [e]

theorem smV_smooth (ρ : Representation ℂ G V) : GlobalTheory.PRep.IsSmooth (ρ.subrepresentation (smV ρ) (smV_stable ρ)) := by
  intro x
  have e : {g | ρ.subrepresentation (smV ρ) (smV_stable ρ) g x = x} = {g | ρ g x.1 = x.1} := by
    ext g; exact Subtype.ext_iff
  rw [e]
  exact x.2

end Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem fix_of (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2) (hφ : IsHolV k c ω φ) :
    φ ∈ Hi.fixd (TR.finRep F 2) (Kc c) := by
  let ρ := (TR.finRep F 2).subrepresentation (smV (TR.finRep F 2)) (smV_stable _)
  have hx : φ ∈ smV (TR.finRep F 2) := hφ.aut.level
  have h := fixGlob F _ ρ (smV_smooth _) c ⟨φ, hx⟩ fun w u hu => Subtype.ext (hφ.level w u hu)
  intro u hu
  exact congrArg Subtype.val (h u hu)

private def rot (θ : TR.Rinf F) : GL (Fin 2) (TR.Rinf F) where
  val := !![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)]
  inv := !![fun v => Real.cos (θ v), fun v => -Real.sin (θ v); fun v => Real.sin (θ v), fun v => Real.cos (θ v)]
  val_inv := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith
  inv_val := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith

omit [NumberField F] [IsTotallyReal F] in
private theorem rot_add (θ θ' : TR.Rinf F) : rot (θ + θ') = rot θ * rot θ' := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

theorem sign_holV {k c} {ω : HChar F} {φ : TR.Sm F 2} (hφ : IsHolV k c ω φ) (h0 : φ ≠ 0) (v : InfinitePlace F) :
    ((ω.locInf v (-1) : ℂˣ) : ℂ) = Complex.exp (Complex.I * (k v : ℕ) * Real.pi) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (Subtype.ext (funext h))
  set e : TR.Rinf F := Pi.single v 1 with he
  have hr0 : rot ((0 : ℝ) • e) = 1 := by
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [rot]
  have hd0 : ∀ g, HasDerivAt (fun t : ℝ => φ.1 (g * TR.infGL F 2 (rot (t • e)))) (Complex.I * (k v : ℕ) * φ.1 g) 0 := fun g => by
    have h1 := TR.hasDerivAt_curve φ g (fun t : ℝ => rot (t • e))
      (TR.toL (Matrix.single 0 1 e) - TR.toL (Matrix.single 1 0 e)) hr0 (by
        refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
        have hc := ((hasDerivAt_id (0 : ℝ)).mul_const (e u)).cos
        have hs := ((hasDerivAt_id (0 : ℝ)).mul_const (e u)).sin
        fin_cases i <;> fin_cases j
        · simpa [rot] using hc
        · simpa [rot] using hs
        · simpa [rot] using hs.fun_neg
        · simpa [rot] using hc)
    rw [← TR.lie_apply, map_sub] at h1
    exact h1.congr_deriv (congrArg (fun x : TR.Sm F 2 => x.1 g) (hφ.wt v))
  set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rot (t • e))) with hf
  have hd : ∀ t, HasDerivAt f (Complex.I * (k v : ℕ) * f t) t := fun t => by
    have h1 := HasDerivAt.comp_sub_const t t ((sub_self t).symm ▸ hd0 (g * TR.infGL F 2 (rot (t • e))))
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [mul_assoc, ← map_mul, ← rot_add, ← add_smul, add_sub_cancel]
  have hc : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f t * Complex.exp (-(Complex.I * (k v : ℕ) * t))) 0 t := fun t => by
    have h1 := (hd t).mul (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * (k v : ℕ))).fun_neg.cexp)
    exact h1.congr_deriv (by simp; ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hc t).differentiableAt) (fun t => (hc t).deriv) Real.pi 0
  have hu : (1 - 2 * e) * (1 - 2 * e) = 1 := by
    funext w
    by_cases h : w = v
    · subst h; simp [he]; norm_num
    · simp [he, h]
  let u : (TR.Rinf F)ˣ := ⟨1 - 2 * e, 1 - 2 * e, hu, hu⟩
  have h3 : rot (Real.pi • e) = GeneralLinearGroup.scalar (Fin 2) u := by
    ext i j w
    by_cases h : w = v
    · subst h
      fin_cases i <;> fin_cases j <;> simp [rot, u, he] <;> norm_num
    · fin_cases i <;> fin_cases j <;> simp [rot, u, he, h]
  have h4 : Units.map (GlobalTheory.CuspRep.corner (TR.sInf F)) u = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1) := by
    refine Units.ext (Prod.ext (funext fun w => ?_) ?_)
    · change (1 - TR.infEq F 1 + TR.infEq F (1 - 2 * e)) w = Pi.mulSingle (M := fun w : InfinitePlace F => w.Completion) v (-1) w
      rw [map_one, sub_self, zero_add]
      change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm ((1 - 2 * e) w) = _
      by_cases h : w = v
      · subst h
        rw [show (1 - 2 * e) w = -1 by simp [he]; norm_num]
        simp
      · simp [he, h]
    · change (1 : Af F) - 0 + 0 = 1
      simp
  simp only [hf, hr0, h3, TR.infGL, map_one, mul_one] at h2
  rw [GlobalTheory.CuspRep.cornerGL_scalar, h4, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent] at h2
  rw [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, Complex.exp_neg, mul_right_comm,
    mul_eq_right₀ hg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at h2
  exact h2

theorem sgn_of {k c} {ω : HChar F} {φ : TR.Sm F 2} (hφ : IsHolV k c ω φ) (h0 : φ ≠ 0) : Sgn k ω := by
  intro v
  rw [sign_holV hφ h0 v, show Complex.I * ((k v : ℕ) : ℂ) * (Real.pi : ℂ) = (k v : ℕ) * ((Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_nat_mul, Complex.exp_pi_mul_I]

theorem fin_zc (z : (Af F)ˣ) : finGL F 2 (zc F z) = GeneralLinearGroup.scalar (Fin 2) (finId F z) := by
  rw [zc, finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  rfl

theorem chi_of {k c} {ω : HChar F} {φ : TR.Sm F 2} (hφ : IsHolV k c ω φ) (h0 : φ ≠ 0) : ∃ χ, IsChi c ω χ := by
  have hfix := fix_of k c ω φ hφ
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (Subtype.ext (funext h))
  have h1 : ∀ z, zc F z ∈ Kc c → (ω.1.comp (finId F)) z = 1 := by
    intro z hz
    have e := congrArg (fun ψ : TR.Sm F 2 => ψ.1 g) (hfix _ hz)
    change φ.1 (g * finGL F 2 (zc F z)) = φ.1 g at e
    rw [fin_zc, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent, mul_eq_right₀ hg] at e
    exact Units.ext e
  obtain ⟨χ, hχ⟩ := exChi (GF F) (Af F)ˣ (Kc c) (zc F) (ω.1.comp (finId F)) (fun z => zc_center z) h1
  exact ⟨χ, hχ⟩

end UpperTheory.Esk.HyperbolicSetupLemmas

open UpperTheory.Esk.HyperbolicSetupLemmas in
theorem UpperTheory.Esk.hyperbolic_terms_setup_proof : UpperTheory.Esk.H0 := by
  intro F _ _ _ k c ω φ hφ h0
  exact ⟨sgn_of hφ h0, fix_of k c ω φ hφ, chi_of hφ h0⟩
end
end

section
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.Esk.HyperbolicKernelContinuity

theorem norm_omega {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Ideles F) : ‖((ω.1 z : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  have e3 : ω.1 z ^ n = 1 := by
    have := DFunLike.congr_fun e2 z
    simpa using this
  have e4 : ((ω.1 z : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, e3, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one e4 hn.ne'

end UpperTheory.Esk.HyperbolicKernelContinuity

theorem UpperTheory.Esk.hyperbolic_kernel_continuity : UpperTheory.Esk.H1c := by
  intro F _ _ _ k c ω φ hω hφ hcusp
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cuspForms ((UpperTheory.V.Fb.isCuspForm_iff φ).1 hcusp)
  refine ⟨C, fun g => ?_⟩
  obtain ⟨s, y, hy, rfl⟩ := exists_centralSection_mul_mem_normOneGL g
  have hz : centralSection F 2 s = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (posIdeleHom F (rpowHom ((2 * Module.finrank ℚ F : ℝ))⁻¹ s)) := by
    refine Units.ext ?_
    ext i j
    simp [centralSection, scalarUnits_apply, coe_diagUnits, Matrix.diagonal_apply, Matrix.scalar_apply]
  rw [hz, hφ.cent, norm_mul, UpperTheory.Esk.HyperbolicKernelContinuity.norm_omega hω, one_mul]
  exact hC y hy
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.HyperbolicIntegrabilityLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem pInf_alg (v : InfinitePlace F) (x : F) :
    TR.pInf F (algebraMap F (Ad F) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  have e : TR.pInf F (algebraMap F (Ad F) x) v = (v.embedding x).re := by
    rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]
    change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap F (InfiniteAdeleRing F) x v) = _
    simp
  rw [e, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

omit [IsTotallyReal F] in
theorem fin_zc (u : (Af F)ˣ) : finGL F 2 (zc F u) = Matrix.GeneralLinearGroup.scalar (Fin 2) (finId F u) := by
  rw [zc, finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  rfl

def rr (γ : GL (Fin 2) F) : GL (Fin 2) (TR.Rinf F) := Matrix.GeneralLinearGroup.map ((TR.pInf F).comp (algebraMap F (Ad F))) γ

theorem gv_rr (c : Pl F → ℕ) (χ : Hc c →* ℂˣ) (γ : GL (Fin 2) F) (v : InfinitePlace F) : gv v (rr γ) = (mkDat c χ).r v γ :=
  Units.ext (Matrix.ext fun i j => pInf_alg v (γ i j))

theorem rat_eq (γ : GL (Fin 2) F) : ratGL F 2 γ = TR.infGL F 2 (rr γ) * finGL F 2 (jF F γ) := by
  rw [← TR.infGL_mul_finGL (ratGL F 2 γ)]
  rfl

omit [IsTotallyReal F] in
theorem sc_comm (s : Ideles F) (a : GA F 2) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) s * a = a * Matrix.GeneralLinearGroup.scalar (Fin 2) s :=
  Units.ext (Matrix.scalar_commute (s : Ad F) (fun _ => Commute.all _ _) a.val).eq

theorem aut (hb : B1b) (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (χ : Hc c →* ℂˣ) (φ : TR.Sm F 2) (hφ : TR.IsAutForm φ)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (γ : GL (Fin 2) F) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    f ((mkDat c χ).act γ (fun v => gv v g • iP), jF F γ * x) =
      (mkDat c χ).J k γ (fun v => gv v g • iP) * f ((fun v => gv v g • iP), x) := by
  have e1 : (mkDat c χ).act γ (fun v => gv v g • iP) = fun v => gv v (rr γ * g) • iP := funext fun v => by
    change (mkDat c χ).r v γ • gv v g • iP = _
    rw [map_mul, mul_smul, gv_rr c χ]
  have e4 : TR.infGL F 2 (rr γ * g) * finGL F 2 (jF F γ * x) = ratGL F 2 γ * (TR.infGL F 2 g * finGL F 2 x) := by
    rw [rat_eq, map_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (TR.infGL F 2 g), TR.infGL_comm, mul_assoc]
  have e5 : ∀ v, j1 (k v) (gv v (rr γ * g)) iP = j1 (k v) ((mkDat c χ).r v γ) (gv v g • iP) * j1 (k v) (gv v g) iP :=
    fun v => by rw [map_mul, hb.1, gv_rr c χ]
  rw [e1, ← hf, ← hf, e4, hφ.left, Finset.prod_congr rfl fun v _ => e5 v, Finset.prod_mul_distrib]
  change _ = (∏ v, j1 (k v) ((mkDat c χ).r v γ) (gv v g • iP)) * _
  ring

theorem lev (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (χ : Hc c →* ℂˣ) (hχ : IsChi c ω χ) (φ : TR.Sm F 2)
    (hcent : ∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g)
    (hfix : ∀ u ∈ Kc c, TR.finRep F 2 u φ = φ)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) (h : Hc c) :
    f ((fun v => gv v g • iP), x * (h : GF F)) = ((χ h : ℂˣ) : ℂ) * f ((fun v => gv v g • iP), x) := by
  obtain ⟨⟨κ, hκ, z0, hz⟩, hv⟩ := hχ h
  have e5 : φ.1 (TR.infGL F 2 g * finGL F 2 x * finGL F 2 κ) = φ.1 (TR.infGL F 2 g * finGL F 2 x) :=
    congrArg (fun ψ : TR.Sm F 2 => ψ.1 (TR.infGL F 2 g * finGL F 2 x)) (hfix κ hκ)
  have e6 : TR.infGL F 2 g * finGL F 2 (x * (h : GF F)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (finId F z0) * (TR.infGL F 2 g * finGL F 2 x * finGL F 2 κ) := by
    rw [hz, map_mul, map_mul, fin_zc, sc_comm]
    simp only [mul_assoc]
  rw [← hf, ← hf, hv κ hκ z0 hz, e6, hcent, e5, mul_assoc]

theorem bdd (hb : B1b) (k : InfinitePlace F → ℕ) (φ : TR.Sm F 2) (C : ℝ) (hC : ∀ g, ‖φ.1 g‖ ≤ C)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    ‖f ((fun v => gv v g • iP), x)‖ * nrm k (fun v => gv v g • iP) ≤ C := by
  have e : ∀ v, ‖j1 (k v) (gv v g) iP‖ * |(gv v g • iP).1.im| ^ ((k v : ℝ) / 2) = 1 := fun v => by
    rw [hb.2.2.2.2.1]
    simp [iP]
  rw [← hf g x, norm_mul, nrm, norm_prod, mul_assoc, ← Finset.prod_mul_distrib]
  simp only [e, Finset.prod_const_one, mul_one]
  exact hC _

end UpperTheory.Esk.HyperbolicIntegrabilityLemmas

open UpperTheory.Esk in
theorem UpperTheory.Esk.hyperbolic_terms_integrable_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.H0 → UpperTheory.Esk.H1a → UpperTheory.Esk.H1b → UpperTheory.Esk.H1c → UpperTheory.Esk.H1 := by
  intro hb hc h0 h1a h1b h1c F _ _ _ k c ω χ hω hχ φ hφ hcusp
  obtain ⟨f, hf⟩ := h1a F k c ω φ hω hφ
  refine ⟨f, ⟨h1b F k c ω φ hω hφ f hf, fun γ z x => ?_, fun z x h => ?_, ?_⟩, hf⟩
  · obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    exact HyperbolicIntegrabilityLemmas.aut hb k c χ φ hφ.aut f hf γ g x
  · obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    by_cases h0φ : φ = 0
    · have e : ∀ g x, f (fun v => gv v g • iP, x) = 0 := fun g x => by rw [← hf g x, h0φ]; simp
      change f (_, x * (h : GF F)) = ((χ h : ℂˣ) : ℂ) * f (_, x)
      rw [e, e, mul_zero]
    obtain ⟨-, hfix, -⟩ := h0 F k c ω φ hφ h0φ
    exact HyperbolicIntegrabilityLemmas.lev k c ω χ hχ φ hφ.cent hfix f hf g x h
  · obtain ⟨C, hC⟩ := h1c F k c ω φ hω hφ hcusp
    refine ⟨C, fun z x => ?_⟩
    obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    exact HyperbolicIntegrabilityLemmas.bdd hb k φ C hC f hf g x
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.TraceCongruenceBounds

open UpperTheory.Esk

theorem nu_two {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (ι : Qbar l ≃+* ℂ) : nu ι 2 = 1 := by
  have hle : ∀ m : ℕ, nu ι (m : ℂ) ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.cast_succ]; exact (nu ι).map_add_le ih (by simp)
  have hlt : nu ι (l : ℂ) < 1 := by
    rw [nu_apply, map_natCast, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l]
    exact lt_of_eq_of_lt (PadicAlgCl.norm_extends l _) Padic.norm_p_lt_one
  obtain ⟨m, hm⟩ := (Fact.out : l.Prime).odd_of_ne_two hl
  refine le_antisymm (by simpa using hle 2) (not_lt.1 fun h2 => ?_)
  have e : (1 : ℂ) = (l : ℂ) - 2 * (m : ℂ) := by rw [hm]; push_cast; ring
  have : nu ι ((l : ℂ) - 2 * (m : ℂ)) < 1 := by
    refine (nu ι).map_sub_lt hlt ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hle m)) h2
  rw [← e, map_one] at this
  exact lt_irrefl _ this

theorem sum_bound (ν : Valuation ℂ ℝ≥0) {β : Type*} (s : Finset β) (u x y : β → ℂ) (m : ℝ≥0)
    (hu : ∀ j ∈ s, ν (u j) ≤ 1)
    (h : ∀ j ∈ s, u j ≠ 0 → ν (x j) ≤ 1 ∧ ν (y j) ≤ 1 ∧ ν (x j - y j) ≤ m) :
    ν (∑ j ∈ s, u j * x j) ≤ 1 ∧ ν (∑ j ∈ s, u j * y j) ≤ 1 ∧
      ν (∑ j ∈ s, u j * x j - ∑ j ∈ s, u j * y j) ≤ m := by
  have key : ∀ j ∈ s, ∀ (z : ℂ) (b : ℝ≥0), (u j ≠ 0 → ν z ≤ b) → ν (u j * z) ≤ b := by
    intro j hj z b hz
    by_cases h0 : u j = 0
    · simp [h0]
    · rw [map_mul]
      exact le_trans (mul_le_mul' (hu j hj) (hz h0)) (by simp)
  refine ⟨ν.map_sum_le fun j hj => key j hj _ _ fun h0 => (h j hj h0).1,
    ν.map_sum_le fun j hj => key j hj _ _ fun h0 => (h j hj h0).2.1, ?_⟩
  rw [← Finset.sum_sub_distrib]
  refine ν.map_sum_le fun j hj => ?_
  rw [← mul_sub]
  exact key j hj _ _ fun h0 => (h j hj h0).2.2

theorem geo_expand {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf) (k : I → ℕ) {n : ℕ}
    (a : Fin n → Gf) (S : Finset (D.Cj × D.Om)) (z : ℂ) :
    z * geo D k a S = ∑ q ∈ S ×ˢ (Finset.univ : Finset (Fin n)),
      ((Nat.card (MulAction.stabilizer (PG F) q.1) : ℂ)⁻¹ *
        D.ee ((D.rep q.1.2)⁻¹ * (D.j (D.el q.1.1).out)⁻¹ * D.rep q.1.2 * a q.2)) *
      (z * D.orb k (D.el q.1.1).out) := by
  rw [Finset.sum_product, geo, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Dat.Te, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem ee_mem {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) {x : Gf} (h : D.ee x ≠ 0) : x ∈ D.H := by
  by_contra hx
  exact h (by simp [Dat.ee, hx])

theorem nu_ee {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)
    {m : ℕ} (hm0 : 0 < m) (hm : ∀ h, D.χ h ^ m = 1) (x : Gf) : nu ι (D.ee x) ≤ 1 := by
  unfold Dat.ee
  split_ifs with hx
  · have e : (nu ι (D.χ ⟨x, hx⟩ : ℂ)) ^ m = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hm, Units.val_one, map_one]
    exact (pow_le_one_iff hm0.ne').1 e.le
  · simp

theorem nu_card {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (ι : Qbar l ≃+* ℂ) {G : Type*} [Group G] (S : Subgroup G)
    (hS : ∃ n, Nat.card S = 2 ^ n) : nu ι ((Nat.card S : ℂ)⁻¹) = 1 := by
  obtain ⟨n, hn⟩ := hS
  rw [map_inv₀, hn, Nat.cast_pow, map_pow, Nat.cast_ofNat, nu_two hl, one_pow, inv_one]

theorem stab_le {G A B : Type*} [Group G] [MulAction G A] [MulAction G B] (p : A × B) :
    MulAction.stabilizer G p ≤ MulAction.stabilizer G p.2 := fun g hg => by
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  exact congrArg Prod.snd hg

theorem geo_bound (ν : Valuation ℂ ℝ≥0) {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)
    (k k' : I → ℕ) {n : ℕ} (a : Fin n → Gf) (S : Finset (D.Cj × D.Om)) (z z' : ℂ) (m : ℝ≥0)
    (hu : ∀ p ∈ S, ∀ i, ν ((Nat.card (MulAction.stabilizer (PG F) p) : ℂ)⁻¹ *
        D.ee ((D.rep p.2)⁻¹ * (D.j (D.el p.1).out)⁻¹ * D.rep p.2 * a i)) ≤ 1)
    (h : ∀ p ∈ S, ∀ i, D.ee ((D.rep p.2)⁻¹ * (D.j (D.el p.1).out)⁻¹ * D.rep p.2 * a i) ≠ 0 →
      ν (z * D.orb k (D.el p.1).out) ≤ 1 ∧ ν (z' * D.orb k' (D.el p.1).out) ≤ 1 ∧
        ν (z * D.orb k (D.el p.1).out - z' * D.orb k' (D.el p.1).out) ≤ m) :
    ν (z * geo D k a S) ≤ 1 ∧ ν (z' * geo D k' a S) ≤ 1 ∧ ν (z * geo D k a S - z' * geo D k' a S) ≤ m := by
  rw [geo_expand, geo_expand]
  refine sum_bound ν _ _ _ _ m (fun q hq => hu q.1 (Finset.mem_product.1 hq).1 q.2) fun q hq hne => ?_
  exact h q.1 (Finset.mem_product.1 hq).1 q.2 (right_ne_zero_of_mul hne)

end UpperTheory.Esk.TraceCongruenceBounds

open UpperTheory.Esk UpperTheory.Esk.TraceCongruenceBounds in
theorem UpperTheory.Esk.pf_TrCong : UpperTheory.Esk.TF → UpperTheory.Esk.DAx → UpperTheory.Esk.DTwo → UpperTheory.Esk.DGood → UpperTheory.Esk.GTerm → UpperTheory.Esk.H0b → UpperTheory.Esk.HFin → UpperTheory.Esk.TrCong := by
  intro hTF hDAx hTwo hGood hGT hH0b hFin
  intro F _ _ _ hd l _ hl ι L k₀ hk₀ c hc hcL hu ω χ hω hχ hS N t ht W r hr hW n a hreps h h'
  obtain ⟨⟨m, hm0, hm⟩, hsg⟩ := hH0b F (fun _ => k₀) c ω χ hω hχ
  have hS' : Sgn (fun v => k₀ + 2 * t v) ω := fun v => by
    rw [hS v, pow_add, pow_mul]; simp
  have hax : (mkDat c χ).Ax := hDAx F hd c hc χ ⟨m, hm0, hm⟩
  obtain ⟨hgood, hreg⟩ := hGood F c ω χ hχ W n a hreps
  have hreg' : (mkDat c χ).Reg a := by
    apply hreg
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    classical
    exact ⟨L.pl v, List.count_pos_iff.1 (le_trans hr (hW v)), by rw [hcL v]; exact one_ne_zero⟩
  obtain ⟨S, hFam, hT⟩ := hTF F (InfinitePlace F) (GF F) (mkDat c χ) hax (Fin n) a
  have hyp0 : (mkDat c χ).Hyp (fun _ => k₀) a := ⟨hax, fun _ => hk₀, (hsg hS).1, hgood, hreg'⟩
  have hyp1 : (mkDat c χ).Hyp (fun v => k₀ + 2 * t v) a :=
    ⟨hax, fun _ => by omega, ((hH0b F _ c ω χ hω hχ).2 hS').1, hgood, hreg'⟩
  have fd0 : FiniteDimensional ℂ ((mkDat c χ).M fun _ => k₀) := hFin F _ c hc ω χ hω hχ hS fun _ => by omega
  have fd1 : FiniteDimensional ℂ ((mkDat c χ).M fun v => k₀ + 2 * t v) :=
    hFin F _ c hc ω χ hω hχ hS' fun _ => by omega
  rw [hT _ hyp0 fd0 h, hT _ hyp1 fd1 h']
  refine geo_bound (nu ι) (mkDat c χ) _ _ a S _ _ _ ?_ ?_
  · intro p hp i
    have hp' := hFam p hp
    rw [map_mul, nu_card hl ι _ (hTwo F c χ hu p.2 _ (stab_le p) hp'.2), one_mul]
    exact nu_ee ι _ hm0 hm _
  · intro p hp i hne
    exact hGT F l ι L c χ hcL k₀ (by omega) N t ht W r hr hW n a hreps _ _ i (hFam p hp).1 (ee_mem _ hne)
end
end

section
namespace UpperTheory.Esk

theorem s_GCh : GCh := pf_GCh
theorem s_GUnit : GUnit := pf_GUnit
theorem s_GMod : GMod := pf_GMod
theorem hyperbolic_orbit_integral_holds : H0b := hyperbolic_orbit_integral_proof
theorem s_HRel : HRel := pf_HRel automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds
theorem hyperbolic_relation_holds : H2a := hyperbolic_relation_proof automorphy_factor_kernel_algebra_holds hyperbolic_orbit_integral_holds
theorem hyperbolic_orbit_bound_holds : H2b := hyperbolic_orbit_bound_proof s_Osg automorphy_factor_kernel_algebra_holds
theorem hyperbolic_orbit_summable_holds : H2c := hyperbolic_orbit_summable_proof s_Osg automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds
theorem hyperbolic_tail_estimate_holds : H2d := hyperbolic_tail_estimate_proof automorphy_factor_kernel_algebra_holds hyperbolic_relation_holds hyperbolic_orbit_bound_holds hyperbolic_orbit_summable_holds
theorem hyperbolic_finite_sum_identity_holds : H2e := pf_H2e
theorem s_HCap : HCap := pf_HCap
theorem s_HFinC : HFinC := pf_HFinC s_HCap
theorem s_HFin : HFin := pf_HFin s_HRel hyperbolic_relation_holds hyperbolic_tail_estimate_holds hyperbolic_finite_sum_identity_holds s_HFinC
theorem hyperbolic_terms_setup_holds : H0 := hyperbolic_terms_setup_proof
theorem hyperbolic_kernel_algebra_holds : H1a := hyperbolic_kernel_algebra_proof automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds
theorem hyperbolic_kernel_measurable_holds : H1b := hyperbolic_kernel_measurable_proof half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds
theorem hyperbolic_kernel_continuity_holds : H1c := hyperbolic_kernel_continuity
theorem hyperbolic_terms_integrable_holds : H1 := hyperbolic_terms_integrable_proof automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds hyperbolic_terms_setup_holds hyperbolic_kernel_algebra_holds hyperbolic_kernel_measurable_holds hyperbolic_kernel_continuity_holds

theorem holWC_of (dAx : DAx) (dTwo : DTwo) (dGood : DGood) (dReps : DReps) (g : GTerm) : HolWC :=
  pf_HolWC finite_system_holds forms_stable_under_operators_holds dAx dReps dGood (pf_TrCong s_TF dAx dTwo dGood g hyperbolic_orbit_integral_holds s_HFin) hyperbolic_terms_setup_holds hyperbolic_orbit_integral_holds s_HRel hyperbolic_terms_integrable_holds s_HFin hyperbolic_relation_holds hyperbolic_tail_estimate_holds hyperbolic_finite_sum_identity_holds

end UpperTheory.Esk
end
