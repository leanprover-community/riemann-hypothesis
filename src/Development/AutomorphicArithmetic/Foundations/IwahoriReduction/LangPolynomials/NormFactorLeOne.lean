import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormOfDvd
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumAlg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobEx
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PConj
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PolyEx
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsClosedInertiaCyclotomicKernelStatement
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.SerMulPow
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepUniq
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresMono
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresTr
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepSmul
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Period
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DivEqZeroOfCg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.HtvExpand
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormSubLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaElementsUnramifiedOrdinaryOfEulerSystemInert
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonvanishingTransferCharacterSumsPowerSeriesStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientCharTrivialInertiaCyclotomicTower

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.ToBasisLogarithm

variable {l : ℕ} [Fact l.Prime]

private theorem norm_alg_le (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  exact z.2

private theorem norm_nat_le (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 := by
  simpa using norm_alg_le (l := l) (a : ℤ_[l])

private theorem cg_sum {ι : Type} [Fintype ι] (n : ℕ) (f g : ι → Qbar l) (h : ∀ i, Cg n (f i) (g i)) :
    Cg n (∑ i, f i) (∑ i, g i) := by
  unfold Cg
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => h i

private theorem cg_mul {n : ℕ} {a b y : Qbar l} (h : Cg n a b) (hy : ‖y‖ ≤ 1) : Cg n (a * y) (b * y) := by
  unfold Cg at *
  rw [← sub_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans h

private theorem cg_trans {n : ℕ} {a b c : Qbar l} (h : Cg n a b) (h' : Cg n b c) : Cg n a c := by
  unfold Cg at *
  rw [show a - c = (a - b) + (b - c) by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cg_nat {n x y : ℕ} (h : (x : ZMod (l ^ n)) = y) : Cg n (x : Qbar l) y := by
  obtain ⟨e, he⟩ := (Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h).symm)
  have he' : (x : Qbar l) - y = (l : Qbar l) ^ n * (e : Qbar l) := by exact_mod_cast congrArg (Int.cast : ℤ → Qbar l) he
  have hn : ‖(e : Qbar l)‖ ≤ 1 := by simpa using norm_alg_le (l := l) (e : ℤ_[l])
  unfold Cg
  rw [he', norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hn

private theorem coords {c : Coef l} (β : Bas c) (hβ : ∀ i, ‖β.val i‖ ≤ 1) (n : ℕ) (o : Qbar l) (ho : o ∈ c.O) :
    ∃ a : Fin β.d → ℕ, Cg n o (∑ i, β.val i * (a i : Qbar l)) := by
  refine ⟨fun i => (β.e.repr ⟨o, ho⟩ i).appr n, ?_⟩
  have h1 : o = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i) := by
    have := congrArg (fun x : c.O => (x : PadicAlgCl l)) (β.e.sum_repr ⟨o, ho⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul] at this
    refine this.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Algebra.smul_def, mul_comm]; rfl
  refine cg_trans (b := ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i)) ?_ (cg_sum n _ _ fun i => ?_)
  · unfold Cg; rw [← h1, sub_self, norm_zero]; exact norm_nonneg _
  · rw [mul_comm (β.val i), mul_comm (β.val i)]
    refine cg_mul ?_ (hβ i)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n (β.e.repr ⟨o, ho⟩ i))
    have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) he
    rw [map_mul, map_pow, map_natCast, map_sub, map_natCast] at this
    unfold Cg
    rw [← this, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_alg_le e)

private theorem cg_swap {ι : Type} [Fintype ι] {d n : ℕ} (b : Fin d → Qbar l) (o y : ι → Qbar l) (a : ι → Fin d → ℕ)
    (h : ∀ k, Cg n (o k) (∑ i, b i * (a k i : Qbar l))) (hy : ∀ k, ‖y k‖ ≤ 1) :
    Cg n (∑ k, o k * y k) (∑ i, b i * ∑ k, (a k i : Qbar l) * y k) := by
  have e : ∑ i, b i * ∑ k, (a k i : Qbar l) * y k = ∑ k, (∑ i, b i * (a k i : Qbar l)) * y k := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [e]
  exact cg_sum n _ _ fun k => cg_mul (h k) (hy k)

private theorem logd {Ω : Type} [Field Ω] {ι : Type} (S : Finset ι) (P : ι → Polynomial Ω) (a : ι → ℕ) (z : Ω)
    (hP : ∀ k, (P k).eval z ≠ 0) :
    z * (Polynomial.derivative (∏ k ∈ S, P k ^ a k)).eval z / (∏ k ∈ S, P k ^ a k).eval z =
      ∑ k ∈ S, (a k : Ω) * (z * (Polynomial.derivative (P k)).eval z / (P k).eval z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have h0 : (∏ k ∈ S, P k ^ a k).eval z ≠ 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_ne_zero_iff.2 fun k _ => by rw [Polynomial.eval_pow]; exact pow_ne_zero _ (hP k)
    have hk0 := hP k
    rw [Finset.prod_insert hk, Finset.sum_insert hk, ← ih, Polynomial.derivative_mul, Polynomial.derivative_pow]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    rcases a k with _ | r
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]
      field_simp

private theorem pv_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) {z : Ω} (hz : z ∈ A) :
    (P.map (R0 A).subtype).eval z ∈ A := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, Polynomial.eval_add]; exact A.add_mem _ _ hp hq
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.eval_monomial]
    exact A.mul_mem _ _ a.2.1 (A.toSubring.pow_mem hz n)

private theorem pv_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) (z : Ω)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) :
    (P.map (R0 A).subtype).eval (s z) = s ((P.map (R0 A).subtype).eval z) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, Polynomial.eval_add, Polynomial.eval_add, map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial, map_mul, map_pow]
    congr 1
    exact (a.2.2 s hs).symm

private theorem root_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {z : Ω} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) : z ∈ A := by
  rcases A.mem_or_inv_mem z with h | h
  · exact h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    have e : z = (z⁻¹) ^ k := by
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_right (by rw [← hz, pow_succ])
    rw [e]; exact A.toSubring.pow_mem h k

private theorem ex_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω}
    (h : ∀ u : ℤ_[l]ˣ, ∃ s ∈ Ine (F := ℚ) A, cycZ ℚ Ω l s = u) {m : ℕ} (hm : 1 ≤ m) {z : Ω} (hz : z ^ l ^ m = 1)
    (b : (ZMod (l ^ m))ˣ) : ∃ s ∈ Ine (F := ℚ) A, s z = z ^ (b : ZMod (l ^ m)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hc : ((b : ZMod (l ^ m)).val).Coprime l :=
    Nat.Coprime.coprime_dvd_right (dvd_pow_self l (by omega)) (ZMod.val_coe_unit_coprime b)
  have hu : IsUnit (((b : ZMod (l ^ m)).val : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 hc.symm
  obtain ⟨s, hs, hs'⟩ := h hu.unit
  refine ⟨s, hs, ?_⟩
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) z hz
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)) = hu.unit := hs'
  rw [h2, IsUnit.unit_spec, map_natCast, ZMod.natCast_zmod_val] at h1
  exact h1

end UpperTheory.Kd.C7.ToBasisLogarithm

open UpperTheory.Kd.C7.ToBasisLogarithm in
theorem UpperTheory.Kd.C7.pToBasis :
    UpperTheory.Kd.C7.SToBasis := by
  intro l _ hl Ω _ _ _ A hA c β ζ hζ j hj Z m n ι _ P o hm hP ho hK
  classical
  obtain ⟨hprim, hnm, hu, ho1, hpres⟩ := hK
  have hβ := ((pBasEx l c).2 β).1
  have hfr := (pFrobEx l hl Ω A hA).2.2
  choose a ha using fun k => coords β hβ n (o k) (ho k)
  have hQ : ∀ k, ∃ Q : Polynomial (R0 A), Q.map (R0 A).subtype = P k := fun k =>
    ⟨(P k).toSubring (R0 A) (fun x hx => hP k x hx), Polynomial.map_toSubring _ _ _⟩
  choose Q hQ using hQ
  have hmap : ∀ i, (∏ k, Q k ^ a k i).map (R0 A).subtype = ∏ k, P k ^ a k i := fun i => by
    simp only [Polynomial.map_prod, Polynomial.map_pow, hQ]
  have hpv : ∀ i, pv (∏ k, Q k ^ a k i) (ζ m) = ∏ k, (P k).eval (ζ m) ^ a k i := fun i => by
    rw [pv, Polynomial.eval₂_eq_eval_map, hmap, Polynomial.eval_prod]
    simp only [Polynomial.eval_pow]
  refine ⟨fun i => ∏ k, Q k ^ a k i, ⟨hprim, hnm, fun i => ?_, hβ, fun s hs hc hz => ?_⟩, fun b => ?_⟩
  · dsimp only
    rw [hpv]
    refine ⟨A.toSubring.prod_mem fun k _ => A.toSubring.pow_mem (hu k).1 _,
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hu k).2.1, ?_⟩
    rw [← Finset.prod_inv_distrib]
    exact A.toSubring.prod_mem fun k _ => by rw [← inv_pow]; exact A.toSubring.pow_mem (hu k).2.2 _
  · obtain ⟨κ, hκ, hcg⟩ := hpres s hs hc hz
    have hKA := (pKumAlg l hl Ω A hA ζ hζ m n hnm s ⟨hs, hc⟩).1
    refine ⟨fun i => ∑ k, (a k i : ZMod (l ^ n)) * κ k, fun i => ?_, ?_⟩
    · dsimp only
      rw [hpv]
      generalize (Finset.univ : Finset ι) = S
      induction S using Finset.induction_on with
      | empty => simpa using kumVal_one (l := l) n (ζ n) s
      | insert k S hk ih =>
        rw [Finset.prod_insert hk, Finset.sum_insert hk]
        exact (hKA _ _ _ _ ((hKA _ _ _ _ (hκ k) (hκ k)).2.2 (a k i)) ih).1
    · refine cg_trans hcg (cg_trans (cg_swap β.val o _ a ha fun k => norm_nat_le _) (cg_sum n _ _ fun i => ?_))
      rw [mul_comm (β.val i), mul_comm (β.val i)]
      refine cg_mul ?_ (hβ i)
      haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      have := cg_nat (l := l) (n := n) (x := ∑ k, a k i * (κ k).val) (y := (∑ k, (a k i : ZMod (l ^ n)) * κ k).val)
        (by simp)
      simpa using this
  · obtain ⟨s, hs, hsz⟩ := ex_conj hfr hm (hζ m).1.pow_eq_one b
    have hzA : ζ m ∈ A := root_mem A (pow_pos (Fact.out : l.Prime).pos m) (hζ m).1.pow_eq_one
    have hz : ζ m ^ (b : ZMod (l ^ m)).val ∈ A := A.toSubring.pow_mem hzA _
    have hev : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) = s ((P k).eval (ζ m)) := fun k => by
      rw [← hsz, ← hQ, pv_conj _ _ hs]
    have hne : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) ≠ 0 := fun k => by
      rw [hev]; exact (map_ne_zero s).2 (hu k).2.1
    unfold htv
    simp only [hmap, logd _ P _ _ hne, map_sum, map_mul j, map_natCast]
    refine cg_swap β.val o _ a ha fun k => hj _ ?_
    rw [div_eq_mul_inv]
    refine A.mul_mem _ _ (A.mul_mem _ _ hz ?_) ?_
    · rw [← hQ, Polynomial.derivative_map]; exact pv_mem _ hz
    · rw [hev, ← map_inv₀, apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs)]; exact (hu k).2.2
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem cg_mono {l : ℕ} [Fact l.Prime] {n N : ℕ} (h : n ≤ N) {a b : Qbar l} (hc : Cg N a b) : Cg n a b := by
  unfold Cg at *
  refine hc.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) h

private theorem cg_down {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {A : ValuationSubring Ω}
    {Z : Sy Ω l} (hZ : IwI c A Z) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (n r : ℕ) :
    ∀ d, (∀ x, Cg n (Z (r + d) s x) 0) → ∀ x, Cg n (Z r s x) 0 := by
  intro d
  induction d with
  | zero => intro h; simpa using h
  | succ d ih =>
    intro h
    apply ih
    intro x
    have hsum := hZ.nrm (r + d) s hs x
    unfold Cg at h ⊢
    rw [sub_zero, hsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
    intro x' _
    have := h x'
    rw [sub_zero] at this
    exact this

private theorem unit_lift (l : ℕ) [Fact l.Prime] (m : ℕ) (hm : 1 ≤ m) (x : (ZMod (l ^ m))ˣ) :
    ∃ u : ℤ_[l]ˣ, PadicInt.toZModPow m (u : ℤ_[l]) = x := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Fact (1 < l ^ m) := ⟨Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt⟩
  have hsurj : Function.Surjective (PadicInt.toZModPow (p := l) m) := by
    intro y
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective y
    exact ⟨k, map_natCast _ k⟩
  obtain ⟨u, hu⟩ := IsLocalRing.surjective_units_map_of_local_ringHom _ hsurj hsurj.isLocalHom x
  exact ⟨u, congrArg Units.val hu⟩

theorem UpperTheory.Kd.C7.pContOf :
    UpperTheory.Kd.C7.SContOf := by
  unfold UpperTheory.Kd.C7.SContOf
  intro l _ hl2 Ω _ _ _ A hA c β ζ hζ Z hZ hP
  obtain ⟨c₀, m₀, hP⟩ := hP
  intro r n
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  set m := r + (m₀ + n + c₀ + 1) with hm_def
  have hm0 : m₀ ≤ m := by omega
  obtain ⟨P, hKP⟩ := hP m hm0
  set N := m - c₀ with hN
  obtain ⟨hprim, hNm, hu, ho, hk⟩ := hKP
  have hlN : 0 < l ^ N := pow_pos (Fact.out : l.Prime).pos N
  choose w hw using fun i : Fin β.d => IsAlgClosed.exists_pow_nat_eq (pv (P i) (ζ m)) hlN
  have hfe := UpperTheory.Kd.C7.pFrobEx l hl2 Ω A hA
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hlift : ∀ y : (ZMod (l ^ m))ˣ, ∃ t ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m t = y⁻¹ := by
    intro y
    obtain ⟨u, hu'⟩ := unit_lift l m (by omega) y⁻¹
    obtain ⟨t, ht, htu⟩ := hfe.2.2 u
    refine ⟨t, ht, ?_⟩
    ext
    simp [ReciprocityTheory.Gal.cycMod, htu, hu']
  choose tt htt hcyc using hlift
  let f : (ZMod (l ^ m))ˣ × Option (Fin β.d) → Ω := fun q => (tt q.1)⁻¹ (q.2.elim (ζ N) w)
  let E := IntermediateField.adjoin ℚ (Set.range f)
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)
  refine ⟨(cycMod ℚ Ω l m).ker ⊓ E.fixingSubgroup, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    refine IsOpen.inter ?_ E.fixingSubgroup_isOpen
    have := (GlobalTheory.KZ.IwC.isLocallyConstant_cycMod (Ω := Ω) (l := l) m).isOpen_fiber 1
    rw [MonoidHom.coe_ker]
    exact this
  · intro s hsU hs
    obtain ⟨hsk, hsE⟩ := Subgroup.mem_inf.mp hsU
    have hfix : ∀ q, s (f q) = f q := by
      intro q
      exact (mem_fixingSubgroup_iff _).mp hsE (f q) (IntermediateField.subset_adjoin ℚ _ ⟨q, rfl⟩)
    apply cg_down hZ hs n r (m₀ + n + c₀ + 1)
    intro y
    have hsH : s ∈ Hm l A m := by
      unfold UpperTheory.Kd.C7.Hm
      exact Subgroup.mem_inf.mpr ⟨hs, hsk⟩
    obtain ⟨hconjH, hconj⟩ := UpperTheory.Kd.C7.pConj l hl2 Ω A hA c Z hZ m s hsH (tt y) (htt y)
    have hZeq : Z m (tt y * s * (tt y)⁻¹) 1 = Z m s y := by
      rw [hconj]
      simp [hcyc]
    have hconjH' := hconjH
    unfold UpperTheory.Kd.C7.Hm at hconjH'
    have hs'I := (Subgroup.mem_inf.mp hconjH').1
    have hs'k : cycMod ℚ Ω l m (tt y * s * (tt y)⁻¹) = 1 := (Subgroup.mem_inf.mp hconjH').2
    have hs'fix : ∀ o : Option (Fin β.d),
        (tt y * s * (tt y)⁻¹) (o.elim (ζ N) w) = o.elim (ζ N) w := by
      intro o
      have h := hfix (y, o)
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, ← AlgEquiv.mul_apply, mul_inv_cancel,
        AlgEquiv.one_apply]
    have hz : (tt y * s * (tt y)⁻¹) (ζ N) = ζ N := hs'fix none
    obtain ⟨k, hkv, hcg⟩ := hk _ hs'I hs'k hz
    have hk0 : ∀ i, k i = 0 := by
      intro i
      have hwi : (tt y * s * (tt y)⁻¹) (w i) = w i := hs'fix (some i)
      have h0 : KumVal N (ζ N) (pv (P i) (ζ m)) (tt y * s * (tt y)⁻¹) 0 :=
        ⟨w i, hw i, by rw [hwi]; simp⟩
      exact kumVal_unique hprim hz (hu i).2.1 (hkv i) h0
    rw [← hZeq]
    apply cg_mono (n := n) (N := N) (by omega)
    simpa [hk0] using hcg
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem div_mem_of {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω)
    (t : G ℚ Ω) (ht : ∀ x ∈ A, t x ∈ A) (u : Ω) (hu : u ≠ 0) : u / t u ∈ A ∧ t u / u ∈ A := by
  have hfin : ∃ N : ℕ, (t ^ (N + 1)) u = u := by
    have hint : IsIntegral ℚ u := Algebra.IsIntegral.isIntegral u
    have hf : ((minpoly ℚ u).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
    have hm : ∀ k : ℕ, (t ^ k) u ∈ (minpoly ℚ u).rootSet Ω := fun k => by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero hint, ?_⟩
      rw [Polynomial.aeval_algEquiv]
      simp
    obtain ⟨i, j, hij, he⟩ := hf.exists_lt_map_eq_of_forall_mem hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    refine ⟨d, ?_⟩
    rw [add_assoc, pow_add, AlgEquiv.mul_apply] at he
    exact ((t ^ i).injective he).symm
  obtain ⟨N, hN⟩ := hfin
  have hne : ∀ k : ℕ, (t ^ k) u ≠ 0 := fun k => (map_ne_zero _).2 hu
  have htu : t u ≠ 0 := (map_ne_zero _).2 hu
  have hs : ∀ k : ℕ, (t ^ (k + 1)) u = t ((t ^ k) u) := fun k => by rw [pow_succ', AlgEquiv.mul_apply]
  rcases A.mem_or_inv_mem (t u / u) with h | h
  · have key : ∀ k : ℕ, (t ^ k) u / u ∈ A := by
      intro k
      induction k with
      | zero => simp [hu, A.one_mem]
      | succ k ih =>
        have := A.mul_mem _ _ (ht _ ih) h
        rwa [map_div₀, div_mul_div_cancel₀ htu, ← hs] at this
    have := ht _ (key N)
    rw [map_div₀, ← hs, hN] at this
    exact ⟨this, h⟩
  · rw [inv_div] at h
    have key : ∀ k : ℕ, u / (t ^ k) u ∈ A := by
      intro k
      induction k with
      | zero => simp [hu, A.one_mem]
      | succ k ih =>
        have := A.mul_mem _ _ h (ht _ ih)
        rwa [map_div₀, div_mul_div_cancel₀ htu, ← hs] at this
    have := ht _ (key N)
    rw [map_div₀, ← hs, hN] at this
    exact ⟨h, this⟩

private theorem cg_coord {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) (m : ℕ) (w : c.O) :
    Cg m (w : PadicAlgCl l) (∑ i, β.val i * ((PadicInt.toZModPow m (β.e.repr w i)).val : Qbar l)) := by
  have h1 := ((pBasEx l c).2 β).1
  have hw : (w : PadicAlgCl l) = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr w i) := by
    conv_lhs => rw [← β.e.sum_repr w]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]; rfl
  unfold Cg
  rw [hw, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  have h2 : β.e.repr w i - ((PadicInt.toZModPow m (β.e.repr w i)).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ m} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 h2
  have h3 := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) he
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast] at h3
  rw [← mul_sub, ← h3, norm_mul, norm_mul]
  have h4 : ‖algebraMap ℤ_[l] (PadicAlgCl l) e‖ ≤ 1 := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact e.2
  calc _ ≤ 1 * (1 * ‖((l : ℕ) : Qbar l) ^ m‖) := by gcongr; exact h1 i
    _ = _ := by ring

private theorem exists_tau (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (b : ℕ) (hb : ¬ l ∣ b) (m : ℕ) :
    ∃ τ ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m τ = un b hb m := by
  have hu : IsUnit (b : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hb)
  obtain ⟨τ, hτ, he⟩ := (pFrobEx l hl Ω A hA).2.2 hu.unit
  refine ⟨τ, hτ, Units.ext ?_⟩
  have : ((cycMod ℚ Ω l m τ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = PadicInt.toZModPow m ((cycZ ℚ Ω l τ : ℤ_[l]ˣ) : ℤ_[l]) := rfl
  rw [this, he]
  simp [un]

theorem UpperTheory.Kd.C7.pKumEx :
    UpperTheory.Kd.C7.SKumEx := by
  classical
  intro l _ hl Ω _ _ _ A hA c β ζ hζ Z hZ hC b hb
  refine ⟨0, 0, fun m _ => ?_⟩
  rw [Nat.sub_zero]
  haveI : NeZero (l : Ω) := by
    haveI : CharZero Ω := algebraRat.charZero Ω
    exact ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨τ, hτ, hτb⟩ := exists_tau l hl Ω A hA b hb m
  obtain ⟨U, hU, hUZ⟩ := hC m m
  let w : G ℚ Ω → c.O := fun s => if h : s ∈ Ine (F := ℚ) A then ⟨Z m s 1, hZ.int m s h 1⟩ else 0
  have hw : ∀ s ∈ Ine (F := ℚ) A, (w s : PadicAlgCl l) = Z m s 1 := fun s hs => by simp only [w, dif_pos hs]
  let χ : Fin β.d → G ℚ Ω → ZMod (l ^ m) := fun i s => PadicInt.toZModPow m (β.e.repr (w s) i)
  have hex : ∀ i, ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ Hm l A m, s u = u) ∧
      ∀ s ∈ Hm l A m, KumVal (l := l) m (ζ m) u s (χ i s) := by
    intro i
    refine GlobalTheory.T.exists_kummer_element_fixed_field_closed_subgroup l Ω m (Hm l A m) (GlobalTheory.T.isClosed_inertia_cyclotomic_kernel l Ω A m) (ζ m) (hζ m).1
      (fun s hs => fix_of_cycMod le_rfl hs.2 (hζ m).1.pow_eq_one) (χ i) (fun s hs t ht => ?_) U hU (fun s hs hsU => ?_)
    · have e : w (s * t) = w s + w t := by
        apply Subtype.ext
        have h1 : cycMod ℚ Ω l m s = 1 := hs.2
        rw [Subalgebra.coe_add, hw _ (mul_mem hs.1 ht.1), hw _ hs.1, hw _ ht.1, hZ.coc m s hs.1 t ht.1, h1, inv_one, mul_one]
      simp only [χ, e, map_add, Finsupp.add_apply]
    · obtain ⟨y, hy⟩ := ((pBasEx l c).2 β).2.2.1 m (w s) (by rw [hw s hs.1]; exact hUZ s hsU hs.1 1)
      have e : w s = ((l : ℤ_[l]) ^ m) • y := by rw [hy, Algebra.smul_def, map_pow, map_natCast]
      simp only [χ, e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
      rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  choose u hu0 hufix huk using hex
  have hconj := fun s hs => pConj l hl Ω A hA c Z hZ m s hs τ⁻¹ (inv_mem hτ)
  simp only [inv_inv] at hconj
  have hun := fun i => div_mem_of A τ (fun x hx => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hτ) x).2 hx) (u i) (hu0 i)
  have hP : ∀ i, ∃ P : Polynomial (R0 A), pv P (ζ m) = u i / τ (u i) := by
    intro i
    refine pPolyEx l hl Ω A hA ζ hζ m _ (hun i).1 fun s hs => ?_
    have h1 := congrArg τ (hufix i _ (hconj s hs).1)
    rw [← AlgEquiv.mul_apply, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, AlgEquiv.mul_apply] at h1
    rw [map_div₀, h1, hufix i s hs]
  choose P hP using hP
  refine ⟨P, (hζ m).1, le_rfl, fun i => ?_, ((pBasEx l c).2 β).1, fun s hs hc _ => ?_⟩
  · simp only [hP, inv_div]
    exact ⟨(hun i).1, div_ne_zero (hu0 i) ((map_ne_zero _).2 (hu0 i)), (hun i).2⟩
  · have hH : s ∈ Hm l A m := ⟨hs, hc⟩
    obtain ⟨hs', hZ'⟩ := hconj s hH
    refine ⟨fun i => PadicInt.toZModPow m (β.e.repr (w s - (b : ℤ_[l]) • w (τ⁻¹ * s * τ)) i), fun i => ?_, ?_⟩
    · have k1 := (pKumAlg l hl Ω A hA ζ hζ m m le_rfl _ hs').2.2 (τ (u i)) (χ i (τ⁻¹ * s * τ)) τ (by
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]; exact huk i _ hs')
      rw [show τ * (τ⁻¹ * s * τ) * τ⁻¹ = s by group, hτb] at k1
      have a1 := (pKumAlg l hl Ω A hA ζ hζ m m le_rfl _ hH).1
      have k2 := (a1 _ _ _ _ (huk i s hH) (a1 _ _ _ _ k1 k1).2.1).1
      simp only [hP, div_eq_mul_inv]
      convert k2 using 1
      simp [χ, un, sub_eq_add_neg]
    · have := cg_coord β m (w s - (b : ℤ_[l]) • w (τ⁻¹ * s * τ))
      convert this using 1
      rw [Subalgebra.coe_sub, Subalgebra.coe_smul, hw s hs, hw _ hs'.1, hZ', map_inv, inv_inv, hτb, Algebra.smul_def,
        map_natCast]
      rfl
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem iwOps_red_un {l : ℕ} [Fact l.Prime] (b : ℕ) (hb : ¬ l ∣ b) (r : ℕ) :
    red l r (un b hb (r + 1)) = un b hb r := by
  ext
  simp only [un, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, map_natCast]

private theorem iwOps_tr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {A : ValuationSubring Ω} {Z : Sy Ω l} (h : IwI c A Z) (b : ℕ) (hb : ¬ l ∣ b) : IwI c A (tr b hb Z) := by
  refine ⟨fun r s hs x => h.int r s hs _, fun r s hs t ht x => ?_, fun r s hs x => ?_⟩
  · simp only [UpperTheory.Kd.C7.tr]
    rw [h.coc r s hs t ht, mul_right_comm]
  · simp only [UpperTheory.Kd.C7.tr]
    rw [h.nrm r s hs]
    symm
    refine Finset.sum_equiv (Equiv.mulRight (un b hb (r + 1))) (fun y => ?_) (fun y _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight]
    rw [map_mul, iwOps_red_un, mul_left_inj]

theorem UpperTheory.Kd.C7.pIwOps :
    UpperTheory.Kd.C7.SIwOps := by
  intro l _ _ Ω _ _ _ A _ c Z h b hb
  have h' := iwOps_tr h b hb
  refine ⟨h', fun r s hs x => ?_, fun r s hs t ht x => ?_, fun r s hs x => ?_⟩
  · exact c.O.sub_mem (h.int r s hs x) (c.O.mul_mem (natCast_mem c.O b) (h'.int r s hs x))
  · simp only [sharp]
    rw [h.coc r s hs t ht, h'.coc r s hs t ht]
    ring
  · simp only [sharp]
    rw [h.nrm r s hs, h'.nrm r s hs, Finset.sum_sub_distrib, Finset.mul_sum]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem nat_le_one' {l : ℕ} [Fact l.Prime] (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a

private theorem dd_mul_eq_dd_mul_add_mul_dd {R : Type} [CommRing R] (f g : PowerSeries R) :
    dd (f * g) = dd f * g + f * dd g := by
  simp [dd]; ring

private theorem dl_mul_eq_add_of_isUnit {R : Type} [CommRing R] {f g : PowerSeries R}
    (hf : IsUnit f) (hg : IsUnit g) : dl (f * g) = dl f + dl g := by
  obtain ⟨u, rfl⟩ := hf
  obtain ⟨v, rfl⟩ := hg
  simp only [dl, ← Units.val_mul, Ring.inverse_unit]
  simp only [Units.val_mul, mul_inv_rev, dd_mul_eq_dd_mul_add_mul_dd]
  have h1 : (u : PowerSeries R) * ↑u⁻¹ = 1 := u.mul_inv
  have h2 : (v : PowerSeries R) * ↑v⁻¹ = 1 := v.mul_inv
  linear_combination (dd (u : PowerSeries R) * ↑u⁻¹) * h2 + (dd (v : PowerSeries R) * ↑v⁻¹) * h1

theorem UpperTheory.Kd.C7.pRepAdd :
    UpperTheory.Kd.C7.SRepAdd := by
  intro l _ hl Ω _ _ _ A hA j Φ c β ζ hζ
  have hB := (pBasEx l c).2 β
  have hpv : ∀ (P Q : Polynomial (R0 A)) (z : Ω), pv (P * Q) z = pv P z * pv Q z := by
    intro P Q z; simp [pv, Polynomial.eval₂_mul]
  refine ⟨?_, ?_⟩
  · rintro Z Z' D D' ⟨c₁, m₁, h₁⟩ ⟨c₂, m₂, h₂⟩
    refine ⟨max c₁ c₂, max (max m₁ m₂) 1, fun m hm => ?_⟩
    have hm₁ : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
    have hm₂ : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
    have hm0 : 1 ≤ m := le_trans (le_max_right _ _) hm
    have hc₁ : m - max c₁ c₂ ≤ m - c₁ := Nat.sub_le_sub_left (le_max_left _ _) m
    have hc₂ : m - max c₁ c₂ ≤ m - c₂ := Nat.sub_le_sub_left (le_max_right _ _) m
    obtain ⟨P, hP, hPL⟩ := h₁ m hm₁
    obtain ⟨P', hP', hPL'⟩ := h₂ m hm₂
    have hQ := pPresMono l hl Ω A hA c β ζ hζ Z Z m (m - c₁) (m - max c₁ c₂) P hc₁
      (fun s _ => by simp [Cg]) hP
    have hQ' := pPresMono l hl Ω A hA c β ζ hζ Z' Z' m (m - c₂) (m - max c₁ c₂) P' hc₂
      (fun s _ => by simp [Cg]) hP'
    unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres at hQ hQ'
    obtain ⟨hprim, hnr, hu, ho, hk⟩ := hQ
    obtain ⟨-, -, hu', -, hk'⟩ := hQ'
    refine ⟨fun i => P i * P' i, ?_, fun i => ?_⟩
    · unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres
      refine ⟨hprim, hnr, fun i => ?_, ho, fun s hs hcyc hsζ => ?_⟩
      · dsimp only
        rw [hpv]
        obtain ⟨a₁, a₂, a₃⟩ := hu i
        obtain ⟨b₁, b₂, b₃⟩ := hu' i
        dsimp only at a₁ a₂ a₃ b₁ b₂ b₃
        exact ⟨mul_mem a₁ b₁, mul_ne_zero a₂ b₂, by rw [mul_inv]; exact mul_mem a₃ b₃⟩
      · obtain ⟨k, hkv, hkc⟩ := hk s hs hcyc hsζ
        obtain ⟨k', hkv', hkc'⟩ := hk' s hs hcyc hsζ
        have hsH : s ∈ Hm l A m := Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩
        have halg := (pKumAlg l hl Ω A hA ζ hζ m (m - max c₁ c₂) (Nat.sub_le _ _) s hsH).1
        refine ⟨k + k', fun i => ?_, ?_⟩
        · dsimp only
          rw [hpv]
          exact (halg _ _ _ _ (hkv i) (hkv' i)).1
        · have hNz : NeZero (l ^ (m - max c₁ c₂)) :=
            ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
          have key : ∀ i, (((k + k') i).val : Qbar l) = (k i).val + (k' i).val
              - (l : Qbar l) ^ (m - max c₁ c₂)
                * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) : Qbar l) := by
            intro i
            rw [Pi.add_apply, ZMod.val_add, eq_sub_iff_add_eq]
            exact_mod_cast Nat.mod_add_div ((k i).val + (k' i).val) (l ^ (m - max c₁ c₂))
          unfold Cg at hkc hkc' ⊢
          dsimp only
          have hsplit : Z m s 1 + Z' m s 1 - ∑ i, β.val i * (((k + k') i).val : Qbar l)
              = (Z m s 1 - ∑ i, β.val i * ((k i).val : Qbar l))
                + (Z' m s 1 - ∑ i, β.val i * ((k' i).val : Qbar l))
                + ∑ i, β.val i * ((l : Qbar l) ^ (m - max c₁ c₂)
                  * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) : Qbar l)) := by
            simp only [key, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
            ring
          rw [hsplit]
          have hN : 0 ≤ ‖(l : Qbar l) ^ (m - max c₁ c₂)‖ := norm_nonneg _
          refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
            (max_le (le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hkc hkc')) ?_)
          refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hN (fun i _ => ?_)
          rw [norm_mul, norm_mul]
          have h1 := ho i
          have h2 := nat_le_one' (l := l) (((k i).val + (k' i).val) / l ^ (m - max c₁ c₂))
          calc _ ≤ 1 * (‖(l : Qbar l) ^ (m - max c₁ c₂)‖ * 1) :=
                mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hN) (by positivity) zero_le_one
            _ = _ := by ring
    · have hU : IsUnit (Φ.ser (P i)) := (pWD l hl Ω A hA j Φ ζ hζ m hm0 (P i)).2 (hu i)
      have hU' : IsUnit (Φ.ser (P' i)) := (pWD l hl Ω A hA j Φ ζ hζ m hm0 (P' i)).2 (hu' i)
      have hs : Φ.ser (P i * P' i) = Φ.ser (P i) * Φ.ser (P' i) := by
        simp [Fr.ser, Polynomial.map_mul, Polynomial.eval₂_mul]
      have ht : Φ.tw m ((D + D') i) = Φ.tw m (D i) + Φ.tw m (D' i) := by
        simp [Fr.tw, map_add]
      have e₁ := hPL i
      have e₂ := hPL' i
      unfold LC at e₁ e₂ ⊢
      dsimp only
      rw [ht, hs, dl_mul_eq_add_of_isUnit hU hU', map_add, map_add]
      have f₁ := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₁) e₁
      have f₂ := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₂) e₂
      convert Ideal.add_mem _ f₁ f₂ using 1
      ring
  · intro Z hZ
    refine ⟨0, 0, fun m _ => ⟨fun _ => 1, ?_, fun i => ?_⟩⟩
    · unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres
      refine ⟨by simpa using (hζ m).1, by simp, fun i => by simp [pv], fun i => hB.1 i,
        fun s hs hcyc hsζ => ⟨0, fun i => ?_, ?_⟩⟩
      · unfold KumVal
        exact ⟨1, by simp [pv], by simp⟩
      · unfold Cg
        have hz := hZ m s (Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩)
        simp [hz]
    · unfold LC
      simp [Fr.tw, Fr.ser, dl, dd]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7

section
variable {R : Type} [CommRing R]

private theorem sb_one_add (b : ℕ) : sb (R := R) b (1 + PowerSeries.X) = (1 + PowerSeries.X) ^ b := by
  rw [map_add, map_one, sb, PowerSeries.substAlgHom_X]; ring

private theorem sb_C (b : ℕ) (a : R) : sb b (PowerSeries.C a : PowerSeries R) = PowerSeries.C a :=
  (sb (R := R) b).commutes a

private theorem sb_eval₂ (b : ℕ) (P : Polynomial R) :
    sb b (P.eval₂ PowerSeries.C (1 + PowerSeries.X)) =
      (Polynomial.expand R b P).eval₂ PowerSeries.C (1 + PowerSeries.X) := by
  induction P using Polynomial.induction_on' with
  | add f g hf hg => simp only [Polynomial.eval₂_add, map_add, hf, hg]
  | monomial n a =>
    rw [Polynomial.expand_monomial, Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, map_mul, map_pow,
      sb_one_add, sb_C, ← pow_mul, mul_comm b n]

private theorem map_sb' {S : Type} [CommRing S] (τ : R →+* S) (b : ℕ) (h : PowerSeries R) :
    PowerSeries.map τ (sb b h) = sb b (PowerSeries.map τ h) := by
  unfold sb
  rw [PowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom]
  refine Eq.trans (PowerSeries.map_subst (hasSubst_pow (R := R) b) (h := τ) h) ?_
  congr 1
  change PowerSeries.map τ _ = _
  simp

private theorem dd_sb (b : ℕ) (hb : b ≠ 0) (f : PowerSeries R) :
    dd (sb b f) = (b : PowerSeries R) * sb b (dd f) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
  unfold dd
  rw [map_mul, sb_one_add]
  unfold sb
  rw [PowerSeries.coe_substAlgHom, PowerSeries.derivative_subst (hasSubst_pow (R := R) _)]
  simp only [map_sub, Derivation.leibniz_pow, map_add, Derivation.map_one_eq_zero, PowerSeries.derivative_X,
    smul_eq_mul, nsmul_eq_mul, Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

private theorem dl_sb (b : ℕ) (hb : b ≠ 0) (f : PowerSeries R) (hf : IsUnit f) :
    dl (sb b f) = (b : PowerSeries R) * sb b (dl f) := by
  obtain ⟨u, rfl⟩ := hf
  unfold dl
  have h1 : Ring.inverse (sb b (u : PowerSeries R)) = sb b ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) := by
    have := Ring.inverse_unit (Units.map (sb (R := R) b : PowerSeries R →* PowerSeries R) u)
    simpa using this
  rw [dd_sb b hb, h1, Ring.inverse_unit, map_mul, mul_assoc]

private theorem isUnit_nat {l : ℕ} [Fact l.Prime] (b : ℕ) (hb : ¬ l ∣ b) : IsUnit (b : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hb ?_)
  have : ‖((b : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
  exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd (b : ℤ)).1 this

private theorem lc_sb {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] R] (b : ℕ) (hb : ¬ l ∣ b) (m n : ℕ) (f g : PowerSeries R)
    (h : LC l m n f g) : LC l m n ((b : PowerSeries R) * sb b f) ((b : PowerSeries R) * sb b g) := by
  obtain ⟨u, hu⟩ := isUnit_nat b hb
  unfold LC at h ⊢
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  have h2 := congrArg (levAct (R := R) l m u) hy
  rw [map_sub, levAct_ev, levAct_ev, hu, sbp_nat, map_mul, map_pow, map_natCast] at h2
  rw [map_mul, map_mul, ← mul_sub, ← h2]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

end

end UpperTheory.Kd.C7

theorem UpperTheory.Kd.C7.pRepTr :
    UpperTheory.Kd.C7.SRepTr := by
  intro l _ hl Ω _ _ _ A hA j Φ c β ζ hζ Z hZ b hb D hD
  have hb0 : b ≠ 0 := by rintro rfl; exact hb (dvd_zero l)
  have h1 : Rep Φ β ζ (fun r s x => (b : Qbar l) * tr b hb Z r s x)
      (fun i => (b : PowerSeries Φ.R) * sb b (D i)) := by
    obtain ⟨c₁, m₁, H⟩ := hD
    refine ⟨c₁, max m₁ 1, fun m hm => ?_⟩
    obtain ⟨P, hP, hL⟩ := H m (le_of_max_le_left hm)
    refine ⟨_, pPresTr l hl Ω A hA c β ζ hζ Z hZ b hb m _ P hP, fun i => ?_⟩
    have hu : IsUnit (Φ.ser (P i)) :=
      (pWD l hl Ω A hA j Φ ζ hζ m (le_of_max_le_right hm) (P i)).2 (hP.2.2.1 i)
    have e1 : Φ.ser (Polynomial.expand (R0 A) b (P i)) = sb b (Φ.ser (P i)) := by
      unfold Fr.ser
      rw [sb_eval₂, Polynomial.map_expand]
    have e2 : Φ.tw m ((b : PowerSeries Φ.R) * sb b (D i)) = (b : PowerSeries Φ.R) * sb b (Φ.tw m (D i)) := by
      unfold Fr.tw
      rw [map_mul, map_natCast, map_sb']
    rw [e1, e2, dl_sb b hb0 _ hu]
    exact lc_sb b hb _ _ _ _ (hL i)
  obtain ⟨u, hu⟩ := isUnit_nat (l := l) b hb
  have hw : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (b : ℤ_[l]) = 1 := by rw [← hu, Units.inv_mul]
  generalize ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = w at hw
  have h2 := pRepSmul l hl Ω A hA j Φ c β ζ hζ _ _ (algebraMap ℤ_[l] c.O w) h1
  convert h2 using 1
  · funext r s x
    have : ((algebraMap ℤ_[l] c.O w : c.O) : PadicAlgCl l) * (b : Qbar l) = 1 := by
      have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) hw
      rw [map_mul, map_natCast, map_one] at this
      exact this
    rw [← mul_assoc, this, one_mul]
  · funext i
    have hm : β.mat (algebraMap ℤ_[l] c.O w) = Matrix.diagonal fun _ => w := by
      unfold Bas.mat
      rw [AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
      rfl
    have h3 : PowerSeries.C (algebraMap ℤ_[l] Φ.R w) * (b : PowerSeries Φ.R) = 1 := by
      have := congrArg (fun z => PowerSeries.C (algebraMap ℤ_[l] Φ.R z)) hw
      simpa using this
    unfold Fr.act
    rw [hm, Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq, ← mul_assoc, h3, one_mul]
    · intro k _ hk
      rw [Matrix.diagonal_apply_ne _ hk.symm]; simp
    · intro h; exact absurd (Finset.mem_univ i) h
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem apply_inv_conj (t s : G ℚ Ω) (x : Ω) :
    s ((t⁻¹ : G ℚ Ω) x) = (t⁻¹ : G ℚ Ω) ((t * s * t⁻¹) x) := by
  simp [AlgEquiv.mul_apply]

private def decompositionInvRingHom (A : ValuationSubring Ω) (t : G ℚ Ω) (ht : t ∈ Dec (F := ℚ) A) : R0 A →+* R0 A where
  toFun y := ⟨(t⁻¹ : G ℚ Ω) (y : Ω), (apply_mem_iff_of_mem_Dec (inv_mem ht) _).2 y.2.1, fun s hs => by
    rw [apply_inv_conj t s, y.2.2 _ (conj_mem_Ine ht hs)]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

private theorem residueInverse_coe (A : ValuationSubring Ω) (t : G ℚ Ω) (ht : t ∈ Dec (F := ℚ) A) (y : R0 A) :
    ((decompositionInvRingHom A t ht y : R0 A) : Ω) = (t⁻¹ : G ℚ Ω) (y : Ω) := rfl

end SlopeTestRemainingChoices

section Frame

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}
  {j : Ω →+* Qbar l} (Φ : Fr l A j)

end Frame

private theorem apply_root_eq_of_cycBar_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (s : G ℚ Ω)
    (hs : cycBar ℚ Ω l s = 1) (ζ : ℕ → Ω) (hζ : Roots l ζ) (m : ℕ) : s (ζ m) = ζ m := by
  have hZ : cycZ ℚ Ω l s = 1 := by
    have h := congrArg Units.val hs
    simp [cycBar] at h
    ext1
    rw [Units.val_one]
    apply Subtype.ext
    exact h
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => ⟨⟨ζ i, (hζ i).1⟩, rootsOfUnity.isCyclic _ _⟩
  have h1 := cyclotomicCharacter.spec l (n := m) (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) (ζ m)
    ((hζ m).1.pow_eq_one)
  have hc : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) = 1 := hZ
  rw [hc] at h1
  simp only [Units.val_one, map_one] at h1
  rcases m with _ | m
  · have h0 : ζ 0 = 1 := by simpa using (hζ 0).1
    rw [h0, map_one]
  · have hlt : 1 < l ^ (m + 1) := Nat.one_lt_pow (Nat.succ_ne_zero m) (Fact.out : l.Prime).one_lt
    haveI : Fact (1 < l ^ (m + 1)) := ⟨hlt⟩
    exact h1.trans (by rw [ZMod.val_one, pow_one])

private theorem lc_map' {R : Type} [CommRing R] (e : R →+* R) (l m n : ℕ) (f g : PowerSeries R)
    (h : LC l m n f g) : LC l m n (PowerSeries.map e f) (PowerSeries.map e g) := by
  have hcyc : PowerSeries.map e (GlobalTheory.Col.cyc R l m) = GlobalTheory.Col.cyc R l m := by
    unfold GlobalTheory.Col.cyc
    rw [Polynomial.hom_eval₂]
    have : (PowerSeries.map e).comp PowerSeries.C = PowerSeries.C.comp e := by
      ext x : 1
      simp
    rw [this, ← Polynomial.eval₂_map, Polynomial.map_cyclotomic]
    simp
  unfold LC at *
  rw [← map_sub] at h ⊢
  rw [← map_sub]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hb : b * (l : PowerSeries R) ^ n - (f - g) ∈ Ideal.span {GlobalTheory.Col.cyc R l m} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_pow, map_natCast]
    exact sub_eq_zero.2 ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
  have hfg : f - g = b * (l : PowerSeries R) ^ n - c * GlobalTheory.Col.cyc R l m := by
    rw [hc]
    ring
  have hz : ev R l m (GlobalTheory.Col.cyc R l m) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [hfg]
  refine Ideal.mem_span_singleton'.2 ⟨ev R l m (PowerSeries.map e b), ?_⟩
  simp only [map_sub, map_mul, map_pow, map_natCast, hcyc, hz, mul_zero, sub_zero]

private theorem dl_map_ringEquiv {R : Type} [CommRing R] (e : R ≃+* R) (f : PowerSeries R) :
    dl (PowerSeries.map (e : R →+* R) f) = PowerSeries.map (e : R →+* R) (dl f) := by
  have hinv : ∀ g : PowerSeries R,
      PowerSeries.map (e.symm : R →+* R) (PowerSeries.map (e : R →+* R) g) = g := by
    intro g
    ext n
    simp
  have hd : dd (PowerSeries.map (e : R →+* R) f) = PowerSeries.map (e : R →+* R) (dd f) := by
    unfold dd
    rw [map_mul]
    congr 1
    · simp
    · ext n
      simp [PowerSeries.coeff_derivative]
  have hr : Ring.inverse (PowerSeries.map (e : R →+* R) f) =
      PowerSeries.map (e : R →+* R) (Ring.inverse f) := by
    by_cases hu : IsUnit f
    · have hu' : IsUnit (PowerSeries.map (e : R →+* R) f) := hu.map _
      apply hu'.mul_left_cancel
      rw [Ring.mul_inverse_cancel _ hu', ← map_mul, Ring.mul_inverse_cancel _ hu, map_one]
    · have hu' : ¬ IsUnit (PowerSeries.map (e : R →+* R) f) := by
        intro h
        apply hu
        simpa [hinv] using h.map (PowerSeries.map (e.symm : R →+* R))
      rw [Ring.inverse_non_unit _ hu, Ring.inverse_non_unit _ hu', map_zero]
  unfold dl
  rw [hd, hr, map_mul]

private theorem fr_ser_map_decompositionInv_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (Φ : Fr l A j) (P : Polynomial (R0 A)) :
    Φ.ser (P.map (decompositionInvRingHom A Φ.fr Φ.fr_dec)) = PowerSeries.map (Φ.σ.symm : Φ.R →+* Φ.R) (Φ.ser P) := by
  have hi : Φ.i0.comp (decompositionInvRingHom A Φ.fr Φ.fr_dec) = (Φ.σ.symm : Φ.R →+* Φ.R).comp Φ.i0 := by
    ext y
    have h := Φ.frobenius_compat_inclusion (decompositionInvRingHom A Φ.fr Φ.fr_dec y) y (by
      rw [residueInverse_coe]
      simp)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
    rw [← h, RingEquiv.symm_apply_apply]
  unfold Fr.ser
  rw [Polynomial.map_map, hi, ← Polynomial.map_map, Polynomial.hom_eval₂]
  have : (PowerSeries.map (Φ.σ.symm : Φ.R →+* Φ.R)).comp PowerSeries.C =
      PowerSeries.C.comp (Φ.σ.symm : Φ.R →+* Φ.R) := by
    ext x : 1
    simp
  rw [this, ← Polynomial.eval₂_map]
  simp

private theorem dec_frob_of_mem_dec_rat {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (t : G ℚ Ω)
    (ht : t ∈ Dec (F := ℚ) A) (P : Polynomial (R0 A)) (z : Ω) (hz : t z = z) :
    pv (P.map (decompositionInvRingHom A t ht)) z = (t⁻¹ : G ℚ Ω) (pv P z) := by
  have hz' : (t⁻¹ : G ℚ Ω) z = z := by
    conv_lhs => rw [← hz]
    simp [AlgEquiv.aut_inv]
  have hc : (R0 A).subtype.comp (decompositionInvRingHom A t ht) = ((t⁻¹ : G ℚ Ω) : Ω →+* Ω).comp (R0 A).subtype := by
    ext y
    exact residueInverse_coe A t ht y
  unfold pv
  rw [Polynomial.eval₂_map, hc]
  conv_lhs => rw [← hz']
  exact (Polynomial.hom_eval₂ P (R0 A).subtype ((t⁻¹ : G ℚ Ω) : Ω →+* Ω) z).symm

private theorem dec_frob_of_mem_dec_rat_prime {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
    (A : ValuationSubring Ω) (t : G ℚ Ω) (ht : t ∈ Dec (F := ℚ) A) (n r : ℕ) (z : Ω) (hz : t z = z)
    (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) {ι : Type} [Fintype ι] (u : ι → Ω) (o : ι → Qbar l)
    (h : KumPres A n r z Z u o) :
    KumPres A n r z (fun s x => Z (t * s * t⁻¹) x) (fun i => (t⁻¹ : G ℚ Ω) (u i)) o := by
  have hz' : (t⁻¹ : G ℚ Ω) z = z := by
    conv_lhs => rw [← hz]
    simp [AlgEquiv.aut_inv]
  obtain ⟨hprim, hnr, hu, ho, hK⟩ := h
  refine ⟨hprim, hnr, fun i => ?_, ho, fun s hs hcyc hsz => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hu i
    refine ⟨(apply_mem_iff_of_mem_Dec (inv_mem ht) _).2 h1, (map_ne_zero _).2 h2, ?_⟩
    rw [← map_inv₀]
    exact (apply_mem_iff_of_mem_Dec (inv_mem ht) _).2 h3
  · have hs' := conj_mem_Ine ht hs
    have hc' : cycMod ℚ Ω l r (t * s * t⁻¹) = 1 := by
      rw [map_mul, map_mul, hcyc, mul_one, ← map_mul, mul_inv_cancel, map_one]
    have hz2 : (t * s * t⁻¹) z = z := by
      simp only [AlgEquiv.mul_apply, hz', hsz, hz]
    obtain ⟨k, hk, hcg⟩ := hK _ hs' hc' hz2
    refine ⟨k, fun i => ?_, hcg⟩
    obtain ⟨v, hv1, hv2⟩ := hk i
    refine ⟨(t⁻¹ : G ℚ Ω) v, by rw [← map_pow, hv1], ?_⟩
    rw [apply_inv_conj t s v, hv2, map_mul, map_pow, hz']

theorem pRepFrob :
    SRepFrob := by
  intro l _ hl2 Ω _ _ _ A hA j Φ c β ζ hζ Z D a hR hZ i
  have hfix : ∀ m, Φ.fr (ζ m) = ζ m := apply_root_eq_of_cycBar_eq_one Φ.fr Φ.fr_cyc ζ hζ
  let Z' : Sy Ω l := fun r s x => Z r (Φ.fr * s * Φ.fr⁻¹) x
  have hR' : Rep Φ β ζ Z' (fun i => Φ.tw 1 (D i)) := by
    obtain ⟨c₁, m₁, hm⟩ := hR
    refine ⟨c₁, m₁, fun m hm1 => ?_⟩
    obtain ⟨P, hP, hL⟩ := hm m hm1
    refine ⟨fun i => (P i).map (decompositionInvRingHom A Φ.fr Φ.fr_dec), ?_, fun i => ?_⟩
    · unfold BPres at *
      have h6 := dec_frob_of_mem_dec_rat_prime A Φ.fr Φ.fr_dec (m - c₁) m (ζ (m - c₁)) (hfix _) (Z m) _ _ hP
      convert h6 using 2
      exact dec_frob_of_mem_dec_rat A Φ.fr Φ.fr_dec (P _) (ζ m) (hfix m)
    · rw [fr_ser_map_decompositionInv_eq, dl_map_ringEquiv]
      have h2 := lc_map' (Φ.σ.symm : Φ.R →+* Φ.R) l m (m - c₁) _ _ (hL i)
      have htw : Φ.tw m (Φ.tw 1 (D i)) =
          PowerSeries.map (Φ.σ.symm : Φ.R →+* Φ.R) (Φ.tw m (D i)) := by
        unfold Fr.tw
        ext n
        simp only [PowerSeries.coeff_map, pow_one]
        rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← RingHom.mul_def, ← RingHom.mul_def,
          ← pow_succ, ← pow_succ']
      rw [htw]
      exact h2
  have hS := pRepSmul l hl2 Ω A hA j Φ c β ζ hζ Z D a hR
  have hU := pRepUniq l hl2 Ω A hA j Φ c β ζ hζ Z' (fun r s x => (a : Qbar l) * Z r s x)
    (fun i => Φ.tw 1 (D i)) (Φ.act (β.mat a) D) hR' hS (fun m s hs => hZ m s hs)
  exact congrFun hU i

end UpperTheory.Kd.C7
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω}

private theorem norm_pow_anti (n' n : ℕ) (h : n' ≤ n) : ‖((l : ℕ) : Qbar l) ^ n‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one.le h

private theorem cg_mono {n' n : ℕ} (h : n' ≤ n) {x y : Qbar l} (hc : Cg n x y) : Cg n' x y :=
  le_trans hc (norm_pow_anti n' n h)

private theorem cg_trans {n : ℕ} {x y z : Qbar l} (h1 : Cg n x y) (h2 : Cg n y z) : Cg n x z := by
  have e : x - z = (x - y) + (y - z) := by ring
  unfold Cg at *
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

private theorem cg_sub {n : ℕ} {x y x' y' : Qbar l} (h1 : Cg n x y) (h2 : Cg n x' y') : Cg n (x - x') (y - y') := by
  have e : x - x' - (y - y') = (x - y) + -(x' - y') := by ring
  unfold Cg at *
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rwa [norm_neg]

private theorem cg_mul {n : ℕ} {x y w : Qbar l} (hw : ‖w‖ ≤ 1) (h1 : Cg n x y) : Cg n (w * x) (w * y) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖w‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := by gcongr
    _ ≤ _ := by rwa [one_mul]

private theorem cg_sum {n : ℕ} {ι : Type} (T : Finset ι) (x y : ι → Qbar l) (h : ∀ i ∈ T, Cg n (x i) (y i)) :
    Cg n (∑ i ∈ T, x i) (∑ i ∈ T, y i) := by
  unfold Cg at *
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) h

private theorem norm_nat_le (d : ℕ) : ‖(d : Qbar l)‖ ≤ 1 := by
  have h : (d : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (d : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  have h1 := PadicInt.norm_le_one (d : ℤ_[l])
  rw [PadicInt.norm_def] at h1
  exact_mod_cast h1

private theorem norm_padic_nat (d : ℕ) (hd : ¬ l ∣ d) : ‖(d : ℚ_[l])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hd)

private theorem norm_nat_eq (d : ℕ) (hd : ¬ l ∣ d) : ‖(d : Qbar l)‖ = 1 := by
  have h : (d : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (d : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact norm_padic_nat d hd

private theorem exists_unit (d : ℕ) (hd : ¬ l ∣ d) : ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = d := by
  have h : IsUnit (d : ℤ_[l]) := PadicInt.isUnit_iff.2 (by
    rw [PadicInt.norm_def]
    simpa using norm_padic_nat (l := l) d hd)
  exact ⟨h.unit, h.unit_spec⟩

private theorem exists_ine_un (hl : l ≠ 2) (hA : OverL l A) (d : ℕ) (hd : ¬ l ∣ d) (m : ℕ) :
    ∃ t ∈ Ine (F := ℚ) A, (cycMod ℚ Ω l m t)⁻¹ = un d hd m := by
  obtain ⟨u, hu⟩ := exists_unit (l := l) d hd
  obtain ⟨t, ht, e⟩ := (pFrobEx l hl Ω A hA).2.2 u⁻¹
  refine ⟨t, ht, Units.ext ?_⟩
  have h1 : (cycMod ℚ Ω l m t)⁻¹ = Units.map (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)).toMonoidHom u := by
    simp [cycMod, e]
  rw [h1]
  simp [un, hu]

private theorem mem_of_mul_mem (c : Coef l) {θ y : Qbar l} (h1 : ‖θ‖ = 1) (hy : y ∈ c.O) (h0 : y ≠ 0)
    (hθ : θ * y ∈ c.O) : θ ∈ c.O := by
  obtain ⟨β⟩ := (pBasEx l c).1
  have hinv := ((pBasEx l c).2 β).2.2.2
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at h1
  rcases ValuationRing.dvd_total (⟨y, hy⟩ : c.O) ⟨θ * y, hθ⟩ with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h2 : θ * y = y * k := congrArg Subtype.val hk
    have h3 : θ = k := by
      apply mul_right_cancel₀ h0
      rw [h2, mul_comm]
    rw [h3]; exact k.2
  · have h2 : y = θ * y * k := congrArg Subtype.val hk
    have h3 : θ⁻¹ = k := by
      apply mul_left_cancel₀ (mul_ne_zero hθ0 h0)
      rw [← h2, mul_assoc, mul_comm θ, mul_assoc, inv_mul_cancel₀ hθ0, mul_one]
    have h4 : θ⁻¹ ∈ c.O := by rw [h3]; exact k.2
    have := hinv θ⁻¹ h4 (by rw [norm_inv, h1, inv_one])
    rwa [inv_inv] at this

private theorem eig_at (hl : l ≠ 2) (hA : OverL l A) {c : Coef l} {Z : Sy Ω l} (hZ : IwI c A Z) {a : Qbar l} {fr : G ℚ Ω}
    (hfr : fr ∈ Dec (F := ℚ) A) (E : ∀ m, ∀ s ∈ Hm l A m, Z m (fr * s * fr⁻¹) 1 = a * Z m s 1) (m : ℕ) {s : G ℚ Ω}
    (hs : s ∈ Hm l A m) {t : G ℚ Ω} (ht : t ∈ Ine (F := ℚ) A) :
    Z m (fr * s * fr⁻¹) (cycMod ℚ Ω l m t)⁻¹ = a * Z m s (cycMod ℚ Ω l m t)⁻¹ := by
  have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
  have hsk : cycMod ℚ Ω l m s = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).2
  have hs' : fr * s * fr⁻¹ ∈ Hm l A m := by
    refine Subgroup.mem_inf.2 ⟨conj_mem_Ine hfr hsI, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, hsk, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have ht' : fr * t * fr⁻¹ ∈ Ine (F := ℚ) A := conj_mem_Ine hfr ht
  have h1 := (pConj l hl Ω A hA c Z hZ m _ hs' _ ht').2 1
  have hc : cycMod ℚ Ω l m (fr * t * fr⁻¹) = cycMod ℚ Ω l m t := by
    rw [map_mul, map_mul, map_inv, mul_comm (cycMod ℚ Ω l m fr), mul_assoc, mul_inv_cancel, mul_one]
  have hconj : (fr * t * fr⁻¹) * (fr * s * fr⁻¹) * (fr * t * fr⁻¹)⁻¹ = fr * (t * s * t⁻¹) * fr⁻¹ := by group
  have h2 := pConj l hl Ω A hA c Z hZ m s hs t ht
  have h3 := E m _ h2.1
  have h4 := h2.2 1
  rw [hconj, hc, one_mul] at h1
  rw [one_mul] at h4
  rw [← h1, h3, h4]

private theorem sharp_eig (hl : l ≠ 2) (hA : OverL l A) {c : Coef l} {Z : Sy Ω l} (hZ : IwI c A Z) {a : Qbar l} {fr : G ℚ Ω}
    (hfr : fr ∈ Dec (F := ℚ) A) (E : ∀ m, ∀ s ∈ Hm l A m, Z m (fr * s * fr⁻¹) 1 = a * Z m s 1) (d : ℕ) (hd : ¬ l ∣ d) (m : ℕ)
    {s : G ℚ Ω} (hs : s ∈ Hm l A m) : sharp d hd Z m (fr * s * fr⁻¹) 1 = a * sharp d hd Z m s 1 := by
  obtain ⟨t, ht, e⟩ := exists_ine_un (Ω := Ω) hl hA d hd m
  simp only [sharp, tr, one_mul]
  rw [E m s hs, ← e, eig_at hl hA hZ hfr E m hs ht]
  ring

private theorem pack (hl : l ≠ 2) (hA : OverL l A) {j : Ω →+* Qbar l} (Φ : Fr l A j) {c : Coef l} (β : Bas c) {ζ : ℕ → Ω}
    (hζ : Roots l ζ) {Y : Sy Ω l} (hY : IwI c A Y) {D : Fin β.d → PowerSeries Φ.R} (hD : Rep Φ β ζ Y D) {a : Qbar l}
    (ha : ‖a‖ = 1) (E : ∀ m, ∀ s ∈ Hm l A m, Y m (Φ.fr * s * Φ.fr⁻¹) 1 = a * Y m s 1) :
    ∃ (a₁ : c.O) (Gs : PowerSeries (Qbar l)) (v : ℂ_[l]), (∀ i, Φ.tw 1 (D i) = Φ.act (β.mat a₁) D i) ∧ ‖v‖ = 1 ∧
      (∀ n, Gs.coeff n ∈ c.O) ∧
      (∀ n, Φ.lam β (fun i => (D i).coeff n) = v * algebraMap (PadicAlgCl l) ℂ_[l] (Gs.coeff n)) ∧
      ((a₁ : PadicAlgCl l) = a ∨ Gs = 0) := by
  by_cases haO : a ∈ c.O
  · let a' : c.O := ⟨a, haO⟩
    have hinv := ((pBasEx l c).2 β).2.2.2 a haO ha
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    have hu : IsUnit a' := IsUnit.of_mul_eq_one ⟨a⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
    have hfr := pRepFrob l hl Ω A hA j Φ c β ζ hζ Y D a' hD E
    obtain ⟨v, hv, hper⟩ := pPeriod l hl Ω A hA j Φ c β a' hu
    have hx : ∀ n, ∃ o : c.O, Φ.lam β (fun i => (D i).coeff n) = v * algebraMap (PadicAlgCl l) ℂ_[l] (o : PadicAlgCl l) := by
      intro n
      refine hper _ fun i => ?_
      have := congrArg (PowerSeries.coeff n) (hfr i)
      simpa [Fr.tw, Fr.act, PowerSeries.coeff_C_mul] using this
    choose o ho using hx
    refine ⟨a', PowerSeries.mk fun n => (o n : PadicAlgCl l), v, hfr, hv, fun n => ?_, fun n => ?_, Or.inl rfl⟩
    · rw [PowerSeries.coeff_mk]; exact (o n).2
    · rw [PowerSeries.coeff_mk]; exact ho n
  · have hz : ∀ m, ∀ s ∈ Hm l A m, Y m s 1 = 0 := by
      intro m s hs
      by_contra h0
      have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
      refine haO (mem_of_mul_mem c ha (hY.int m s hsI 1) h0 ?_)
      rw [← E m s hs]
      exact hY.int m _ (conj_mem_Ine Φ.fr_dec hsI) 1
    have h0 := pRepUniq l hl Ω A hA j Φ c β ζ hζ Y Y D 0 hD
      ((pRepAdd l hl Ω A hA j Φ c β ζ hζ).2 Y hz) (fun _ _ _ => rfl)
    subst h0
    refine ⟨1, 0, 1, fun i => ?_, by simp, fun n => by simp [zero_mem], fun n => ?_, Or.inr rfl⟩
    · simp [Fr.tw, Fr.act]
    · simp [Fr.lam]

private theorem exists_approx (v : ℂ_[l]) (hv : ‖v‖ = 1) : ∃ vm : ℕ → Qbar l,
    (∀ m, ‖algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v‖ ≤ ‖(l : ℂ_[l]) ^ m‖) ∧ ∀ m, ‖vm m‖ = 1 ∧ Cg m (vm (m + 1)) (vm m) := by
  have hn : ∀ n, ‖(l : ℂ_[l]) ^ n‖ = ‖((l : ℕ) : Qbar l) ^ n‖ := by
    intro n
    rw [norm_pow, norm_pow, ← PadicComplex.coe_natCast]
    congr 1
    exact PadicComplex.norm_extends l _
  have hal : ∀ x : Qbar l, ‖algebraMap (PadicAlgCl l) ℂ_[l] x‖ = ‖x‖ := fun x => PadicComplex.norm_extends l x
  have hl1 : ‖((l : ℕ) : Qbar l)‖ < 1 := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one
  have hl0 : 0 < ‖((l : ℕ) : Qbar l)‖ := norm_pos_iff.2 GlobalTheory.LambdaValuationPowers.natCast_ne_zero
  have hex : ∀ m : ℕ, ∃ y : Qbar l, ‖algebraMap (PadicAlgCl l) ℂ_[l] y - v‖ ≤ ‖(l : ℂ_[l]) ^ (m + 1)‖ := by
    intro m
    have hr : 0 < ‖(l : ℂ_[l]) ^ (m + 1)‖ := by
      rw [hn, norm_pow]; exact pow_pos hl0 _
    obtain ⟨y, hy⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt v hr
    refine ⟨y, ?_⟩
    rw [dist_comm, dist_eq_norm] at hy
    exact hy.le
  choose vm hvm using hex
  have hlt : ∀ m, ‖algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v‖ < 1 := by
    intro m
    refine (hvm m).trans_lt ?_
    rw [hn, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hl1 (by omega)
  refine ⟨vm, fun m => (hvm m).trans ?_, fun m => ⟨?_, ?_⟩⟩
  · rw [hn, hn]; exact norm_pow_anti m (m + 1) (by omega)
  · rw [← hal]
    apply le_antisymm
    · have e : algebraMap (PadicAlgCl l) ℂ_[l] (vm m) = (algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v) + v := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hlt m).le hv.le)
    · have e : v = algebraMap (PadicAlgCl l) ℂ_[l] (vm m) + -(algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v) := by ring
      have h1 : ‖v‖ ≤ _ := (congrArg norm e).le.trans (IsUltrametricDist.norm_add_le_max _ _)
      rw [hv, norm_neg] at h1
      rcases le_max_iff.1 h1 with h | h
      · exact h
      · exact absurd h (not_le.2 (hlt m))
  · unfold Cg
    rw [← hal, map_sub]
    have e : algebraMap (PadicAlgCl l) ℂ_[l] (vm (m + 1)) - algebraMap (PadicAlgCl l) ℂ_[l] (vm m) =
        (algebraMap (PadicAlgCl l) ℂ_[l] (vm (m + 1)) - v) + -(algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine (hvm (m + 1)).trans ?_
      rw [hn]; exact norm_pow_anti m _ (by omega)
    · rw [norm_neg]
      refine (hvm m).trans ?_
      rw [hn]; exact norm_pow_anti m _ (by omega)

private theorem sum_step {m : ℕ} (ψ : DirichletCharacter (Qbar l) (l ^ m)) (d₀ : ℕ) (hd : ¬ l ∣ d₀) (n : ℕ)
    (h h' T : (ZMod (l ^ m))ˣ → Qbar l) (w : Qbar l) (h1 : ∀ b, Cg n (h b) (h' b))
    (h2 : ∀ b, Cg n (h' b - (d₀ : Qbar l) * h' (b * un d₀ hd m)) (w * T b)) :
    Cg n ((1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * ∑ b : (ZMod (l ^ m))ˣ, ψ b * h b)
      (w * ∑ b : (ZMod (l ^ m))ˣ, ψ b * T b) := by
  have hu : ((un d₀ hd m : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = (d₀ : ZMod (l ^ m)) := by simp [un]
  have hinv : ψ⁻¹ (d₀ : ZMod (l ^ m)) * ψ (d₀ : ZMod (l ^ m)) = 1 := by
    rw [← hu, MulChar.inv_apply, Ring.inverse_unit, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have hre : ∑ b : (ZMod (l ^ m))ˣ, ψ b * h (b * un d₀ hd m) =
      ψ⁻¹ (d₀ : ZMod (l ^ m)) * ∑ b : (ZMod (l ^ m))ˣ, ψ b * h b := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight (un d₀ hd m)) _ _ fun b => ?_
    simp only [Equiv.coe_mulRight, Units.val_mul, map_mul, hu]
    linear_combination (-(ψ b * h (b * un d₀ hd m))) * hinv
  have key : (1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * ∑ b : (ZMod (l ^ m))ˣ, ψ b * h b =
      ∑ b : (ZMod (l ^ m))ˣ, ψ b * (h b - (d₀ : Qbar l) * h (b * un d₀ hd m)) := by
    have e : ∀ b : (ZMod (l ^ m))ˣ, ψ b * (h b - (d₀ : Qbar l) * h (b * un d₀ hd m)) =
        ψ b * h b - (d₀ : Qbar l) * (ψ b * h (b * un d₀ hd m)) := fun b => by ring
    simp only [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hre]
    ring
  rw [key, Finset.mul_sum]
  have e2 : ∀ b : (ZMod (l ^ m))ˣ, w * (ψ b * T b) = ψ b * (w * T b) := fun b => by ring
  simp only [e2]
  refine cg_sum _ _ _ fun b _ => cg_mul (DirichletCharacter.unit_norm_eq_one ψ b).le ?_
  exact cg_trans (cg_sub (h1 b) (cg_mul (norm_nat_le d₀) (h1 _))) (h2 b)

theorem pCore : SCore := by
  intro l _ hl Ω _ _ _ A hA c Z a j d₀ e₀ m₀ ζ hZ ha E hj hd hζ hP
  obtain ⟨Φ⟩ := pFrEx3 l hl Ω A hA j hj
  obtain ⟨β⟩ := (pBasEx l c).1
  have hHP : HasPres β A ζ Z := by
    refine ⟨e₀, max m₀ 1, fun m hm => ?_⟩
    obtain ⟨ι, _, P, o, h1, h2, h3⟩ := hP m (le_of_max_le_left hm)
    obtain ⟨P', hP', -⟩ := pToBasis l hl Ω A hA c β ζ hζ j hj Z m (m - e₀) ι P o (le_of_max_le_right hm) h1 h2 h3
    exact ⟨P', hP'⟩
  have hCont := pContOf l hl Ω A hA c β ζ hζ Z hZ hHP
  have hops := pIwOps l hl Ω A hA c Z hZ d₀ hd
  have hHS := pKumEx l hl Ω A hA c β ζ hζ Z hZ hCont d₀ hd
  obtain ⟨D, hD⟩ := pRepEx l hl Ω A hA j Φ c β ζ hζ _ hops.2 hHS
  have E' : ∀ m, ∀ s ∈ Hm l A m, Z m (Φ.fr * s * Φ.fr⁻¹) 1 = a * Z m s 1 := E Φ.fr Φ.fr_dec Φ.fr_frob Φ.fr_cyc
  obtain ⟨a₁, Gs, v, htw, hv, hGs, hlam, hor⟩ := pack hl hA Φ β hζ hops.2 hD ha
    (fun m s hs => sharp_eig hl hA hZ Φ.fr_dec E' d₀ hd m hs)
  have hGn : ∀ n, ‖Gs.coeff n‖ ≤ 1 := fun n => GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hGs n)
  obtain ⟨vm, hvm, hvm2⟩ := exists_approx v hv
  obtain ⟨c₁, m₁, hcl⟩ := pClause1 l hl Ω A hA j Φ c β ζ hζ hj Z hZ d₀ hd D a₁ Gs v vm hD htw hGn hlam hvm e₀
  refine ⟨Gs, vm, max c₁ e₀, max m₁ 1, hGs, hvm2, ?_, ?_⟩
  · intro m hm ι _ P o h1 h2 h3 ψ
    obtain ⟨P', hP', hcg⟩ := pToBasis l hl Ω A hA c β ζ hζ j hj Z m (m - e₀) ι P o (le_of_max_le_right hm) h1 h2 h3
    have hc := hcl m (le_of_max_le_left hm) P' hP'
    have hT : ∀ (N : ℕ) (z : Qbar l), vm m * (a₁ : PadicAlgCl l) ^ m * tval Gs N z = vm m * a ^ m * tval Gs N z := by
      intro N z
      rcases hor with e | e
      · rw [e]
      · simp [e, tval]
    exact sum_step ψ d₀ hd (m - max c₁ e₀) (fun b => htv j (ζ m) P o (b : ZMod (l ^ m)).val)
      (fun b => htv j (ζ m) (fun i => (P' i).map (R0 A).subtype) β.val (b : ZMod (l ^ m)).val)
      (fun b => tval Gs (l ^ (3 * m)) (j (ζ m) ^ (b : ZMod (l ^ m)).val)) (vm m * a ^ m)
      (fun b => cg_mono (Nat.sub_le_sub_left (le_max_right _ _) m) (hcg b))
      (fun b => by
        have := hc b
        rw [hT] at this
        exact cg_mono (Nat.sub_le_sub_left (le_max_left _ _) m) this)
  · intro φ k hk hsp
    obtain ⟨g, hg, c₂, Z', hZ', hC', rel⟩ := pDiv l hl Ω A hA c Z hZ hCont φ k hk hsp
    have ops' := pIwOps l hl Ω A hA c Z' hZ' d₀ hd
    have hHS' := pKumEx l hl Ω A hA c β ζ hζ Z' hZ' hC' d₀ hd
    obtain ⟨D', hD'⟩ := pRepEx l hl Ω A hA j Φ c β ζ hζ _ ops'.2 hHS'
    have hθn : ‖φ (g : ZMod l) * (g : Qbar l) ^ k‖ = 1 := by
      have hcop : g.Coprime l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hg).symm
      have h1 := DirichletCharacter.unit_norm_eq_one φ (ZMod.unitOfCoprime g hcop)
      rw [ZMod.coe_unitOfCoprime] at h1
      rw [norm_mul, norm_pow, norm_nat_eq g hg, h1, one_pow, one_mul]
    have hrel : ∀ m, ∀ s ∈ Hm l A m, ∀ x, (l : Qbar l) ^ c₂ * sharp d₀ hd Z m s x =
        sharp d₀ hd Z' m s (x * un g hg m) - φ (g : ZMod l) * (g : Qbar l) ^ k * sharp d₀ hd Z' m s x := by
      intro m s hs x
      have r1 := rel m s hs x
      have r2 := rel m s hs (x * un d₀ hd m)
      simp only [sharp, tr] at r1 r2 ⊢
      rw [mul_right_comm x (un d₀ hd m) (un g hg m)] at r2
      linear_combination r1 - (d₀ : Qbar l) * r2
    by_cases hθ : φ (g : ZMod l) * (g : Qbar l) ^ k ∈ c.O
    · let θ : c.O := ⟨_, hθ⟩
      have R1 := pRepSmul l hl Ω A hA j Φ c β ζ hζ _ D ((l : c.O) ^ c₂) hD
      have R2 := pRepSmul l hl Ω A hA j Φ c β ζ hζ _ D' θ hD'
      have R3 := (pRepAdd l hl Ω A hA j Φ c β ζ hζ).1 _ _ _ _ R1 R2
      have R4 := pRepTr l hl Ω A hA j Φ c β ζ hζ _ ops'.2 g hg D' hD'
      have heq := pRepUniq l hl Ω A hA j Φ c β ζ hζ _ _ _ _ R3 R4 (fun m s hs => by
        have h1 := hrel m s hs 1
        have e : (((l : c.O) ^ c₂ : c.O) : PadicAlgCl l) = (l : Qbar l) ^ c₂ := by simp
        rw [e]
        change _ + (φ (g : ZMod l) * (g : Qbar l) ^ k) * _ = sharp d₀ hd Z' m s (1 * un g hg m)
        rw [h1]
        ring)
      refine pClause2 l hl Ω A hA j Φ hj c β D D' Gs v g c₂ k φ θ hg rfl hv hGn hlam fun i => ?_
      have := congrFun heq i
      rw [eq_sub_iff_add_eq]
      exact this
    · have hz' : ∀ m, ∀ s ∈ Hm l A m, ∀ x, sharp d₀ hd Z' m s x = 0 := by
        intro m s hs x
        by_contra h0
        have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
        refine hθ (mem_of_mul_mem c hθn (ops'.2.int m s hsI x) h0 ?_)
        have h1 := hrel m s hs x
        have e : φ (g : ZMod l) * (g : Qbar l) ^ k * sharp d₀ hd Z' m s x =
            sharp d₀ hd Z' m s (x * un g hg m) - (l : Qbar l) ^ c₂ * sharp d₀ hd Z m s x := by
          rw [h1]; ring
        rw [e]
        exact c.O.sub_mem (ops'.2.int m s hsI _) (c.O.mul_mem (pow_mem (natCast_mem _ _) _) (hops.2.int m s hsI x))
      have hz : ∀ m, ∀ s ∈ Hm l A m, sharp d₀ hd Z m s 1 = 0 := by
        intro m s hs
        have h1 := hrel m s hs 1
        rw [hz' m s hs, hz' m s hs, mul_zero, sub_zero] at h1
        exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ GlobalTheory.LambdaValuationPowers.natCast_ne_zero)
      have h0 := pRepUniq l hl Ω A hA j Φ c β ζ hζ _ _ D 0 hD
        ((pRepAdd l hl Ω A hA j Φ c β ζ hζ).2 _ hz) (fun _ _ _ => rfl)
      have hG0 : Gs = 0 := by
        ext n
        have h1 := hlam n
        have hv0 : v ≠ 0 := by rintro rfl; simp at hv
        have h2 : Φ.lam β (fun i => (D i).coeff n) = 0 := by simp [h0, Fr.lam]
        rw [h2] at h1
        have h3 := (mul_eq_zero.1 h1.symm).resolve_left hv0
        simpa using h3
      rw [hG0]
      intro n
      exact ⟨0, fun r _ ξ _ => by simp [Cg, intg, mass, tval]⟩

end UpperTheory.Kd.C7
end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.LocalUnitsRoots

variable {l : ℕ} [Fact l.Prime]

private theorem cg_symm {n : ℕ} {x y : Qbar l} (h : Cg n x y) : Cg n y x := by
  unfold Cg at *; rwa [norm_sub_rev]

private theorem cg_trans {n : ℕ} {x y w : Qbar l} (h₁ : Cg n x y) (h₂ : Cg n y w) : Cg n x w := by
  unfold Cg at *
  calc ‖x - w‖ = ‖(x - y) + (y - w)‖ := by ring_nf
    _ ≤ max ‖x - y‖ ‖y - w‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le h₁ h₂

private theorem cg_mono {n n' : ℕ} (hn : n ≤ n') {x y : Qbar l} (h : Cg n' x y) : Cg n x y := by
  unfold Cg at *
  refine h.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ l) hn

private theorem cg_mul {n : ℕ} {t x y : Qbar l} (ht : ‖t‖ ≤ 1) (h : Cg n x y) : Cg n (t * x) (t * y) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖t‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h

private theorem norm_char_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (x : ZMod N) : ‖ψ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have h1 : (ψ (u : ZMod N)) ^ (Fintype.card (ZMod N)ˣ) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have h2 : ‖ψ (u : ZMod N)‖ ^ (Fintype.card (ZMod N)ˣ) = 1 := by rw [← norm_pow, h1, norm_one]
    have hc : Fintype.card (ZMod N)ˣ ≠ 0 := Fintype.card_ne_zero
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hc).mp h2)
  · rw [MulChar.map_nonunit ψ hx, norm_zero]; exact zero_le_one

private theorem norm_factor_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (d : ℕ) :
    ‖(1 - (d : Qbar l) * ψ (d : ZMod N))‖ ≤ 1 := by
  have h1 := norm_char_le_one ψ (d : ZMod N)
  have h2 := IsUltrametricDist.norm_natCast_le_one (Qbar l) d
  calc _ ≤ max ‖(1 : Qbar l)‖ ‖(d : Qbar l) * ψ (d : ZMod N)‖ := by
        rw [sub_eq_add_neg, ← norm_neg ((d : Qbar l) * _)]; exact IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := by
      refine max_le (by rw [norm_one]) ?_
      rw [norm_mul]
      calc _ ≤ 1 * 1 := mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cycMod_eq_one {s : G ℚ Ω} (h : cycBar ℚ Ω l s = 1) (m : ℕ) : cycMod ℚ Ω l m s = 1 := by
  have h1 : cycZ ℚ Ω l s = 1 := by
    have h2 := congrArg (fun u : (Qbar l)ˣ => (u : Qbar l)) h
    simp only [cycBar, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      RingHom.comp_apply, Units.val_one] at h2
    have h3 : PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = (1 : ℚ_[l]) :=
      (algebraMap ℚ_[l] (Qbar l)).injective (by rw [h2, map_one])
    exact Units.ext (Subtype.ext h3)
  simp only [cycMod, MonoidHom.comp_apply, h1, map_one]

private theorem roots_pow {ζ : ℕ → Ω} (h : Roots l ζ) (c m : ℕ) (hc : c ≤ m) : ζ m ^ l ^ c = ζ (m - c) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hc
  rw [Nat.add_sub_cancel]
  clear hc
  induction c with
  | zero => simp
  | succ c ih => rw [pow_succ', pow_mul, ← add_assoc, (h (k + c)).2, ih]

private theorem conj_law {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {Z : Sy Ω l}
    (hIw : IwSys2 c A ν Z) (hν : ∀ s ∈ Ine (F := ℚ) A, ν s = 1) {σ : G ℚ Ω} (hσ : σ ∈ Dec (F := ℚ) A)
    (hcy : cycBar ℚ Ω l σ = 1) (m : ℕ) {s : G ℚ Ω} (hs : s ∈ Hm l A m) :
    Z m (σ * s * σ⁻¹) 1 = (ν σ : Qbar l) * Z m s 1 := by
  obtain ⟨hsI, hsc⟩ := Subgroup.mem_inf.1 hs
  rw [MonoidHom.mem_ker] at hsc
  have hsD := Ine_le_Dec A hsI
  have hc := cycMod_eq_one hcy m
  have coc := (hIw.2.1 m).2
  have h0 : Z m 1 1 = 0 := by
    have := coc 1 (one_mem _) 1 (one_mem _) 1
    rw [hν 1 (one_mem _)] at this
    simpa using this
  have h1 := coc σ hσ σ⁻¹ (inv_mem hσ) 1
  have h2 := coc σ hσ s hsD 1
  have h3 := coc (σ * s) (mul_mem hσ hsD) σ⁻¹ (inv_mem hσ) 1
  rw [hIw.1 σ hσ s hsD, hν s hsI, map_mul, hc, hsc] at h3
  rw [mul_inv_cancel, h0, hc] at h1
  rw [hc] at h2
  simp only [inv_one, mul_one] at h1 h2 h3
  rw [h3, h2]
  linear_combination -h1

private theorem main
    (h48 : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Gs L : PowerSeries (Qbar l)) (a a' κ : Qbar l) (v v' : ℕ → Qbar l) (c₀ m₀ c₁ n₀ : ℕ) (φ : DirichletCharacter (Qbar l) l) (e : ℕ), l ≠ 2 → 1 ≤ e → 2 ≤ m₀ → (∀ n, Gs.coeff n ∈ c.O) → (∀ n, L.coeff n ∈ c.O) → ‖a‖ = 1 → ‖a'‖ = 1 → κ ≠ 0 → (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) → (∀ m, ‖v' m‖ = 1 ∧ Cg m (v' (m + 1)) (v' m)) → 2 ≤ c₀ → ¬ l ∣ c₀ → (∀ m, m₀ ≤ m → ∃ z : Qbar l, IsPrimitiveRoot z (l ^ m) ∧ ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → Cg (m - c₁) ((1 - (c₀ : Qbar l) * ψ⁻¹ (c₀ : ZMod (l ^ m))) * (v' m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) (v m * a ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval Gs (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) → (∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0) → ∃ n₁ r₁ : ℕ, ∀ r, r₁ ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₁ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass Gs r ξ x) 0)
    (h50 : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → mat W s 1 1 = 1) :
    GlobalTheory.KZ.ZetaEulerSystemNonvanishing GlobalTheory.KZ.Pin7 := by
  intro l _ Ω _ _ _ ι e S A W g hN hS c y S' ν χ Z hSys hIw hSp hPin
  obtain ⟨a, a', κ, v', j, Rhs, L, φ, m₀, c₀, n₀, hInu, ⟨σ₀, hσ₀, hF₀, hν₀⟩, ha, ha', hv', hκ, hj, hL, ⟨ζ, hζ, hHT⟩,
    hRhs, hχ, hNZ⟩ := hPin
  have hl2 : l ≠ 2 := hN.l_odd
  have he : 1 ≤ e := hN.e_pos
  have hA : OverL l A := hN.atL
  have hl2' : ¬ l ∣ 2 := fun h => hl2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h)
  have hR : Roots l ζ := hζ
  by_contra hnz
  have hy : ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → y s 1 = 0 := by
    intro s hs hc
    by_contra h0
    exact hnz ⟨s, hs, hc, h50 l Ω ι e S A W g hN hS s hs hc, h0⟩
  have hSZ : SpZero A φ e Z := by
    intro n
    obtain ⟨r₀, hr₀⟩ := hSp n
    refine ⟨max r₀ 1, fun r hr s hs hc => ?_⟩
    have h1 := hr₀ r (le_trans (le_max_left _ _) hr) s hs hc
    have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
    have heq : (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) = eta φ e r := by
      funext x
      rw [hχ r hr1 x, mul_comm]
    rw [heq, hy s hs hc] at h1
    exact cg_symm h1
  have hI : IwI c A Z := by
    refine ⟨fun r s _ x => (hIw.2.1 r).1 s x, fun r s hs t ht x => ?_, fun r s _ x => hIw.2.2 r s x⟩
    rw [(hIw.2.1 r).2 s (Ine_le_Dec A hs) t (Ine_le_Dec A ht) x, hInu s hs, Units.val_one, one_mul]
  have hFr : ∀ σ ∈ Dec (F := ℚ) A, IsFrob A l σ → cycBar ℚ Ω l σ = 1 → ∀ m, ∀ s ∈ Hm l A m,
      Z m (σ * s * σ⁻¹) 1 = a * Z m s 1 := by
    intro σ hσ hF hc m s hs
    have h1 := (pFrobEx l hl2 Ω A hA).2.1 σ₀ hσ₀ σ hσ hF₀ hF
    have h2 := hIw.1 σ₀ hσ₀ _ (Ine_le_Dec A h1)
    rw [mul_inv_cancel_left, hInu _ h1, mul_one] at h2
    rw [conj_law hIw hInu hσ hc m hs, h2, hν₀]
  obtain ⟨Gs, v, c₁, m₁, hGs, hv, hrel, hint⟩ := pCore l hl2 Ω A hA c Z a j 2 c₀ (max m₀ c₀) ζ hI ha hFr hj hl2' hR (by
    intro m hm
    obtain ⟨κι, hfin, P, o, hP, -⟩ := hHT m (le_trans (le_max_left _ _) hm)
    refine ⟨κι, hfin, P, o, hP.2.1, hP.2.2.1, ?_⟩
    rw [← roots_pow hR c₀ m (le_trans (le_max_right _ _) hm)]
    exact hP.2.2.2.2)
  have hprim : ∀ m, IsPrimitiveRoot (j (ζ m)) (l ^ m) := fun m => (hζ m).1.map_of_injective j.injective
  obtain ⟨n₁, r₂, hG⟩ := h48 l c Gs L a a' κ v v' 2 (max (max m₀ c₀) (max m₁ 2)) (max c₀ c₁) n₀ φ e hl2 he
    (by omega) hGs hL ha ha' hκ hv hv' le_rfl hl2' (by
      intro m hm
      have hm0 : m₀ ≤ m := by omega
      obtain ⟨κι, hfin, P, o, hP, hlaw⟩ := hHT m hm0
      refine ⟨j (ζ m), hprim m, fun ψ hψ => ?_⟩
      have ht := norm_factor_le_one ψ⁻¹ 2
      have e1 := cg_mul ht (cg_symm (hRhs m hm0 ψ hψ _ (hprim m)))
      have e2 := cg_mul ht (cg_symm (hlaw ψ hψ))
      have e3 := hrel m (by omega) κι hfin P o hP.2.1 hP.2.2.1 (by
        rw [← roots_pow hR c₀ m (by omega)]
        exact hP.2.2.2.2) ψ
      exact cg_trans (cg_mono (by omega) (cg_trans e1 e2)) (cg_mono (by omega) e3)) hNZ
  obtain ⟨r₃, hr₃⟩ := hint φ e he hSZ n₁
  exact hG (max r₂ r₃) (le_max_left _ _) _ (hprim _) (hr₃ _ (le_max_right _ _) _ (hprim _))

end UpperTheory.Kd.C7.LocalUnitsRoots

theorem UpperTheory.Kd.C7.pLocu :
    GlobalTheory.KZ.ZetaEulerSystemNonvanishing GlobalTheory.KZ.Pin7 :=
  UpperTheory.Kd.C7.LocalUnitsRoots.main GlobalTheory.T.nonvanishing_transfer_characterSums_powerSeries GlobalTheory.T.quotient_char_trivial_inertia_cyclotomic_tower
end
