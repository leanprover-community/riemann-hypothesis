import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftSLMapMulInvMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTraceStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsOfEmbedding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntModLevelPrimePowEqAddMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxCoefficientSeqOneMemSubring
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjectiveStatement
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.OrderOfTranslationMod
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCongrOfModEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.RingHomApplySmoothedEisensteinCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinRootPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCoeffShiftSecondIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.CardFiberReductionEqTotient
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SumLevelSubgroupModEqSmulSumReps
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.CongruenceActionInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.TwistedEisensteinPieceTrivialCharacterEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.InZlClosedAddMulAndCyclotomicGaloisStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.IsPrimitiveRootEOmAndPowCompatible
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.RepMApplyZtEqPowRedTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.CmulSmFInvariantOfCongruentMulTPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.Gamma0DiamondActionEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.PieceTLevelRaiseEqVp
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.PieceTDetFiberEqPieceTRootPow

section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L.InertiaZetaPowers

open Finset

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

private theorem zpow_mem_closure {x : Ω} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) (k : ℤ) :
    x ^ k ∈ Subring.closure {x} := by
  have hxm : x ∈ Subring.closure {x} := Subring.subset_closure (Set.mem_singleton x)
  have hinv : x⁻¹ = x ^ (m - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hm, hx]
  cases k with
  | ofNat a =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hxm a
  | negSucc a =>
    rw [zpow_negSucc, ← inv_pow, hinv]
    exact pow_mem (pow_mem hxm _) _

private theorem zeta_pow (ε : Ω →+* ℂ) (l N L : ℕ) [NeZero l] [NeZero N] :
    eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ N = zt ε l L := by
  have hl : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  apply ε.injective
  rw [map_pow, zt, (eOm_props ε ε.injective).1, (eOm_props ε ε.injective).1, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

private theorem zeta_zpow_mem (ε : Ω →+* ℂ) (l N L : ℕ) [NeZero l] [NeZero N] (k : ℤ) :
    eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ ((N : ℤ) * k) ∈ Subring.closure {zt ε l L} := by
  rw [zpow_mul, zpow_natCast, zeta_pow]
  exact zpow_mem_closure (Nat.pow_pos (Nat.pos_of_ne_zero (NeZero.ne l))) (IsNTr.isPrimitiveRoot_zt ε l L).pow_eq_one k

private theorem closure_le_adjoin (ε : Ω →+* ℂ) (l L : ℕ) {y : Ω} (h : y ∈ Subring.closure {zt ε l L}) :
    y ∈ IntermediateField.adjoin ℚ {zt ε l L} :=
  (Subring.closure_le (t := (IntermediateField.adjoin ℚ {zt ε l L}).toSubring)).2
    (IntermediateField.subset_adjoin ℚ _) h

private theorem eisF_mem (F : IntermediateField ℚ Ω) (j M N : ℕ) (ζ : Ω) (a₁ b : ℤ) (n : ℕ)
    (h : ∀ k : ℤ, ζ ^ ((N : ℤ) * k) ∈ F) : eisF j M ζ a₁ ((N : ℤ) * b) n ∈ F := by
  have hq : ∀ q : ℚ, (q : Ω) ∈ F := fun q => by simpa using F.algebraMap_mem q
  have hh : (1 / 2 : Ω) ∈ F := by simpa using hq (1 / 2)
  unfold eisF
  split_ifs with h0
  · unfold const0
    split_ifs
    · exact div_mem (mul_mem hh (add_mem (one_mem _) (h b))) (sub_mem (one_mem _) (h b))
    · exact hq _
    · exact neg_mem (hq _)
  · unfold coefPos
    refine sum_mem fun d _ => sub_mem ?_ ?_
    · split_ifs
      · refine mul_mem (pow_mem (div_mem (natCast_mem F _) (natCast_mem F _)) _) ?_
        rw [show (N : ℤ) * b * (d : ℤ) = (N : ℤ) * (b * d) by ring]
        exact h _
      · exact zero_mem _
    · split_ifs
      · refine mul_mem (pow_mem (neg_mem (div_mem (natCast_mem F _) (natCast_mem F _))) _) ?_
        rw [show -((N : ℤ) * b * (d : ℤ)) = (N : ℤ) * (-(b * d)) by ring]
        exact h _
      · exact zero_mem _

private theorem zpow_memF (F : IntermediateField ℚ Ω) {x : Ω} (hx : x ∈ F) (k : ℤ) : x ^ k ∈ F := by
  cases k with
  | ofNat a =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hx a
  | negSucc a =>
    rw [zpow_negSucc]
    exact inv_mem (pow_mem hx _)

private theorem smF_mem (F : IntermediateField ℚ Ω) (c : ℤ) (j M N : ℕ) (ζ : Ω) (a₁ a₂ : ℤ) (n : ℕ)
    (hd : (N : ℤ) ∣ a₂) (h : ∀ k : ℤ, ζ ^ ((N : ℤ) * k) ∈ F) : smF c j M ζ a₁ a₂ n ∈ F := by
  obtain ⟨b, rfl⟩ := hd
  unfold smF
  refine sub_mem (mul_mem (pow_mem (intCast_mem F c) _) (eisF_mem F j M N ζ a₁ b n h))
    (mul_mem (zpow_memF F (intCast_mem F c) _) ?_)
  rw [show c * ((N : ℤ) * b) = (N : ℤ) * (c * b) by ring]
  exact eisF_mem F j M N ζ _ _ n h

private theorem mem_closure_of_isIntegral (ε : Ω →+* ℂ) (l L : ℕ) [Fact l.Prime] [CharZero Ω] {y : Ω}
    (hy : y ∈ IntermediateField.adjoin ℚ {zt ε l L}) (hi : IsIntegral ℤ y) :
    y ∈ Subring.closure {zt ε l L} := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero (l ^ L) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hz := IsNTr.isPrimitiveRoot_zt ε l L
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI hcyc : IsCyclotomicExtension {l ^ L} ℚ (IntermediateField.adjoin ℚ {zt ε l L}) :=
    by
      convert hz.intermediateField_adjoin_isCyclotomicExtension ℚ
      · rfl
      · exact Subsingleton.elim _ _
  let zF : IntermediateField.adjoin ℚ {zt ε l L} := ⟨zt ε l L, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hzF : IsPrimitiveRoot zF (l ^ L) :=
    IsPrimitiveRoot.of_map_of_injective (f := (IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype) hz
      (IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype.injective
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow
    (p := l) (k := L) (ζ := zF) hzF
  have hi' : IsIntegral ℤ (⟨y, hy⟩ : IntermediateField.adjoin ℚ {zt ε l L}) :=
    (isIntegral_algHom_iff ((IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype.toIntAlgHom)
      (IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype.injective).1 hi
  obtain ⟨t, ht⟩ := hcl.isIntegral_iff.1 hi'
  have key : ∀ s ∈ Algebra.adjoin ℤ ({zF} : Set (IntermediateField.adjoin ℚ {zt ε l L})),
      ((s : IntermediateField.adjoin ℚ {zt ε l L}) : Ω) ∈ Subring.closure {zt ε l L} := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact Subring.subset_closure rfl
    | algebraMap r => simpa using intCast_mem (Subring.closure {zt ε l L}) r
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | mul x y _ _ hx hy => simpa using mul_mem hx hy
  have e : y = (((t : IntermediateField.adjoin ℚ {zt ε l L})) : Ω) := by
    have := congrArg (fun s : IntermediateField.adjoin ℚ {zt ε l L} => (s : Ω)) ht
    exact this.symm
  rw [e]
  exact key _ t.2

private theorem inZl_of_mem {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {y : Ω} (h : y ∈ Subring.closure {zt ε l L}) :
    InZl ε l L y :=
  ⟨1, fun h1 => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h1), by simpa using h⟩

private theorem inZl_add {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {a b : Ω} (ha : InZl ε l L a) (hb : InZl ε l L b) :
    InZl ε l L (a + b) := by
  obtain ⟨D, hD, h⟩ := ha
  obtain ⟨D', hD', h'⟩ := hb
  refine ⟨D * D', fun hd => ((Fact.out : l.Prime).dvd_mul.1 hd).elim hD hD', ?_⟩
  have e : ((D * D' : ℕ) : Ω) * (a + b) = (D' : Ω) * ((D : Ω) * a) + (D : Ω) * ((D' : Ω) * b) := by
    push_cast
    ring
  rw [e]
  exact add_mem (mul_mem (natCast_mem _ _) h) (mul_mem (natCast_mem _ _) h')

private theorem inZl_mul {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {a b : Ω} (ha : InZl ε l L a) (hb : InZl ε l L b) :
    InZl ε l L (a * b) := by
  obtain ⟨D, hD, h⟩ := ha
  obtain ⟨D', hD', h'⟩ := hb
  refine ⟨D * D', fun hd => ((Fact.out : l.Prime).dvd_mul.1 hd).elim hD hD', ?_⟩
  have e : ((D * D' : ℕ) : Ω) * (a * b) = ((D : Ω) * a) * ((D' : Ω) * b) := by
    push_cast
    ring
  rw [e]
  exact mul_mem h h'

private theorem inZl_sum {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → Ω)
    (h : ∀ i ∈ s, InZl ε l L (f i)) : InZl ε l L (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inZl_of_mem (zero_mem _)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inZl_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end UpperTheory.Kd.L.InertiaZetaPowers

namespace UpperTheory.Kd.L.InertiaZetaPowers

open Finset

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω]

private theorem smF_one_mem (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c L : ℕ) (hL : 1 ≤ L)
    (hc : Nat.Coprime c (6 * l * N)) (a a₂ : ℤ) (ha : ¬ (l : ℤ) ∣ a) (h₂ : (N : ℤ) ∣ a₂) (r : ℕ) :
    smF (c : ℤ) 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) a a₂ r ∈ Subring.closure {zt ε l L} := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, rfl⟩ := h₂
  have hcN : Nat.Coprime c N := hc.coprime_dvd_right (Dvd.intro_left _ rfl)
  have hcl : Nat.Coprime c l := hc.coprime_dvd_right ((Dvd.intro_left _ rfl : l ∣ 6 * l).mul_right N)
  refine smF_one_mem_subring Ω _ c (N * l ^ L) _ a _
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) (Nat.pow_pos (Nat.pos_of_ne_zero (NeZero.ne l))))
    (Nat.Coprime.mul_right hcN (Nat.Coprime.pow_right L hcl)) ?_ (zeta_zpow_mem ε l N L b) ?_ r
  · intro h
    refine ha (dvd_trans ?_ h)
    exact_mod_cast Dvd.dvd.mul_left (dvd_pow_self l (by omega : L ≠ 0)) N
  · rw [show -((N : ℤ) * b) = (N : ℤ) * (-b) by ring]
    exact zeta_zpow_mem ε l N L _

private theorem cong_step (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c L w : ℕ) (hw : 1 ≤ w)
    (h2 : l ≠ 2) (hlN : ¬ l ∣ N) (hc : Nat.Coprime c (6 * l * N)) (hb : (w + 1) ^ 2 * l ≤ l ^ L)
    (α a₁ a₂ : ℤ) (h0 : 0 ≤ α) (hlt : α < (l : ℤ) ^ L) (hcong : a₁ ≡ N * α [ZMOD (l : ℤ) ^ L]) (h₂ : (N : ℤ) ∣ a₂) (r : ℕ) :
    ∃ β : Ω, InZl ε l L β ∧ (l : Ω) ^ (L - 1) * β =
      (α : Ω) ^ w * smF (c : ℤ) 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) a₁ a₂ r -
        (l : Ω) ^ (L * w) * smF (c : ℤ) (w + 1) (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) a₁ a₂ r := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hζ : IsPrimitiveRoot (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (N * l ^ L) :=
    isPrimitiveRoot_eOm ε (Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (NeZero.ne l)))
  have hcl : Nat.Coprime c l := hc.coprime_dvd_right ((Dvd.intro_left _ rfl : l ∣ 6 * l).mul_right N)
  have hlc : ¬ (l : ℤ) ∣ (c : ℤ) := fun h =>
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hcl.symm) (Int.natCast_dvd_natCast.1 h)
  obtain ⟨D, hD, hint⟩ := GlobalTheory.EisCongGen.smF_congr_gen l N L (w + 1) Ω _ h2 hζ
    (Nat.pos_of_ne_zero (NeZero.ne N)) hlN (by omega) hb (c : ℤ) hlc α a₁ a₂ h0 hlt hcong r
  rw [Nat.add_sub_cancel] at hint
  have hF : ∀ k : ℤ, eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ ((N : ℤ) * k) ∈ IntermediateField.adjoin ℚ {zt ε l L} :=
    fun k => closure_le_adjoin ε l L (zeta_zpow_mem ε l N L k)
  refine ⟨_, ?_, mul_div_cancel₀ _ (pow_ne_zero _ hl0)⟩
  refine ⟨D, hD, mem_closure_of_isIntegral ε l L ?_ ?_⟩
  · refine mul_mem (natCast_mem _ _) (div_mem (sub_mem (mul_mem (pow_mem (intCast_mem _ _) _) ?_)
      (mul_mem (pow_mem (natCast_mem _ _) _) ?_)) (pow_mem (natCast_mem _ _) _))
    · exact smF_mem _ _ _ _ N _ _ _ _ h₂ hF
    · exact smF_mem _ _ _ _ N _ _ _ _ h₂ hF
  · rw [← mul_div_assoc]
    exact hint

private theorem comb (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (L n w m : ℕ) (hnL : n < L) (A₁ A₂ B : ℕ → Ω)
    (α u : ℤ) (e : ℕ) (he : (e : ℤ) = α ^ w + (l : ℤ) ^ n * u)
    (hA : ∀ r, A₁ r ∈ Subring.closure {zt ε l L}) (hB : ∀ r, B r ∈ Subring.closure {zt ε l L})
    (hβ : ∀ r, ∃ β : Ω, InZl ε l L β ∧ (l : Ω) ^ (L - 1) * β = (α : Ω) ^ w * A₁ r - (l : Ω) ^ (L * w) * A₂ r) :
    ∃ E : Ω, InZl ε l L E ∧ (e : Ω) * cmul A₁ B m = (l : Ω) ^ (L * w) * cmul A₂ B m + (l : Ω) ^ n * E := by
  choose β hβ₁ hβ₂ using hβ
  refine ⟨∑ i ∈ range (m + 1), ((u : Ω) * A₁ i + (l : Ω) ^ (L - 1 - n) * β i) * B (m - i), ?_, ?_⟩
  · refine inZl_sum _ _ fun i _ => inZl_mul (inZl_add (inZl_of_mem (mul_mem (intCast_mem _ _) (hA i)))
      (inZl_mul (inZl_of_mem (pow_mem (natCast_mem _ _) _)) (hβ₁ i))) (inZl_of_mem (hB _))
  · have e1 : (e : Ω) = (α : Ω) ^ w + (l : Ω) ^ n * (u : Ω) := by
      have := congrArg (Int.cast : ℤ → Ω) he
      push_cast at this
      exact this
    have e2 : (l : Ω) ^ n * (l : Ω) ^ (L - 1 - n) = (l : Ω) ^ (L - 1) := by
      rw [← pow_add]
      congr 1
      omega
    unfold cmul
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    linear_combination (A₁ i * B (m - i)) * e1 - B (m - i) * hβ₂ i - (β i * B (m - i)) * e2

private theorem coefQ_nat (M : ℕ) (f : ℕ → Ω) (i : ℕ) : coefQ M f (i : ℚ) = f (M * i) := by
  have e : (i : ℚ) * (M : ℚ) = ((M * i : ℕ) : ℚ) := by
    push_cast
    ring
  unfold coefQ
  rw [e, if_pos ⟨Nat.cast_nonneg _, Rat.den_natCast _⟩, Rat.num_natCast, Int.toNat_natCast]

private theorem ex_eq (l n L w : ℕ) [Fact l.Prime] (hnL : n < L) (g : SL(2, ℤ)) :
    ∃ u : ℤ, ((ex l n w g : ℕ) : ℤ) = (en g 0 0 % (l : ℤ) ^ L) ^ w + (l : ℤ) ^ n * u := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h1 : (((((en g 0 0 : ℤ) : ZMod (l ^ n)).val : ℕ) : ℤ) : ZMod (l ^ n)) = ((en g 0 0 : ℤ) : ZMod (l ^ n)) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h2 := (ZMod.intCast_eq_intCast_iff _ _ (l ^ n)).1 h1
  have h3 : (l : ℤ) ^ n ∣ (l : ℤ) ^ L := pow_dvd_pow _ hnL.le
  have h4 : en g 0 0 % (l : ℤ) ^ L ≡ en g 0 0 [ZMOD (l : ℤ) ^ n] := Int.emod_emod_of_dvd _ h3
  have h5 : en g 0 0 % (l : ℤ) ^ L ≡ (((en g 0 0 : ℤ) : ZMod (l ^ n)).val : ℤ) [ZMOD (l : ℤ) ^ n] := by
    refine h4.trans (Int.ModEq.symm ?_)
    simpa using h2
  obtain ⟨u, hu⟩ := Int.modEq_iff_dvd.1 (h5.pow w)
  refine ⟨u, ?_⟩
  unfold ex
  push_cast
  linarith

end UpperTheory.Kd.L.InertiaZetaPowers

open UpperTheory.Kd.L.InertiaZetaPowers in
theorem UpperTheory.Kd.L.inzl :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (L n w : ℕ), 1 ≤ w → n < L → ∀ g : SL(2, ℤ), ¬ (l : ℤ) ∣ en g 0 0 → ¬ (l : ℤ) ∣ en g 1 0 → ∀ i : ℕ, InZl ε l L (EE ε l L N x c d g (i : ℚ)) ∧ ((w + 1) ^ 2 * l ≤ l ^ L → ∃ E : Ω, InZl ε l L E ∧ (ex l n w g : Ω) * EE ε l L N x c d g (i : ℚ) = (l : Ω) ^ (L * w) * cmul (smF c (w + 1) (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1)) (smF d 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1)) (l ^ L * i) + (l : Ω) ^ n * E) := by
  intro Ω _ _ _ _ ε l _ N _ c d gm hP x L n w hw hnL g hg0 hg1 i
  have hL : 1 ≤ L := by omega
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have hlL : (l : ℤ) ∣ (l : ℤ) ^ L := dvd_pow_self _ (by omega)
  have hNl : ¬ (l : ℤ) ∣ (N : ℤ) := fun h => hP.cop (Int.natCast_dvd_natCast.1 h)
  have ha : ¬ (l : ℤ) ∣ en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L) := by
    intro h
    rcases hlp.dvd_or_dvd h with h | h
    · exact hg0 h
    · exact hNl ((dvd_add_left (hlL.mul_left _)).1 h)
  have hb : ¬ (l : ℤ) ∣ en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0 := fun h =>
    hg1 ((dvd_add_right (hlL.mul_left _)).1 h)
  have hA := smF_one_mem ε l N c L hL hP.cc _ ((N : ℤ) ^ 2 * en g 0 1) ha ⟨(N : ℤ) * en g 0 1, by ring⟩
  have hB := smF_one_mem ε l N d L hL hP.dc _ ((N : ℤ) * en g 1 1) hb ⟨en g 1 1, rfl⟩
  have hEE : EE ε l L N x c d g (i : ℚ) = cmul (smF c 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1)) (smF d 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1)) (l ^ L * i) :=
    coefQ_nat _ _ _
  rw [hEE]
  refine ⟨inZl_of_mem (sum_mem fun r _ => mul_mem (hA r) (hB _)), fun hbd => ?_⟩
  obtain ⟨u, hu⟩ := ex_eq l n L w hnL g
  have hlpos : (0 : ℤ) < (l : ℤ) ^ L := by
    have := (Fact.out : l.Prime).pos
    positivity
  refine comb ε l L n w _ hnL _ _ _ (en g 0 0 % (l : ℤ) ^ L) u _ hu hA hB fun r => ?_
  refine cong_step ε l N c L w hw hP.odd hP.cop hP.cc hbd _ _ _ (Int.emod_nonneg _ hlpos.ne') (Int.emod_lt_of_pos _ hlpos) ?_
    ⟨(N : ℤ) * en g 0 1, by ring⟩ r
  refine Int.modEq_iff_dvd.2 ⟨-(N : ℤ) * (en g 0 0 / (l : ℤ) ^ L) - en g 0 0 * ((x.val : ℤ) * (topT l L N : ℤ)), ?_⟩
  rw [Int.emod_def]
  ring
end

section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L

private abbrev rd (a : ℕ) : SL(2, ℤ) →* SL(2, ZMod a) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod a))

private def red {a b : ℕ} (h : b ∣ a) : SL(2, ZMod a) →* SL(2, ZMod b) :=
  Matrix.SpecialLinearGroup.map (ZMod.castHom h (ZMod b))

private lemma rd_apply (a : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) : (rd a g) i j = ((g i j : ℤ) : ZMod a) := rfl

private lemma red_apply {a b : ℕ} (h : b ∣ a) (γ : SL(2, ZMod a)) (i j : Fin 2) :
    (red h γ) i j = ZMod.castHom h (ZMod b) (γ i j) := rfl

private def cj {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : SL(2, R) :=
  ⟨!![h 0 0, (u : R) * h 0 1; ((u⁻¹ : Rˣ) : R) * h 1 0, h 1 1], by
    have hd := h.det_coe
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
    linear_combination hd - h 0 1 * h 1 0 * hu⟩

private lemma cj00 {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : (cj u h) 0 0 = h 0 0 := rfl
private lemma cj01 {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : (cj u h) 0 1 = u * h 0 1 := rfl
private lemma cj10 {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : (cj u h) 1 0 = ((u⁻¹ : Rˣ) : R) * h 1 0 := rfl

open Classical in
private noncomputable def H2 (N : ℕ) [NeZero N] : Finset SL(2, ZMod (N * N)) :=
  Finset.univ.filter fun η => η ∈ (CongruenceSubgroup.Gamma1 N).map (rd (N * N))

private lemma gam_iff {N l : ℕ} {g : SL(2, ℤ)} :
    g ∈ Gam N l ↔ g ∈ CongruenceSubgroup.Gamma1 N ∧ g ∈ CongruenceSubgroup.Gamma0 l :=
  Subgroup.mem_inf

end UpperTheory.Kd.L

private theorem coe_uel_eq_umat (c d M : ℤ) (hc : c ≠ 0)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c → (p : ℤ) ∣ d → (p : ℤ) ∣ M → False) :
    ∃ t : ℤ, IsCoprime c (d + t * M) := by
  classical
  refine ⟨((∏ p ∈ c.natAbs.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ d), (p : ℕ) : ℕ) : ℤ), ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  rw [Int.gcd_eq_natAbs] at hpg
  have hpc : (p : ℤ) ∣ c := Int.ofNat_dvd_left.2 (hpg.trans (Nat.gcd_dvd_left _ _))
  have hpe := Int.ofNat_dvd_left.2 (hpg.trans (Nat.gcd_dvd_right _ _))
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hpd : (p : ℤ) ∣ d
  · have htM := (dvd_add_right hpd).1 hpe
    rcases hpz.dvd_or_dvd htM with hpt | hpM
    · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 (Int.natCast_dvd_natCast.1 hpt)
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hq
      have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq.1.1).1 hpq
      subst hpq'
      exact hq.2 hpd
    · exact h p hp hpc hpd hpM
  · have hpt : (p : ℤ) ∣ ((∏ p ∈ c.natAbs.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ d), (p : ℕ) : ℕ) : ℤ) := by
      apply Int.natCast_dvd_natCast.2
      apply Finset.dvd_prod_of_mem
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hp, Int.ofNat_dvd_left.1 hpc, Int.natAbs_ne_zero.2 hc⟩, hpd⟩
    exact hpd ((dvd_add_left (dvd_mul_of_dvd_left hpt M)).1 hpe)

private theorem exists_rd_eq (M : ℕ) (γ : SL(2, ZMod M)) : ∃ g : SL(2, ℤ), rd M g = γ := by
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (γ 0 0)
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective (γ 0 1)
  obtain ⟨c0, hc0⟩ := ZMod.intCast_surjective (γ 1 0)
  obtain ⟨d0, hd0⟩ := ZMod.intCast_surjective (γ 1 1)
  have h1 : (a : ZMod M) * d0 - b * c0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [ha, hb, hc0, hd0]
    exact this
  obtain ⟨s, hs⟩ : (M : ℤ) ∣ a * d0 - b * c0 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h1]
    ring
  obtain ⟨c, d, hc, hd, hcd⟩ : ∃ c d : ℤ, (c : ZMod M) = γ 1 0 ∧ (d : ZMod M) = γ 1 1 ∧ IsCoprime c d := by
    by_cases hc00 : c0 + (if c0 = 0 then (M : ℤ) else 0) = 0
    · have hc0z : c0 = 0 := by
        by_contra hne
        simp [hne] at hc00
      have hM : (M : ℤ) = 0 := by simpa [hc0z] using hc00
      refine ⟨c0, d0, hc0, hd0, ⟨0, a, ?_⟩⟩
      rw [hM, hc0z] at hs
      linarith
    · obtain ⟨t, ht⟩ := coe_uel_eq_umat _ d0 (M : ℤ) hc00 (by
        intro p hp h1 h2 h3
        have h1' : (p : ℤ) ∣ c0 := by
          split_ifs at h1 with hz
          · rw [hz]
            exact dvd_zero _
          · simpa using h1
        have h4 : (p : ℤ) ∣ 1 := by
          have e : (1 : ℤ) = a * d0 - b * c0 - M * s := by linarith
          rw [e]
          exact dvd_sub (dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1' _))
            (dvd_mul_of_dvd_left h3 _)
        have h5 := Int.eq_one_of_dvd_one (by positivity) h4
        exact hp.one_lt.ne' (by exact_mod_cast h5))
      refine ⟨_, _, ?_, ?_, ht⟩
      · split_ifs <;> push_cast <;> simp [hc0]
      · push_cast
        simp [hd0]
  obtain ⟨u, v, huv⟩ := hcd
  have h1' : (a : ZMod M) * d - b * c = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [ha, hb, hc, hd]
    exact this
  have h2 : (v : ZMod M) * d + u * c = 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod M)) huv
    push_cast at this
    linear_combination this
  obtain ⟨g, hg⟩ : ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) =
      !![v + ((b + u) * v + (a - v) * u) * c, -u + ((b + u) * v + (a - v) * u) * d; c, d] :=
    ⟨⟨_, by
      rw [Matrix.det_fin_two_of]
      linear_combination huv⟩, rfl⟩
  refine ⟨g, ?_⟩
  ext i j
  rw [rd_apply, hg]
  fin_cases i <;> fin_cases j
  · simp
    rw [← ha]
    linear_combination (-(v : ZMod M)) * h1' + (a : ZMod M) * h2
  · simp
    rw [← hb]
    linear_combination (u : ZMod M) * h1' + (b : ZMod M) * h2
  · simp [hc]
  · simp [hd]

private theorem red_rd_eq_rd_of_dvd {a b : ℕ} (h : b ∣ a) (g : SL(2, ℤ)) : red h (rd a g) = rd b g := by
  ext i j
  simp [red_apply, rd_apply]
private theorem chineseRemainder_fst_snd_eq_castHom {L Q : ℕ} (hLQ : L.Coprime Q) (x : ZMod (L * Q)) :
    (ZMod.chineseRemainder hLQ x).1 = ZMod.castHom (dvd_mul_right L Q) (ZMod L) x ∧
    (ZMod.chineseRemainder hLQ x).2 = ZMod.castHom (dvd_mul_left Q L) (ZMod Q) x := by
  constructor
  · show ((ZMod.cast x : ZMod L × ZMod Q)).1 = _
    rw [Prod.fst_zmod_cast]
    rfl
  · show ((ZMod.cast x : ZMod L × ZMod Q)).2 = _
    rw [Prod.snd_zmod_cast]
    rfl

private theorem eq_of_red_eq_of_coprime {L Q : ℕ} (hLQ : L.Coprime Q) (x y : SL(2, ZMod (L * Q)))
    (h1 : red (dvd_mul_right L Q) x = red (dvd_mul_right L Q) y)
    (h2 : red (dvd_mul_left Q L) x = red (dvd_mul_left Q L) y) : x = y := by
  ext i j
  apply (ZMod.chineseRemainder hLQ).injective
  have e1 := congrArg (fun z : SL(2, ZMod L) => z i j) h1
  have e2 := congrArg (fun z : SL(2, ZMod Q) => z i j) h2
  simp only [red_apply] at e1 e2
  refine Prod.ext ?_ ?_
  · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).1, (chineseRemainder_fst_snd_eq_castHom hLQ _).1]
    exact e1
  · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).2, (chineseRemainder_fst_snd_eq_castHom hLQ _).2]
    exact e2

private theorem exists_red_eq_pair_of_coprime {L Q : ℕ} (hLQ : L.Coprime Q) (δ : SL(2, ZMod L)) (η : SL(2, ZMod Q)) :
    ∃ x : SL(2, ZMod (L * Q)), red (dvd_mul_right L Q) x = δ ∧ red (dvd_mul_left Q L) x = η := by
  have hA : ∀ z : ZMod L × ZMod Q,
      ZMod.castHom (dvd_mul_right L Q) (ZMod L) ((ZMod.chineseRemainder hLQ).symm z) = z.1 :=
    fun z => by
      rw [← (chineseRemainder_fst_snd_eq_castHom hLQ _).1]
      exact congrArg Prod.fst ((ZMod.chineseRemainder hLQ).apply_symm_apply z)
  have hB : ∀ z : ZMod L × ZMod Q,
      ZMod.castHom (dvd_mul_left Q L) (ZMod Q) ((ZMod.chineseRemainder hLQ).symm z) = z.2 :=
    fun z => by
      rw [← (chineseRemainder_fst_snd_eq_castHom hLQ _).2]
      exact congrArg Prod.snd ((ZMod.chineseRemainder hLQ).apply_symm_apply z)
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) (ZMod (L * Q)),
      X = fun i j => (ZMod.chineseRemainder hLQ).symm (δ i j, η i j) := ⟨_, rfl⟩
  have hXA : (ZMod.castHom (dvd_mul_right L Q) (ZMod L)).mapMatrix X = (δ : Matrix (Fin 2) (Fin 2) (ZMod L)) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hX]
    exact hA _
  have hXB : (ZMod.castHom (dvd_mul_left Q L) (ZMod Q)).mapMatrix X = (η : Matrix (Fin 2) (Fin 2) (ZMod Q)) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hX]
    exact hB _
  have hdet : X.det = 1 := by
    apply (ZMod.chineseRemainder hLQ).injective
    rw [map_one]
    refine Prod.ext ?_ ?_
    · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).1]
      show ZMod.castHom (dvd_mul_right L Q) (ZMod L) X.det = 1
      rw [RingHom.map_det, hXA, δ.det_coe]
    · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).2]
      show ZMod.castHom (dvd_mul_left Q L) (ZMod Q) X.det = 1
      rw [RingHom.map_det, hXB, η.det_coe]
  obtain ⟨x, hx⟩ : ∃ x : SL(2, ZMod (L * Q)), (x : Matrix (Fin 2) (Fin 2) (ZMod (L * Q))) = X :=
    ⟨⟨X, hdet⟩, rfl⟩
  refine ⟨x, ?_, ?_⟩
  · ext i j
    rw [red_apply, hx]
    exact congrFun (congrFun hXA i) j
  · ext i j
    rw [red_apply, hx]
    exact congrFun (congrFun hXB i) j

private theorem mem_gs_iff_exists_rd_eq (N l M : ℕ) [NeZero M] (γ : SL(2, ZMod M)) :
    γ ∈ Gs N l M ↔ ∃ g ∈ Gam N l, rd M g = γ := by
  unfold Gs
  simp [Subgroup.mem_map]

private theorem castHom_eq_zero_iff_dvd_val (l k : ℕ) [NeZero (l ^ k)] (hd : l ∣ l ^ k) (x : ZMod (l ^ k)) :
    ZMod.castHom hd (ZMod l) x = 0 ↔ l ∣ x.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
private theorem sum_gs_red_eq_card_smul_sum_lower_zero (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (k : ℕ) (hk : k ≠ 0)
    (hlN : ¬ l ∣ N) [NeZero (l ^ k * (N * N))] {V : Type} [AddCommMonoid V]
    (F : SL(2, ZMod (l ^ k)) → V) :
    ∑ γ ∈ Gs N l (l ^ k * (N * N)), F (red (dvd_mul_right (l ^ k) (N * N)) γ) =
      (H2 N).card • ∑ δ ∈ Finset.univ.filter
        (fun δ : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0), F δ := by
  classical
  have hl : l.Prime := Fact.out
  have hLQ : (l ^ k).Coprime (N * N) := by
    have h : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
    exact Nat.Coprime.pow_left _ (Nat.Coprime.mul_right h h)
  set B := Finset.univ.filter
    (fun δ : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0) with hB
  calc ∑ γ ∈ Gs N l (l ^ k * (N * N)), F (red (dvd_mul_right (l ^ k) (N * N)) γ)
        = ∑ p ∈ B ×ˢ H2 N, F p.1 := by
        apply Finset.sum_nbij (fun γ => (red (dvd_mul_right (l ^ k) (N * N)) γ,
          red (dvd_mul_left (N * N) (l ^ k)) γ))
        · intro γ hγ
          obtain ⟨g, hg, rfl⟩ := (mem_gs_iff_exists_rd_eq _ _ _ γ).1 hγ
          rw [gam_iff] at hg
          rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd, Finset.mem_product, hB, Finset.mem_filter]
          refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [rd_apply, map_intCast]
            exact CongruenceSubgroup.Gamma0_mem.1 hg.2
          · unfold H2
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, Subgroup.mem_map_of_mem _ hg.1⟩
        · intro x _ y _ hxy
          simp only [Prod.mk.injEq] at hxy
          exact eq_of_red_eq_of_coprime hLQ x y hxy.1 hxy.2
        · rintro ⟨δ, η⟩ hp
          rw [Finset.mem_coe, Finset.mem_product, hB, Finset.mem_filter] at hp
          obtain ⟨⟨_, hδ⟩, hη⟩ := hp
          unfold H2 at hη
          rw [Finset.mem_filter] at hη
          obtain ⟨g0, hg0, hg0e⟩ := Subgroup.mem_map.1 hη.2
          obtain ⟨x, hx1, hx2⟩ := exists_red_eq_pair_of_coprime hLQ δ η
          obtain ⟨g, rfl⟩ := exists_rd_eq _ x
          rw [red_rd_eq_rd_of_dvd] at hx1 hx2
          refine ⟨rd _ g, ?_, ?_⟩
          · rw [Finset.mem_coe, mem_gs_iff_exists_rd_eq]
            refine ⟨g, ?_, rfl⟩
            rw [gam_iff]
            constructor
            · have E := congrArg (red (dvd_mul_right N N)) (hx2.trans hg0e.symm)
              rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd] at E
              have e : ∀ i j, ((g i j : ℤ) : ZMod N) = ((g0 i j : ℤ) : ZMod N) := fun i j => by
                have := congrArg (fun z : SL(2, ZMod N) => z i j) E
                simpa only [rd_apply] using this
              rw [CongruenceSubgroup.Gamma1_mem] at hg0 ⊢
              rw [e, e, e]
              exact hg0
            · rw [CongruenceSubgroup.Gamma0_mem]
              have := congrArg
                (fun z : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (z 1 0)) hx1
              simp only [rd_apply, map_intCast] at this
              rw [this]
              exact hδ
          · dsimp only
            rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd, hx1, hx2]
        · intro _ _
          rfl
    _ = ∑ δ ∈ B, ∑ _η ∈ H2 N, F δ := Finset.sum_product _ _ _
    _ = (H2 N).card • ∑ δ ∈ B, F δ := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun δ _ => Finset.sum_const _)
private theorem cj_inv_cj_eq_self {R : Type} [CommRing R] (u : Rˣ) (X : SL(2, R)) : cj u⁻¹ (cj u X) = X := by
  have e11 : ∀ (v : Rˣ) (Y : SL(2, R)), (cj v Y) 1 1 = Y 1 1 := fun _ _ => rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cj00, cj01, cj10, e11]

private theorem sum_cj_eq_sum_entries_not_dvd (l : ℕ) [Fact l.Prime] (k : ℕ) (hk : k ≠ 0)
    (gm : (ZMod l)ˣ → SL(2, ℤ))
    (col : ∀ r : (ZMod l)ˣ, ((gm r 1 0 : ℤ) : ZMod l) = -(r : ZMod l) * ((gm r 0 0 : ℤ) : ZMod l))
    (u : (ZMod (l ^ k))ˣ) {V : Type} [AddCommMonoid V] (Φ : SL(2, ZMod (l ^ k)) → V) :
    ∑ r : (ZMod l)ˣ, ∑ δ ∈ Finset.univ.filter
        (fun δ : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0),
        Φ (cj u (rd (l ^ k) (gm r) * δ)) =
      ∑ h ∈ Finset.univ.filter
        (fun h : SL(2, ZMod (l ^ k)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h := by
  classical
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set π := ZMod.castHom (dvd_pow_self l hk) (ZMod l) with hπ
  set B := Finset.univ.filter (fun δ : SL(2, ZMod (l ^ k)) => π (δ 1 0) = 0) with hB
  set S := Finset.univ.filter
    (fun h : SL(2, ZMod (l ^ k)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val) with hS
  have hS' : ∀ h, h ∈ S ↔ π (h 0 0) ≠ 0 ∧ π (h 1 0) ≠ 0 := by
    intro h
    rw [hS, Finset.mem_filter]
    constructor
    · rintro ⟨_, a, b⟩
      exact ⟨fun h0 => a ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).1 h0),
        fun h0 => b ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).1 h0)⟩
    · rintro ⟨a, b⟩
      exact ⟨Finset.mem_univ _, fun h0 => a ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).2 h0),
        fun h0 => b ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).2 h0)⟩
  have hu : π (u : ZMod (l ^ k)) * π ((u⁻¹ : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)) = 1 := by
    rw [← map_mul, u.mul_inv, map_one]
  have hu1 : π ((u⁻¹ : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hu
    exact zero_ne_one hu
  have hu2 : π (u : ZMod (l ^ k)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hu
    exact zero_ne_one hu
  have hA : ∀ r, π (rd (l ^ k) (gm r) 1 0) = -(r : ZMod l) * π (rd (l ^ k) (gm r) 0 0) := by
    intro r
    rw [rd_apply, rd_apply, map_intCast, map_intCast]
    exact col r
  have hA00 : ∀ r, π (rd (l ^ k) (gm r) 0 0) ≠ 0 := by
    intro r h0
    have hd := (gm r).det_coe
    rw [Matrix.det_fin_two] at hd
    have h1 := congrArg (fun x : ℤ => (x : ZMod l)) hd
    push_cast at h1
    rw [col r] at h1
    rw [rd_apply, map_intCast] at h0
    rw [h0] at h1
    simp at h1
  have pm : ∀ (X Y : SL(2, ZMod (l ^ k))) (i j : Fin 2),
      π ((X * Y) i j) = π (X i 0) * π (Y 0 j) + π (X i 1) * π (Y 1 j) := by
    intro X Y i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_mul]
  have pinv : ∀ X : SL(2, ZMod (l ^ k)), (X⁻¹) 1 0 = - X 1 0 ∧ (X⁻¹) 1 1 = X 0 0 := by
    intro X
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp
  have hB00 : ∀ δ ∈ B, π (δ 0 0) ≠ 0 := by
    intro δ hδ h0
    rw [hB, Finset.mem_filter] at hδ
    have hd := δ.det_coe
    rw [Matrix.det_fin_two] at hd
    have h1 := congrArg π hd
    rw [map_sub, map_mul, map_mul, h0, hδ.2, map_one] at h1
    simp at h1
  have e11 : ∀ (v : (ZMod (l ^ k))ˣ) (Y : SL(2, ZMod (l ^ k))), (cj v Y) 1 1 = Y 1 1 := fun _ _ => rfl
  obtain ⟨w, hw⟩ : ∃ w : ZMod l → (ZMod l)ˣ, ∀ x, x ≠ 0 → (w x : ZMod l) = x :=
    ⟨fun x => if hx : x = 0 then 1 else Units.mk0 x hx, fun x hx => by simp [hx]⟩
  obtain ⟨R, hR⟩ : ∃ R : SL(2, ZMod (l ^ k)) → (ZMod l)ˣ, ∀ h,
      R h = w (-(π ((cj u⁻¹ h) 1 0)) / π ((cj u⁻¹ h) 0 0)) := ⟨_, fun _ => rfl⟩
  have hcc : ∀ X, cj u (cj u⁻¹ X) = X := by
    intro X
    have := cj_inv_cj_eq_self u⁻¹ X
    rwa [inv_inv] at this
  rw [(Finset.sum_product' Finset.univ B (fun r δ => Φ (cj u (rd (l ^ k) (gm r) * δ)))).symm]
  apply Finset.sum_nbij' (fun p => cj u (rd (l ^ k) (gm p.1) * p.2))
    (fun h => (R h, (rd (l ^ k) (gm (R h)))⁻¹ * cj u⁻¹ h))
  · rintro ⟨r, δ⟩ hp
    rw [Finset.mem_product] at hp
    have hδ := hp.2
    have hδ' : π (δ 1 0) = 0 := by
      rw [hB, Finset.mem_filter] at hδ
      exact hδ.2
    rw [hS']
    dsimp only
    rw [cj00, cj10, map_mul, pm, pm, hδ', hA]
    refine ⟨?_, ?_⟩
    · rw [mul_zero, add_zero]
      exact mul_ne_zero (hA00 r) (hB00 δ hδ)
    · rw [mul_zero, add_zero]
      exact mul_ne_zero hu1 (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 r.ne_zero) (hA00 r)) (hB00 δ hδ))
  · intro h hh
    rw [hS'] at hh
    rw [Finset.mem_product, hB, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
    have h00 : π ((cj u⁻¹ h) 0 0) = π (h 0 0) := by rw [cj00]
    have h10 : π ((cj u⁻¹ h) 1 0) = π (u : ZMod (l ^ k)) * π (h 1 0) := by
      rw [cj10, inv_inv, map_mul]
    have hx : ((R h : (ZMod l)ˣ) : ZMod l) = -(π ((cj u⁻¹ h) 1 0)) / π ((cj u⁻¹ h) 0 0) := by
      rw [hR]
      apply hw
      rw [h00, h10]
      simp [hh.1, hh.2, hu2]
    have hh1 := hh.1
    rw [pm, (pinv _).1, (pinv _).2, map_neg, hA, hx, h00, h10]
    field_simp
    ring
  · rintro ⟨r, δ⟩ hp
    rw [Finset.mem_product] at hp
    have hδ := hp.2
    have hδ' : π (δ 1 0) = 0 := by
      rw [hB, Finset.mem_filter] at hδ
      exact hδ.2
    have hA0 := hA00 r
    have hδ0 := hB00 δ hδ
    have hRr : R (cj u (rd (l ^ k) (gm r) * δ)) = r := by
      rw [hR, cj_inv_cj_eq_self]
      apply Units.ext
      rw [hw]
      · rw [pm, pm, hδ', hA]
        simp only [mul_zero, add_zero]
        field_simp
      · rw [pm, pm, hδ', hA]
        simp only [mul_zero, add_zero]
        exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 r.ne_zero) hA0) hδ0))
          (mul_ne_zero hA0 hδ0)
    dsimp only
    rw [cj_inv_cj_eq_self, hRr, inv_mul_cancel_left]
  · intro h _
    dsimp only
    rw [mul_inv_cancel_left, hcc]
  · intro p _
    rfl
private theorem rd_liftSL (M : ℕ) (γ : SL(2, ZMod M)) : rd M (liftSL M γ) = γ := by
  unfold liftSL
  exact Classical.epsilon_spec (exists_rd_eq M γ)

theorem UpperTheory.Kd.L.count :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N], ∃ μ : ℕ, 0 < μ ∧ ∀ (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (n m : ℕ), 1 ≤ m → ∀ (V : Type) [AddCommMonoid V] (Φ : SL(2, ZMod (l ^ (m + n))) → V) (Ψ : SL(2, ℤ) → V), (∀ g ∈ CongruenceSubgroup.Gamma0 N, ((en g 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → ∀ h : SL(2, ZMod (l ^ (m + n))), h 0 0 = (en g 0 0 : ℤ) → h 0 1 = ((N : ℤ) * en g 0 1 : ℤ) → (N : ZMod (l ^ (m + n))) * h 1 0 = (en g 1 0 : ℤ) → h 1 1 = (en g 1 1 : ℤ) → Ψ g = Φ h) → ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Gs N l (topMu l n m N), Ψ (gm r₀ * liftSL _ γ) = μ • ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h := by
  classical
  intro l _ N _
  have hl : l.Prime := Fact.out
  refine ⟨(H2 N).card, ?_, ?_⟩
  · apply Finset.card_pos.2
    refine ⟨1, ?_⟩
    unfold H2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨1, Subgroup.one_mem _, map_one _⟩⟩
  intro c d gm hP n m hm V _ Φ Ψ hΨ
  obtain ⟨_, _, cop, _, _, _, _, g0, ga, col⟩ := hP
  unfold topMu
  have hk : m + n ≠ 0 := by omega
  haveI : NeZero (l ^ (m + n) * (N * N)) :=
    ⟨mul_ne_zero (pow_ne_zero _ hl.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
  have hcop : N.Coprime (l ^ (m + n)) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hl).2 cop).symm
  obtain ⟨u, hu⟩ : ∃ u : (ZMod (l ^ (m + n)))ˣ, (u : ZMod (l ^ (m + n))) = N :=
    ⟨ZMod.unitOfCoprime N hcop, ZMod.coe_unitOfCoprime _ _⟩
  have hNM : N ∣ l ^ (m + n) * (N * N) := (dvd_mul_right N N).trans (dvd_mul_left (N * N) _)
  have key : ∀ r₀ : (ZMod l)ˣ, ∀ γ ∈ Gs N l (l ^ (m + n) * (N * N)),
      Ψ (gm r₀ * liftSL _ γ) =
        Φ (cj u (rd (l ^ (m + n)) (gm r₀) * red (dvd_mul_right (l ^ (m + n)) (N * N)) γ)) := by
    intro r₀ γ hγ
    obtain ⟨g1, hg1, rfl⟩ := (mem_gs_iff_exists_rd_eq _ _ _ γ).1 hγ
    rw [gam_iff] at hg1
    have hL := rd_liftSL _ (rd (l ^ (m + n) * (N * N)) g1)
    set L1 := liftSL _ (rd (l ^ (m + n) * (N * N)) g1)
    rw [← hL, red_rd_eq_rd_of_dvd, ← map_mul]
    have E := congrArg (red hNM) hL
    rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd] at E
    have e : ∀ i j, ((L1 i j : ℤ) : ZMod N) = ((g1 i j : ℤ) : ZMod N) := fun i j => by
      have := congrArg (fun z : SL(2, ZMod N) => z i j) E
      simpa only [rd_apply] using this
    have hg1' := (CongruenceSubgroup.Gamma1_mem _ _).1 hg1.1
    have hL00 : ((L1 0 0 : ℤ) : ZMod N) = 1 := by rw [e]; exact hg1'.1
    have hL10 : ((L1 1 0 : ℤ) : ZMod N) = 0 := by rw [e]; exact hg1'.2.2
    have hgΓ : gm r₀ * L1 ∈ CongruenceSubgroup.Gamma0 N :=
      Subgroup.mul_mem _ (g0 r₀) (CongruenceSubgroup.Gamma0_mem.2 hL10)
    have hg00 : ((en (gm r₀ * L1) 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) := by
      rw [← ga r₀]
      unfold en
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      rw [hL00, hL10]
      ring
    apply hΨ _ hgΓ hg00
    · rw [cj00, rd_apply]
      rfl
    · rw [cj01, rd_apply, hu]
      unfold en
      push_cast
      ring
    · rw [cj10, ← hu, ← mul_assoc, Units.mul_inv, one_mul, rd_apply]
      rfl
    · rw [show (cj u (rd (l ^ (m + n)) (gm r₀ * L1))) 1 1 = (rd (l ^ (m + n)) (gm r₀ * L1)) 1 1 from rfl,
        rd_apply]
      rfl
  calc ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Gs N l (l ^ (m + n) * (N * N)), Ψ (gm r₀ * liftSL _ γ)
      = ∑ r₀ : (ZMod l)ˣ, (H2 N).card • ∑ δ ∈ Finset.univ.filter
          (fun δ : SL(2, ZMod (l ^ (m + n))) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0),
          Φ (cj u (rd (l ^ (m + n)) (gm r₀) * δ)) := by
        apply Finset.sum_congr rfl
        intro r₀ _
        rw [Finset.sum_congr rfl (key r₀)]
        exact sum_gs_red_eq_card_smul_sum_lower_zero l N (m + n) hk cop (fun δ => Φ (cj u (rd (l ^ (m + n)) (gm r₀) * δ)))
    _ = (H2 N).card • ∑ r₀ : (ZMod l)ˣ, ∑ δ ∈ Finset.univ.filter
          (fun δ : SL(2, ZMod (l ^ (m + n))) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0),
          Φ (cj u (rd (l ^ (m + n)) (gm r₀) * δ)) := by
        rw [Finset.smul_sum]
    _ = _ := by
        rw [sum_cj_eq_sum_entries_not_dvd l (m + n) hk gm col u Φ]
end

section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

noncomputable section
namespace UpperTheory.Kd.L

private def dgU {R : Type} [CommRing R] (u : Rˣ) : GL (Fin 2) R :=
  ⟨!![1, 0; 0, (u : R)], !![1, 0; 0, ((u⁻¹ : Rˣ) : R)], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def tw {R : Type} [CommRing R] (h : SL(2, R)) (u : Rˣ) : GL (Fin 2) R :=
  Matrix.SpecialLinearGroup.toGL h * dgU u

private theorem twist_column_zero {R : Type} [CommRing R] (h : SL(2, R)) (u : Rˣ) (i : Fin 2) :
    ((tw h u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 0 = h i 0 := by
  fin_cases i <;> simp [tw, dgU, Matrix.mul_apply, Fin.sum_univ_two]

private theorem twist_column_one {R : Type} [CommRing R] (h : SL(2, R)) (u : Rˣ) (i : Fin 2) :
    ((tw h u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 1 = (u : R) * h i 1 := by
  fin_cases i <;> simp [tw, dgU, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private abbrev kz {K : Type} [Field K] [CharZero K] (ζ : K) (l L N : ℕ) (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)) : ℕ → K :=
  cmul (smF (c : ℤ) (w + 1) (N * l ^ L) ζ (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1))
    (smF (d : ℤ) 1 (N * l ^ L) ζ (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1))

private abbrev kg {K : Type} [Field K] [CharZero K] (ζ : K) (l L N : ℕ) (c d : ℤ) (w : ℕ) (v v' : ℤ × ℤ)
    (γ : GL (Fin 2) (ZMod (l ^ L))) : ℕ → K :=
  cmul (smF c (w + 1) (N * l ^ L) ζ (rowT N l L γ 0 v).1 (rowT N l L γ 0 v).2)
    (smF d 1 (N * l ^ L) ζ (rowT N l L γ 1 v').1 (rowT N l L γ 1 v').2)

private theorem swap4 {V α β γ δ : Type} [AddCommMonoid V] (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → V) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ D, f a b c e = ∑ e ∈ D, ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c e := by
  have h1 : ∀ a, ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ D, f a b c e = ∑ c ∈ C, ∑ e ∈ D, ∑ b ∈ B, f a b c e := fun a => by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ c, ∑ a ∈ A, ∑ e ∈ D, ∑ b ∈ B, f a b c e = ∑ e ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c e := fun c => Finset.sum_comm
  simp_rw [h2]
  exact Finset.sum_comm

private theorem sum_key {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime]
    (N : ℕ) [NeZero N] (c d w : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (hP : Par l N c d gm) (x : ZMod N) (a₀ : ℤ) (ha₀ : (a₀ : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N)) (m n : ℕ) (hm : 1 ≤ m)
    (R : Finset SL(2, ZMod (topMu l n m N))) (hR : IsReps N l (topMu l n m N) R) (z : (ZMod (l ^ (m + n)))ˣ)
    (τ : (ZMod (l ^ (m + n)))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a (zt ε l (m + n)) = zt ε l (m + n) ^ (a : ZMod (l ^ (m + n))).val)
    (μ : ℕ) (hμ : ∀ (Φ : SL(2, ZMod (l ^ (m + n))) → Ω) (Ψ : SL(2, ℤ) → Ω), (∀ g ∈ CongruenceSubgroup.Gamma0 N, ((en g 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → ∀ h : SL(2, ZMod (l ^ (m + n))), h 0 0 = (en g 0 0 : ℤ) → h 0 1 = ((N : ℤ) * en g 0 1 : ℤ) → (N : ZMod (l ^ (m + n))) * h 1 0 = (en g 1 0 : ℤ) → h 1 1 = (en g 1 1 : ℤ) → Ψ g = Φ h) → ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Gs N l (topMu l n m N), Ψ (gm r₀ * liftSL _ γ) = μ • ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h)
    (i : ℕ) :
    ((topMu l n m N : ℕ) : Ω) * ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
      τ a (∑ y ∈ Finset.univ.filter (fun y => redTop l n m N y = z), ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
        repM (topM l n m (N * N)) y (kz (eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ))) l (m + n) N x c d w (gm r₀ * liftSL _ γ) (l ^ (m + n) * i))) =
    (μ : Ω) * (Nat.totient (N * N) : Ω) * ∑ γ ∈ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = (((z : ZMod (l ^ (m + n))).val : ℕ) : ZMod (l ^ m))),
      kg (eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ))) l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) γ (l ^ (m + n) * i) := by
  have hcop : ¬ l ∣ N := hP.cop
  have hroots := UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible ε l N
  obtain ⟨hpr, hzN, -⟩ := hroots
  set ζ : Ω := eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) with hζdef
  have hζN : ζ ^ N = zt ε l (m + n) := hzN (m + n)
  have hζ1 : ζ ^ (N * l ^ (m + n)) = 1 := (hpr (m + n)).pow_eq_one
  have hzt1 : zt ε l (m + n) ^ (l ^ (m + n)) = 1 := by rw [← hζN, ← pow_mul, hζ1]
  set A := Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]) with hA
  set Fy := Finset.univ.filter (fun y => redTop l n m N y = z) with hFy
  set r : ℕ := l ^ (m + n) * i with hr
  let Ψ : SL(2, ℤ) → Ω := fun g => ∑ a ∈ A, ∑ y ∈ Fy, τ a (repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w g r))
  let Φ : SL(2, ZMod (l ^ (m + n))) → Ω := fun h => (Nat.totient (N * N)) • ∑ a ∈ A,
    kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) (tw h (a * z)) r
  have hΨ : ∀ g ∈ CongruenceSubgroup.Gamma0 N, ((en g 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → ∀ h : SL(2, ZMod (l ^ (m + n))), h 0 0 = (en g 0 0 : ℤ) → h 0 1 = ((N : ℤ) * en g 0 1 : ℤ) → (N : ZMod (l ^ (m + n))) * h 1 0 = (en g 1 0 : ℤ) → h 1 1 = (en g 1 1 : ℤ) → Ψ g = Φ h := by
    intro g hg hga h h00 h01 h10 h11
    show ∑ a ∈ A, ∑ y ∈ Fy, _ = (Nat.totient (N * N)) • ∑ a ∈ A, _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hy : ∀ y ∈ Fy, τ a (repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w g r)) =
        kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) (tw h (a * z)) r := by
      intro y hy
      have hyz : redTop l n m N y = z := (Finset.mem_filter.1 hy).2
      let s : Ω →+* Ω := (τ a).toRingEquiv.toRingHom.comp (repM (Ω := Ω) (topM l n m (N * N)) y).toRingEquiv.toRingHom
      have hs : s (ζ ^ N) = (ζ ^ N) ^ (((a * z : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n))).val) := by
        rw [hζN]
        show τ a (repM (topM l n m (N * N)) y (zt ε l (m + n))) = _
        rw [UpperTheory.repM_apply_zt_eq_pow_redTop ε l n m N y, hyz, map_pow, hτ a, ← pow_mul, Units.val_mul, ZMod.val_mul,
          ← pow_eq_pow_mod _ hzt1]
      exact UpperTheory.gamma0_diamond_action_eq ζ l (m + n) N x c d w a₀ s
        (((a * z : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n)))) hcop hζ1 hs g hg (hga.trans ha₀.symm) (tw h (a * z))
        (by rw [twist_column_zero, h00]) (by rw [twist_column_one, h01]) (by rw [twist_column_zero, h10]) (by rw [twist_column_one, h11]) r
    rw [Finset.sum_congr rfl hy, Finset.sum_const, hFy, UpperTheory.card_fiber_reduction_eq_totient l n m N hcop z]
  have hcount := hμ Φ Ψ hΨ
  have hT : ∀ γ ∈ R, ∀ b : ℕ, (fun γ => ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ)) (γ * Tm (topMu l n m N) b) =
      (fun γ => ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ)) γ := by
    intro γ _ b
    refine Finset.sum_congr rfl fun r₀ _ => ?_
    have hk := UpperTheory.cmul_smF_invariant_of_congruent_mul_T_pow ζ l (m + n) N x c d w (topMu l n m N) (NeZero.pos N) (Fact.out : l.Prime).pos hζ1
      ⟨N, by unfold topMu; ring⟩ b (gm r₀ * liftSL _ γ) (gm r₀ * liftSL _ (γ * Tm (topMu l n m N) b))
      (by simp only [map_mul, GlobalTheory.K4.map_liftSL, Tm, mul_assoc]) i
    show ∑ a ∈ A, ∑ y ∈ Fy, _ = ∑ a ∈ A, ∑ y ∈ Fy, _
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
    exact congrArg (fun t => τ a (repM (topM l n m (N * N)) y t)) hk
  have hG := UpperTheory.sum_levelSubgroupMod_eq_smul_sum_reps N l (topMu l n m N) R hR Ω (fun γ => ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ)) hT
  have htw := UpperTheory.congruence_action_invariant l (m + n) m hm (by omega) z tw twist_column_zero twist_column_one Ω
    (kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) · r)
  rw [← htw]
  have hl : ∑ a ∈ A, τ a (∑ y ∈ Fy, ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
        repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w (gm r₀ * liftSL _ γ) r)) =
      ∑ γ ∈ R, ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ) := by
    simp only [map_sum]
    exact swap4 A Fy Finset.univ R _
  have hΦ : ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h =
      (Nat.totient (N * N)) • ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), ∑ a ∈ A,
        kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) (tw h (a * z)) r := by
    rw [Finset.smul_sum]
  rw [hl, ← nsmul_eq_mul, ← hG, Finset.sum_comm, hcount, hΦ]
  simp only [nsmul_eq_mul]
  ring

end UpperTheory.Kd.L

theorem UpperTheory.Kd.L.arith :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (w : ℕ), 1 ≤ w → ∃ κ : ℚ, κ ≠ 0 ∧ ∃ L₀ : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (m n : ℕ), 1 ≤ m → ∀ R, IsReps N l (topMu l n m N) R → ∀ (z : (ZMod (l ^ (m + n)))ˣ), (∀ r : ℚ, InZl ε l (m + n) (Fsum ε l n m N x c d w gm R z r)) ∧ (L₀ ≤ m + n → ∀ (i : ℕ) (F' : Ω), IsNT ε l (m + n) m (Fsum ε l n m N x c d w gm R z (i : ℚ)) F' → ∀ (β : ℕ) (t a : ℤ), (a : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → β ≡ (z : ZMod (l ^ (m + n))).val [MOD l ^ m] → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∃ E : Ω, InZl ε l m E ∧ F' = (κ : Ω) * (l : Ω) ^ m * toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a * t, 0) (a * t, 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i + (l : Ω) ^ n * E) := by
  intro l _ N _ w hw
  obtain ⟨μ, hμ0, hμ⟩ := UpperTheory.Kd.L.count l N
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hNN : 0 < N * N := Nat.mul_pos (NeZero.pos N) (NeZero.pos N)
  refine ⟨-((N : ℚ) * (Nat.totient (N * N) : ℚ) * (μ : ℚ)), neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hN0
    (Nat.cast_ne_zero.2 (Nat.totient_pos.2 hNN).ne')) (Nat.cast_ne_zero.2 hμ0.ne')), (w + 1) ^ 2 * l, ?_⟩
  intro Ω _ _ _ _ ε c d gm hP x m n hm R hR z
  have hl : l.Prime := Fact.out
  have hNl : N * l ∣ topMu l n m N := by
    have h1 : l ∣ l ^ (m + n) := dvd_pow_self l (by omega)
    obtain ⟨e, he⟩ := h1
    exact ⟨e * N, by unfold topMu; rw [he]; ring⟩
  have hreps := (UpperTheory.Kd.L.reps l N c d gm hP (topMu l n m N) hNl).2
  have hcond : ∀ (r₀ : (ZMod l)ˣ) (γ : SL(2, ZMod (topMu l n m N))), γ ∈ R →
      ¬ (l : ℤ) ∣ en (gm r₀ * liftSL _ γ) 0 0 ∧ ¬ (l : ℤ) ∣ en (gm r₀ * liftSL _ γ) 1 0 :=
    fun r₀ γ hγ => (hreps γ (hR.1 hγ) r₀).2.2.2
  obtain ⟨inat, iadd, imul, igal⟩ := UpperTheory.inZl_closed_add_mul_and_cyclotomic_galois_stable ε l (m + n)
  have hi0 : InZl ε l (m + n) (0 : Ω) := by simpa using inat 0
  have isum : ∀ {α : Type} (s : Finset α) (f : α → Ω), (∀ a ∈ s, InZl ε l (m + n) (f a)) →
      InZl ε l (m + n) (∑ a ∈ s, f a) := fun s f h => Finset.sum_induction f _ iadd hi0 h
  have irep : ∀ (y : (ZMod (topM l n m (N * N)))ˣ) (F : Ω), InZl ε l (m + n) F →
      InZl ε l (m + n) (repM (topM l n m (N * N)) y F) := fun y F h => igal _ _ (UpperTheory.repM_apply_zt_eq_pow_redTop ε l n m N y) F h
  have iN3 : InZl ε l (m + n) ((N : Ω) ^ 3) := by have h := inat (N ^ 3); rwa [Nat.cast_pow] at h
  have hEE : ∀ (r₀ : (ZMod l)ˣ) (γ : SL(2, ZMod (topMu l n m N))), γ ∈ R → ∀ r : ℚ, r.den = 1 →
      InZl ε l (m + n) (EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) r) := by
    intro r₀ γ hγ r hden
    rcases lt_or_ge r 0 with hr | hr
    · have h0 : EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) r = 0 := by
        simp [EE, coefQ, not_le.2 hr]
      rw [h0]; exact hi0
    · have h1 : (r.num : ℚ) = r := Rat.coe_int_num_of_den_eq_one hden
      have h2 : 0 ≤ r.num := Rat.num_nonneg.2 hr
      have h3 : r = ((r.num.toNat : ℕ) : ℚ) := by
        calc r = (r.num : ℚ) := h1.symm
          _ = ((r.num.toNat : ℤ) : ℚ) := by rw [Int.toNat_of_nonneg h2]
          _ = _ := by push_cast; rfl
      rw [h3]
      exact (UpperTheory.Kd.L.inzl ε l N c d gm hP x (m + n) n w hw (by omega) _ (hcond r₀ γ hγ).1 (hcond r₀ γ hγ).2 _).1
  constructor
  · intro r
    unfold Fsum
    split_ifs with hden
    · exact imul _ _ iN3 (isum _ _ fun y _ => isum _ _ fun r₀ _ => isum _ _ fun γ hγ =>
        imul _ _ (inat _) (irep y _ (hEE r₀ γ hγ r hden)))
    · exact hi0
  intro hL i F' hNT β t a₀ ha₀ hβ hβN ht
  have hlarge : (w + 1) ^ 2 * l ≤ l ^ (m + n) := hL.trans (Nat.lt_pow_self hl.one_lt).le
  have hex : ∀ (r₀ : (ZMod l)ˣ) (γ : SL(2, ZMod (topMu l n m N))), γ ∈ R → ∃ E : Ω, InZl ε l (m + n) E ∧
      (ex l n w (gm r₀ * liftSL _ γ) : Ω) * EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) (i : ℚ) =
        (l : Ω) ^ ((m + n) * w) * kz (eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ))) l (m + n) N x c d w (gm r₀ * liftSL _ γ) (l ^ (m + n) * i) +
          (l : Ω) ^ n * E :=
    fun r₀ γ hγ => (UpperTheory.Kd.L.inzl ε l N c d gm hP x (m + n) n w hw (by omega) _ (hcond r₀ γ hγ).1 (hcond r₀ γ hγ).2 i).2 hlarge
  choose! E hE using hex
  set ζ : Ω := eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) with hζdef
  set S1 : Ω := ∑ y ∈ Finset.univ.filter (fun y => redTop l n m N y = z), ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
    repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w (gm r₀ * liftSL _ γ) (l ^ (m + n) * i)) with hS1
  set S2 : Ω := ∑ y ∈ Finset.univ.filter (fun y => redTop l n m N y = z), ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
    repM (topM l n m (N * N)) y (E r₀ γ) with hS2
  have hF : Fsum ε l n m N x c d w gm R z (i : ℚ) = (N : Ω) ^ 3 * ((l : Ω) ^ ((m + n) * w) * S1 + (l : Ω) ^ n * S2) := by
    unfold Fsum
    rw [if_pos (by simp)]
    congr 1
    simp only [hS1, hS2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun r₀ _ => Finset.sum_congr rfl fun γ hγ => ?_
    have h1 := (hE r₀ γ hγ).2
    calc (ex l n w (gm r₀ * liftSL _ γ) : Ω) * repM (topM l n m (N * N)) y (EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) (i : ℚ))
        = repM (topM l n m (N * N)) y ((ex l n w (gm r₀ * liftSL _ γ) : Ω) * EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) (i : ℚ)) := by
          rw [map_mul, map_natCast]
      _ = _ := by rw [h1, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast]
  have hS2Z : InZl ε l (m + n) S2 := isum _ _ fun y _ => isum _ _ fun r₀ _ => isum _ _ fun γ hγ => irep y _ (hE r₀ γ hγ).1
  have hE0 : InZl ε l (m + n) ((N : Ω) ^ 3 * S2) := imul _ _ iN3 hS2Z
  obtain ⟨E', hNT', hE'Z, -⟩ := GlobalTheory.T.exists_unique_normalizedCyclotomicTrace ε l (m + n) m hm (by omega) _ hE0
  obtain ⟨τ, hτ, hsum⟩ := hNT
  obtain ⟨τ', hτ', hsum'⟩ := hNT'
  rw [Nat.add_sub_cancel_left] at hsum hsum'
  have hkey := sum_key ε l N c d w gm hP x a₀ ha₀ m n hm R hR z τ hτ μ (fun Φ Ψ h => hμ c d gm hP n m hm Ω Φ Ψ h) i
  have hterm : ∀ a, τ a ((N : Ω) ^ 3 * ((l : Ω) ^ ((m + n) * w) * S1 + (l : Ω) ^ n * S2)) =
      (N : Ω) ^ 3 * (l : Ω) ^ ((m + n) * w) * τ a S1 + (l : Ω) ^ n * τ' a ((N : Ω) ^ 3 * S2) := by
    intro a
    rw [← IsNTr.apply_eq_of_mem_adjoin hE0.mem_adjoin ((hτ a).trans (hτ' a).symm)]
    simp only [map_mul, map_add, map_pow, map_natCast]
    ring
  have hB : (l : Ω) ^ (m + n) = (l : Ω) ^ n * (l : Ω) ^ m := by rw [add_comm, pow_add]
  have hln : (l : Ω) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.ne_zero)
  have hprim := (UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible ε l N).1 (m + n)
  have hzm := (UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible ε l N).2.2 m n
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  set T : Ω := ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]), τ a S1 with hT
  have key4 : (l : Ω) ^ n * F' = (N : Ω) ^ 3 * (l : Ω) ^ ((m + n) * w) * T + (l : Ω) ^ n * ((l : Ω) ^ n * E') := by
    have h1 : ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
        τ a ((N : Ω) ^ 3 * ((l : Ω) ^ ((m + n) * w) * S1 + (l : Ω) ^ n * S2)) =
        (N : Ω) ^ 3 * (l : Ω) ^ ((m + n) * w) * T + (l : Ω) ^ n * ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]), τ' a ((N : Ω) ^ 3 * S2) := by
      rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsum, hF, h1, ← hsum']
  set z₀ : ZMod (l ^ m) := (((z : ZMod (l ^ (m + n))).val : ℕ) : ZMod (l ^ m)) with hz₀
  have hcp : Nat.Coprime (l ^ (m + n)) N := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hP.cop)
  have htop : (l : ℤ) ^ n * (topT l (m + n) N : ℤ) ≡ t [ZMOD N] := by
    have h1 : (l : ZMod N) ^ (m + n) * (topT l (m + n) N : ZMod N) = 1 := by
      unfold topT
      rw [ZMod.natCast_zmod_val]
      have h := ZMod.coe_mul_inv_eq_one (l ^ (m + n)) hcp
      simpa using h
    have h2 : (l : ZMod N) ^ m * (t : ZMod N) = 1 := by
      have h := (ZMod.intCast_eq_intCast_iff _ _ N).2 ht
      push_cast at h
      exact h
    apply (ZMod.intCast_eq_intCast_iff _ _ N).1
    push_cast
    rw [pow_add] at h1
    linear_combination (-((l : ZMod N) ^ n * (topT l (m + n) N : ZMod N))) * h2 + (t : ZMod N) * h1
  have e1 : (l : ℤ) ^ n * ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ)) ≡ (x.val : ℤ) * a₀ * t [ZMOD N] := by
    have h := htop.mul_left ((x.val : ℤ) * a₀)
    rwa [show (x.val : ℤ) * a₀ * ((l : ℤ) ^ n * (topT l (m + n) N : ℤ)) = (l : ℤ) ^ n * ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ)) by ring] at h
  have e3 : (l : ℤ) ^ n * (a₀ * (topT l (m + n) N : ℤ)) ≡ a₀ * t [ZMOD N] := by
    have h := htop.mul_left a₀
    rwa [show a₀ * ((l : ℤ) ^ n * (topT l (m + n) N : ℤ)) = (l : ℤ) ^ n * (a₀ * (topT l (m + n) N : ℤ)) by ring] at h
  have e0 : (l : ℤ) ^ n * (0 : ℤ) ≡ 0 [ZMOD N] := by rw [mul_zero]
  have hnd : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → ¬ (l : ℤ) ∣ (e : ℤ) := by
    intro e he h
    have h' : l ∣ e := Int.natCast_dvd_natCast.1 h
    have h2 : l ∣ Nat.gcd e (6 * l * N) := Nat.dvd_gcd h' ⟨6 * N, by ring⟩
    rw [he.gcd_eq_one] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.1 h2)
  have down := UpperTheory.pieceT_level_raise_eq_vp l N m (w + 2) (c : ℤ) (d : ℤ) z₀ (NeZero.pos N) hP.cop hm (by omega) (hnd c hP.cc) (hnd d hP.dc) n ζ
    ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ((x.val : ℤ) * a₀ * t, 0) (a₀ * t, 0)
    hprim e1 e0 e3 e0 (l ^ (m + n) * i)
  have hzm' : ζ ^ (l ^ n) = eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) := hzm
  have hζm1 : (ζ ^ (l ^ n)) ^ (N * l ^ m) = 1 := by
    rw [← pow_mul, show l ^ n * (N * l ^ m) = N * l ^ (m + n) by rw [pow_add]; ring]
    exact hprim.pow_eq_one
  have hunit : IsUnit z₀ := by
    have hd : l ^ m ∣ l ^ (m + n) := pow_dvd_pow l (by omega)
    have h := z.isUnit.map (ZMod.castHom hd (ZMod (l ^ m)))
    rwa [ZMod.castHom_apply, ← ZMod.natCast_val] at h
  have hβ' : (β : ZMod (l ^ m)) = z₀ := (ZMod.natCast_eq_natCast_iff _ _ _).2 hβ
  have beta := UpperTheory.pieceT_det_fiber_eq_pieceT_root_pow l N m (w + 2) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * t) (a₀ * t) (ζ ^ (l ^ n)) β z₀ (NeZero.pos N) hm hζm1 hunit hβ' (l ^ m * i)
  have hvp : ∀ f : ℕ → Ω, vp (l ^ n) f (l ^ (m + n) * i) = f (l ^ m * i) := by
    intro f
    have hdiv : l ^ (m + n) * i = l ^ n * (l ^ m * i) := by rw [pow_add]; ring
    rw [hdiv]
    unfold vp
    rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (pow_pos hl.pos n)]
  rw [hvp] at down
  set Ks : Ω := ∑ γ ∈ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀),
    kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) γ (l ^ (m + n) * i) with hKs
  have key2 : pieceT N l (m + n) m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) (l ^ (m + n) * i) =
      -((l : Ω) ^ (((m + n : ℕ) : ℤ) * ((w : ℤ) - 2))) * Ks :=
    UpperTheory.twistedEisensteinPiece_trivialCharacter_eq l N (m + n) m w (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ z₀ hm (by omega) (l ^ (m + n) * i)
  have hk' : ((topMu l n m N : ℕ) : Ω) * T = (μ : Ω) * (Nat.totient (N * N) : Ω) * Ks := hkey
  have key1 : (l : Ω) ^ (m + n) * (N : Ω) ^ 2 * T = (μ : Ω) * (Nat.totient (N * N) : Ω) * Ks := by
    rw [← hk']; unfold topMu; push_cast; ring
  have key3 : (l : Ω) ^ (((m + n : ℕ) : ℤ) * ((w : ℤ) - 2)) * ((l : Ω) ^ (m + n)) ^ 2 = (l : Ω) ^ ((m + n) * w) := by
    rw [← pow_mul, ← zpow_natCast (l : Ω) ((m + n) * 2), ← zpow_add₀ hl0, ← zpow_natCast (l : Ω) ((m + n) * w)]
    congr 1
    push_cast
    ring
  refine ⟨E', hE'Z, ?_⟩
  have hQ : toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * t, 0) (a₀ * t, 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i =
      pieceT N l (m + n) m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) (l ^ (m + n) * i) := by
    rw [down, beta, hzm']
    rfl
  rw [hQ]
  apply mul_left_cancel₀ hln
  push_cast
  linear_combination key4 - (N : Ω) * (Nat.totient (N * N) : Ω) * (μ : Ω) * (pieceT N l (m + n) m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) (l ^ (m + n) * i)) * hB +
    (N : Ω) * (Nat.totient (N * N) : Ω) * (μ : Ω) * (l : Ω) ^ (m + n) * key2 - (N : Ω) ^ 3 * T * key3 +
    (N : Ω) * (l : Ω) ^ (((m + n : ℕ) : ℤ) * ((w : ℤ) - 2)) * (l : Ω) ^ (m + n) * key1
end
end
