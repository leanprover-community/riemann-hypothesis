import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPolyOfDiffs
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPrimeFiltration
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegreeBound
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRelevantPrimeDimGe
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumAdd
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBase
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRational
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPrincipalDegree
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PExistsForm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleSupport
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumUnique
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbAddBlock
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsAddBlock
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameMultiHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameHilbFn
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameIntNum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameMultiProjPrime
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSplitRelDeg

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace HilbEventuallyPoly

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_iff_isHomogeneous (I : Ideal (MRing ι F)) :
    IsMultiHomogIdeal I ↔ I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := by
  constructor
  · intro h b f hf
    have key : (DirectSum.decompose (weightedHomogeneousSubmodule F (blockWeight ι)) f b :
        MRing ι F) = weightedHomogeneousComponent (blockWeight ι) b f :=
      weightedDecomposition.decompose'_apply F (blockWeight ι) f b
    rw [key]
    exact h f hf b
  · intro h f hf b
    exact weightedHomogeneousComponent_mem_of_mem F (blockWeight ι) h hf b

omit [Fintype K] in

theorem isMultiHomog_X (v : Σ k, ι k) :
    IsMultiHomog (X v : MRing ι F) (Pi.single v.1 1) :=
  isWeightedHomogeneous_X F (blockWeight ι) v

theorem weightedHomogeneousComponent_mul_X (f : MRing ι F) (b : K → ℕ) (v : Σ k, ι k) :
    weightedHomogeneousComponent (blockWeight ι) (b + blockWeight ι v) (f * X v) =
      weightedHomogeneousComponent (blockWeight ι) b f * X v := by
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule F (blockWeight ι)) (a := f) (i := b)
    (isWeightedHomogeneous_X F (blockWeight ι) v)
  have key : ∀ (φ : MRing ι F) (c : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule F (blockWeight ι)) φ c : MRing ι F) =
        weightedHomogeneousComponent (blockWeight ι) c φ :=
    fun φ c => weightedDecomposition.decompose'_apply F (blockWeight ι) φ c
  rw [key, key] at h
  exact h

theorem isMultiHomogIdeal_colon_X {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    (v : Σ k, ι k) : IsMultiHomogIdeal (I.colon (Ideal.span {(X v : MRing ι F)})) := by
  intro f hf b
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul] at hf ⊢
  rw [← weightedHomogeneousComponent_mul_X]
  exact hI _ hf _

theorem isMultiHomogIdeal_sup_span {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  rw [isMultiHomogIdeal_iff_isHomogeneous] at hI ⊢
  refine hI.sup (Ideal.homogeneous_span _ _ ?_)
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨c, hs⟩

theorem hilbFn_eq_zero_of_block {I : Ideal (MRing ι F)} (k : K)
    (hk : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ I) (m : K → ℤ) (hm : 1 ≤ m k) : hilbFn I m = 0 := by
  unfold hilbFn
  split_ifs with h
  · have hbot : gradedPiece I (fun k => (m k).toNat) = ⊥ := by
      rw [gradedPiece, eq_bot_iff, Submodule.map_le_iff_le_comap]
      intro f hf
      rw [Submodule.mem_comap, Submodule.mem_bot, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      rw [mem_weightedHomogeneousSubmodule] at hf
      rw [f.as_sum]
      refine Ideal.sum_mem _ fun d hd => ?_
      have hw := hf (mem_support_iff.mp hd)
      obtain ⟨i, hi⟩ : ∃ i, d ⟨k, i⟩ ≠ 0 := by
        by_contra hcon
        simp only [not_exists, ne_eq, not_not] at hcon
        have h0 : Finsupp.weight (blockWeight ι) d k = 0 := by
          rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
          refine Finset.sum_eq_zero fun v _ => ?_
          obtain ⟨k', i'⟩ := v
          simp only [blockWeight, Pi.smul_apply, smul_eq_mul]
          by_cases hkk : k' = k
          · subst hkk
            simp [hcon i']
          · simp [Ne.symm hkk]
        rw [hw] at h0
        simp only at h0
        omega
      have hmono : monomial d (coeff d f) =
          X ⟨k, i⟩ * monomial (d - Finsupp.single ⟨k, i⟩ 1) (coeff d f) := by
        rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le]
        rw [Finsupp.single_le_iff]
        omega
      rw [hmono]
      exact Ideal.mul_mem_right _ _ (hk i)
    rw [hbot, finrank_bot]
    simp
  · rfl

omit [Fintype K] [DecidableEq K] in

theorem eventually_sub {P : (K → ℤ) → Prop} (h : ∀ᶠ m in Filter.atTop, P m) (e : K → ℤ) :
    ∀ᶠ m in Filter.atTop, P (m - e) := by
  rw [Filter.eventually_atTop] at h ⊢
  obtain ⟨a, ha⟩ := h
  refine ⟨a + e, fun b hb => ha _ fun k => ?_⟩
  have := hb k
  simp only [Pi.add_apply] at this
  simp only [Pi.sub_apply]
  linarith

omit [Fintype K] [DecidableEq K] in

theorem eval_shift (p : MvPolynomial K ℚ) (e m : K → ℤ) :
    eval (fun k => ((m - e) k : ℚ)) p =
      eval (fun k => (m k : ℚ)) (bind₁ (fun j => X j - C ((e j : ℤ) : ℚ)) p) := by
  have hb : ∀ (x : K → ℚ) (g : K → MvPolynomial K ℚ),
      eval x (bind₁ g p) = eval (fun j => eval x (g j)) p :=
    fun x g => eval₂Hom_bind₁ _ _ _ _
  rw [hb]
  refine congrArg (fun x => eval x p) (funext fun j => ?_)
  simp

omit [Fintype K] in

theorem cast_single (k : K) :
    (fun k' => (((Pi.single k 1 : K → ℕ) k' : ℕ) : ℤ)) = Pi.single k 1 := by
  funext k'
  by_cases h : k' = k
  · subst h; simp
  · simp [h]

end Lemmas

end HilbEventuallyPoly

theorem HilbEventuallyPoly.of_exactDivide_polyOfDiffs (h1 : HilbExactDivide.Statement.{u})
    (h2 : PolyOfDiffs.Statement) : HilbEventuallyPoly.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  refine IsNoetherian.induction
    (P := fun J : Ideal (MRing ι F) => IsMultiHomogIdeal J → ∃ p, EventuallyPoly (hilbFn J) p)
    (fun J ih hJ => ?_) I hI
  by_cases hA : ∃ v : Σ k, ι k, (X v : MRing ι F) ∉ J ∧
      J.colon (Ideal.span {(X v : MRing ι F)}) ≠ J
  ·
    obtain ⟨v, hvJ, hne⟩ := hA
    have hle : J ≤ J.colon (Ideal.span {(X v : MRing ι F)}) := fun f hf => by
      rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
      exact Ideal.mul_mem_right _ J hf
    have hlt2 : J < J ⊔ Ideal.span {(X v : MRing ι F)} :=
      lt_of_le_of_ne le_sup_left fun h =>
        hvJ (h ▸ Ideal.mem_sup_right (Ideal.subset_span rfl))
    obtain ⟨p1, hp1⟩ := ih _ (lt_of_le_of_ne hle (Ne.symm hne)) (isMultiHomogIdeal_colon_X hJ v)
    obtain ⟨p2, hp2⟩ := ih _ hlt2 (isMultiHomogIdeal_sup_span hJ (isMultiHomog_X v))
    have hex := h1 F K ι J hJ _ (X v) (isMultiHomog_X v)
    rw [cast_single] at hex
    refine ⟨bind₁ (fun j => X j - C (((Pi.single v.1 1 : K → ℤ) j : ℤ) : ℚ)) p1 + p2, ?_⟩
    filter_upwards [eventually_sub hp1 (Pi.single v.1 1), hp2] with m hm1 hm2
    have hz := hex m
    rw [map_add, ← eval_shift, ← hm1, ← hm2]
    have hz' : hilbFn J m = hilbFn (J.colon (Ideal.span {(X v : MRing ι F)})) (m - Pi.single v.1 1)
        + hilbFn (J ⊔ Ideal.span {(X v : MRing ι F)}) m := by linarith
    rw [hz']
    push_cast
    rfl
  ·
    have hA' : ∀ v : Σ k, ι k, (X v : MRing ι F) ∉ J →
        J.colon (Ideal.span {(X v : MRing ι F)}) = J := fun v hv => by
      by_contra hne
      exact hA ⟨v, hv, hne⟩
    have hdiff : ∀ k, ∃ q : MvPolynomial K ℚ,
        EventuallyPoly (diffStep (Pi.single k 1) (hilbFn J)) q := by
      intro k
      by_cases hk : ∃ i, (X ⟨k, i⟩ : MRing ι F) ∉ J
      · obtain ⟨i, hi⟩ := hk
        have hlt : J < J ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)} :=
          lt_of_le_of_ne le_sup_left fun h =>
            hi (h ▸ Ideal.mem_sup_right (Ideal.subset_span rfl))
        obtain ⟨q, hq⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ (isMultiHomog_X ⟨k, i⟩))
        refine ⟨q, ?_⟩
        have hex := h1 F K ι J hJ _ (X ⟨k, i⟩) (isMultiHomog_X ⟨k, i⟩)
        rw [cast_single, hA' _ hi] at hex
        filter_upwards [hq] with m hm
        rw [← hm]
        unfold diffStep
        rw [hex m]
      · simp only [not_exists, not_not] at hk
        refine ⟨0, ?_⟩
        rw [EventuallyPoly, Filter.eventually_atTop]
        refine ⟨Pi.single k 2, fun m hm => ?_⟩
        have hmk : 2 ≤ m k := by simpa using hm k
        unfold diffStep
        rw [hilbFn_eq_zero_of_block k hk m (by omega),
          hilbFn_eq_zero_of_block k hk _ (by simp only [Pi.sub_apply, Pi.single_eq_same]; omega)]
        simp
    choose q hq using hdiff
    obtain ⟨p, -, hp⟩ := h2 K (hilbFn J) (Finset.univ.sup fun k => (q k).totalDegree + 1)
      fun k => ⟨q k, Or.inr (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Finset.le_sup (f := fun k => (q k).totalDegree + 1) (Finset.mem_univ k))), hq k⟩
    exact ⟨p, hp⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

theorem EventuallyPolyUnique.proof : EventuallyPolyUnique.Statement := by
  intro K _ h p q hp hq
  classical
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (hp.and hq)
  have hpq : p - q = 0 := by
    apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset (p - q)
      (fun k => (Finset.range ((p - q).degreeOf k + 1)).image
        (fun i : ℕ => ((M k + (i : ℤ) : ℤ) : ℚ)))
    · intro k
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b hab
        simpa using hab
    · intro x hx
      choose i _ hix using fun k => Finset.mem_image.1 (hx k)
      have hm : M ≤ fun k => M k + (i k : ℤ) := fun k => by simp
      have hxm : x = fun k => (((M k + (i k : ℤ) : ℤ)) : ℚ) := funext fun k => (hix k).symm
      obtain ⟨h1, h2⟩ := hM _ hm
      rw [map_sub, hxm, ← h1, ← h2, sub_self]
  exact sub_eq_zero.1 hpq

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial Filter

noncomputable section

theorem totalDegree_bind₁_le_of_le_one {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hf i)

theorem EventuallyPolyShift.proof : EventuallyPolyShift.Statement := by
  intro K _ h p c hp
  refine ⟨bind₁ (fun k => X k - C (c k : ℚ)) p, ?_, ?_, ?_⟩
  · have ht : Tendsto (fun m : K → ℤ => m + -c) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-c) tendsto_id
    refine (ht.eventually hp).mono fun m hm => ?_
    simp only [← sub_eq_add_neg] at hm
    have e := eval₂Hom_bind₁ (RingHom.id ℚ) (fun k => (m k : ℚ)) (fun k => X k - C (c k : ℚ)) p
    rw [hm]
    refine Eq.trans ?_ e.symm
    show eval _ p = eval _ p
    refine congrArg (fun x => eval x p) (funext fun k => ?_)
    simp
  · exact totalDegree_bind₁_le_of_le_one _
      (fun k => (totalDegree_sub_C_le _ _).trans (totalDegree_X k).le) p
  · rintro rfl
    exact map_zero _

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem mem_of_isMultiHomog_of_block_le {I : Ideal (MRing ι F)} {k : K}
    (hk : ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ I) {b : K → ℕ} (hb : 1 ≤ b k)
    {f : MRing ι F} (hf : IsWeightedHomogeneous (blockWeight ι) f b) : f ∈ I := by
  rw [f.as_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hw := hf (mem_support_iff.mp hd)
  rw [GroundTheory.Heights₂.Heights.Bridge.weight_blockWeight] at hw
  have hsum : ∑ i, d ⟨k, i⟩ ≠ 0 := by
    have := congrFun hw k
    omega
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hle : Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1 ≤ d := by
    rw [Finsupp.single_le_iff]
    omega
  rw [← tsub_add_cancel_of_le hle, monomial_add_single, pow_one]
  exact Ideal.mul_mem_left _ _ (hk i)

theorem gradedPiece_eq_bot_of_not_isRelevant {I : Ideal (MRing ι F)} (hI : ¬ IsRelevant I)
    {m : K → ℕ} (hm : ∀ k, 1 ≤ m k) : gradedPiece I m = ⊥ := by
  obtain ⟨k, hk⟩ : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ I := by
    by_contra h
    exact hI fun k => by
      by_contra h'
      exact h ⟨k, fun i => by
        by_contra h''
        exact h' ⟨i, h''⟩⟩
  rw [eq_bot_iff]
  rintro _ ⟨f, hf, rfl⟩
  rw [Submodule.mem_bot]
  have : f ∈ I := mem_of_isMultiHomog_of_block_le hk (hm k)
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)
  simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr this

end

theorem HilbIrrelevantZero.proof : HilbIrrelevantZero.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  filter_upwards [Filter.eventually_ge_atTop (1 : K → ℤ)] with m hm
  have hpos : ∀ k, 0 ≤ m k := fun k => le_trans zero_le_one (hm k)
  unfold hilbFn
  rw [if_pos hpos, gradedPiece_eq_bot_of_not_isRelevant hI (m := fun k => (m k).toNat)]
  · simp
  · intro k
    have := hm k
    simp only [Pi.one_apply] at this
    omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous_of_isMultiHomogIdeal {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := by
  classical
  have e : I = Ideal.span
      {g | ∃ f ∈ I, ∃ b, g = weightedHomogeneousComponent (blockWeight ι) b f} := by
    apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact hI f hf b
  rw [e]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  obtain ⟨f, -, b, rfl⟩ := hx
  exact ⟨b, weightedHomogeneousComponent_isWeightedHomogeneous b f⟩

theorem isMultiHomogIdeal_sup_span {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  classical
  have h2 : (Ideal.span {s}).IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ fun x hx => ⟨c, (Set.mem_singleton_iff.mp hx) ▸ hs⟩
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem
    (h := (isHomogeneous_of_isMultiHomogIdeal hI).sup h2) (hp := hf) (m := b)

omit [Fintype K] [DecidableEq K] in

theorem colon_span_eq_of_isPrime {P : Ideal (MRing ι F)} (hP : P.IsPrime) {s : MRing ι F}
    (hs : s ∉ P) : P.colon (Ideal.span {s}) = P := by
  ext x
  rw [Ideal.mem_colon_span_singleton]
  exact ⟨fun h => (hP.mem_or_mem h).resolve_right hs, fun h => P.mul_mem_right s h⟩

omit [Fintype K] [DecidableEq K] in

theorem ringKrullDim_sup_span_add_one_le {P : Ideal (MRing ι F)} [P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) :
    ringKrullDim (MRing ι F ⧸ (P ⊔ Ideal.span {s})) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor le_sup_left)
    (Ideal.Quotient.factor_surjective le_sup_left) (r := Ideal.Quotient.mk P s) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)

theorem lt_of_add_one_le_natCast {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ n) : x < n := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.natCast_lt_top n))
    | coe a =>
      have : a + 1 ≤ n := by exact_mod_cast h
      exact_mod_cast (show a < n by omega)

end Lemmas

theorem totalDegree_add_card_le_ringKrullDim (h1 : HilbEventuallyPoly.Statement.{u})
    (h2 : HilbExactDivide.Statement.{u}) (h3 : PolyOfDiffs.Statement)
    (h4 : PrimeFiltration.Statement.{u}) (hU : EventuallyPolyUnique.Statement)
    (hS : EventuallyPolyShift.Statement) (hZ : HilbIrrelevantZero.Statement.{u})
    (hD : RelevantPrimeDimGe.Statement.{u})
    (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) :
    ∀ I : Ideal (MRing ι F), IsMultiHomogIdeal I → ringKrullDim (MRing ι F ⧸ I) < n →
      ∀ p : MvPolynomial K ℚ, EventuallyPoly (hilbFn I) p → p ≠ 0 →
      ((p.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ I) := by
  induction n with
  | zero =>
    intro I _ hlt p hp hp0
    exfalso
    have hsub : Subsingleton (MRing ι F ⧸ I) := by
      by_contra hn
      rw [not_subsingleton_iff_nontrivial] at hn
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MRing ι F ⧸ I)
      exact absurd hlt (not_lt.mpr (by simpa using h0))
    have hz : ∀ m, hilbFn I m = 0 := by
      intro m
      unfold hilbFn
      split_ifs
      · rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
      · rfl
    have : EventuallyPoly (hilbFn I) 0 := Filter.Eventually.of_forall fun m => by simp [hz]
    exact hp0 (hU K _ p 0 hp this)
  | succ n ih =>
    have prime : ∀ P : Ideal (MRing ι F), P.IsPrime → IsMultiHomogIdeal P →
        ringKrullDim (MRing ι F ⧸ P) < (n + 1 : ℕ) → ∀ p : MvPolynomial K ℚ,
        EventuallyPoly (hilbFn P) p → p ≠ 0 →
        ((p.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ P) := by
      intro P hPp hPh hlt p hp hp0
      by_cases hrel : IsRelevant P
      swap
      · exfalso
        have : EventuallyPoly (hilbFn P) 0 := (hZ F K ι P hrel).mono fun m hm => by simp [hm]
        exact hp0 (hU K _ p 0 hp this)
      have hge := hD F K ι P ⟨hPp, hPh, hrel⟩
      choose i hi using hrel
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ringKrullDim (MRing ι F ⧸ P) = N := by
        generalize ringKrullDim (MRing ι F ⧸ P) = x at hge hlt
        induction x using WithBot.recBotCoe with
        | bot => exact absurd hge (not_le.mpr (WithBot.bot_lt_coe _))
        | coe a =>
          induction a using ENat.recTopCoe with
          | top => exact absurd hlt (by simp)
          | coe a => exact ⟨a, rfl⟩
      have hKN : Fintype.card K ≤ N := by rw [hN] at hge; exact_mod_cast hge
      have hdiff : ∀ k, ∃ q : MvPolynomial K ℚ, (q = 0 ∨ q.totalDegree < N - Fintype.card K) ∧
          EventuallyPoly (diffStep (Pi.single k 1) (hilbFn P)) q := by
        intro k
        have hs : IsMultiHomog (X ⟨k, i k⟩ : MRing ι F) (Pi.single k 1) :=
          isWeightedHomogeneous_X _ _ _
        have hJ := isMultiHomogIdeal_sup_span hPh hs
        obtain ⟨q, hq⟩ := h1 F K ι _ hJ
        refine ⟨q, ?_, ?_⟩
        · by_cases hq0 : q = 0
          · exact Or.inl hq0
          right
          have hdrop := ringKrullDim_sup_span_add_one_le (P := P) (hi k)
          rw [hN] at hdrop
          have hNn : N ≤ n := by
            rw [hN] at hlt
            have : N < n + 1 := by exact_mod_cast hlt
            omega
          have hltJ := lt_of_add_one_le_natCast (hdrop.trans (by exact_mod_cast hNn))
          have hb := ih _ hJ hltJ q hq hq0
          have h' : ((q.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ N := by
            refine le_trans ?_ hdrop
            gcongr
          have h'' : q.totalDegree + Fintype.card K + 1 ≤ N := by exact_mod_cast h'
          omega
        · refine hq.mono fun m hm => ?_
          have e := h2 F K ι P hPh (Pi.single k 1) _ hs m
          rw [colon_span_eq_of_isPrime hPp (hi k)] at e
          have ec : (fun k' => ((Pi.single k 1 : K → ℕ) k' : ℤ)) = (Pi.single k 1 : K → ℤ) := by
            funext k'
            by_cases h : k' = k <;> simp [h]
          rw [ec] at e
          simp only [diffStep]
          rw [e]
          exact hm
      obtain ⟨p', hp'deg, hp'⟩ := h3 K (hilbFn P) (N - Fintype.card K) hdiff
      have hpp' := hU K _ p p' hp hp'
      subst hpp'
      rw [hN]
      exact_mod_cast (show p.totalDegree + Fintype.card K ≤ N by omega)
    intro I hI hlt p hp hp0
    obtain ⟨r, Q, c, hQ, hsum, -, -⟩ := h4 F K ι I hI
    choose pj hpj using fun j => h1 F K ι (Q j) (hQ j).2.1
    choose q hq hqdeg hq0 using fun j => hS K _ (pj j) (fun k => (c j k : ℤ)) (hpj j)
    have hsumP : EventuallyPoly (hilbFn I) (∑ j, q j) := by
      have hall : ∀ᶠ m in Filter.atTop, ∀ j, (hilbFn (Q j) (m - fun k => (c j k : ℤ)) : ℚ) =
          eval (fun k => (m k : ℚ)) (q j) := Filter.eventually_all.mpr hq
      filter_upwards [hall, hsum] with m hm hm'
      rw [hm', map_sum]
      push_cast
      exact Finset.sum_congr rfl fun j _ => hm j
    have hpq := hU K _ p _ hp hsumP
    have hDQ : ∀ j, q j ≠ 0 → (((q j).totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤
        ringKrullDim (MRing ι F ⧸ I) := by
      intro j hj
      have hpj0 : pj j ≠ 0 := fun h => hj (hq0 j h)
      have hle : ringKrullDim (MRing ι F ⧸ Q j) ≤ ringKrullDim (MRing ι F ⧸ I) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor (hQ j).2.2)
          (Ideal.Quotient.factor_surjective _)
      have hb := prime (Q j) (hQ j).1 (hQ j).2.1 (hle.trans_lt hlt) (pj j) (hpj j) hpj0
      refine le_trans ?_ (hb.trans hle)
      have := hqdeg j
      exact_mod_cast (show (q j).totalDegree + Fintype.card K ≤
        (pj j).totalDegree + Fintype.card K by omega)
    classical
    set T := Finset.univ.filter fun j => q j ≠ 0 with hT
    have hpT : p = ∑ j ∈ T, q j := by rw [hpq, hT, Finset.sum_filter_ne_zero]
    have hTne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.sum_empty] at hpT
      exact hp0 hpT
    obtain ⟨j, hjT, hjmax⟩ := Finset.exists_max_image T (fun j => (q j).totalDegree) hTne
    have hdeg : p.totalDegree ≤ (q j).totalDegree := by
      rw [hpT]
      exact totalDegree_finsetSum_le hjmax
    refine le_trans ?_ (hDQ j (Finset.mem_filter.mp hjT).2)
    exact_mod_cast (show p.totalDegree + Fintype.card K ≤ (q j).totalDegree + Fintype.card K by
      omega)

theorem HilbDegreeBound.proof (h1 : HilbEventuallyPoly.Statement.{u})
    (h2 : HilbExactDivide.Statement.{u}) (h3 : PolyOfDiffs.Statement)
    (h4 : PrimeFiltration.Statement.{u}) (hU : EventuallyPolyUnique.Statement)
    (hS : EventuallyPolyShift.Statement) (hZ : HilbIrrelevantZero.Statement.{u})
    (hD : RelevantPrimeDimGe.Statement.{u}) : HilbDegreeBound.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  refine ⟨fun _ p hp hp0 => ?_, fun hrel => hZ F K ι I hrel⟩
  have key := fun n => totalDegree_add_card_le_ringKrullDim h1 h2 h3 h4 hU hS hZ hD F K ι n I hI
  unfold relDim
  generalize hx : ringKrullDim (MRing ι F ⧸ I) = x at key
  induction x using WithBot.recBotCoe with
  | bot =>
    have := key 0 (WithBot.bot_lt_coe _) p hp hp0
    exact absurd this (not_le.mpr (WithBot.bot_lt_coe _))
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.mpr le_top
    | coe N =>
      have := key (N + 1) (by exact_mod_cast Nat.lt_succ_self N) p hp hp0
      have hle : p.totalDegree + Fintype.card K ≤ N := by exact_mod_cast this
      show ((p.totalDegree : ℕ) : WithBot (WithTop ℤ)) ≤
        (((N : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)
      have : (p.totalDegree : ℤ) ≤ (N : ℤ) - Fintype.card K := by omega
      exact_mod_cast this

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

namespace MixedDiffConst

variable {K : Type}

def shiftPoly (b : K → ℤ) (p : MvPolynomial K ℚ) : MvPolynomial K ℚ :=
  aeval (fun k => X k - C ((b k : ℤ) : ℚ)) p

def polyStep (b : K → ℤ) (p : MvPolynomial K ℚ) : MvPolynomial K ℚ :=
  p - shiftPoly b p

theorem eval_shiftPoly (b : K → ℤ) (p : MvPolynomial K ℚ) (x : K → ℚ) :
    eval x (shiftPoly b p) = eval (fun k => x k - b k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [shiftPoly]
  | add p q hp hq => simp only [shiftPoly, map_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p k hp => simp only [shiftPoly, map_mul] at hp ⊢; rw [hp]; simp

theorem monomial_good (b : K → ℤ) (s : K →₀ ℕ) (a : ℚ) :
    (shiftPoly b (monomial s a)).totalDegree ≤ (monomial s a).totalDegree ∧
      (polyStep b (monomial s a) = 0 ∨
        (polyStep b (monomial s a)).totalDegree + 1 ≤ (monomial s a).totalDegree) := by
  refine MvPolynomial.induction_on_monomial (motive := fun q =>
    (shiftPoly b q).totalDegree ≤ q.totalDegree ∧
      (polyStep b q = 0 ∨ (polyStep b q).totalDegree + 1 ≤ q.totalDegree)) ?_ ?_ s a
  · intro a; simp [shiftPoly, polyStep]
  · intro p k hp
    obtain ⟨h1, h2⟩ := hp
    by_cases hp0 : p = 0
    · subst hp0; simp [shiftPoly, polyStep]
    have hdeg : (p * X k).totalDegree = p.totalDegree + 1 := by
      rw [totalDegree_mul_of_isDomain hp0 (X_ne_zero k), totalDegree_X]
    have hXC : (X k - C ((b k : ℤ) : ℚ) : MvPolynomial K ℚ).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le (totalDegree_X k).le (by rw [totalDegree_C]; omega))
    have hsh : shiftPoly b (p * X k) = shiftPoly b p * (X k - C ((b k : ℤ) : ℚ)) := by
      simp [shiftPoly]
    have hst : polyStep b (p * X k) = polyStep b p * X k + C ((b k : ℤ) : ℚ) * shiftPoly b p := by
      rw [polyStep, polyStep, hsh]; ring
    refine ⟨?_, Or.inr ?_⟩
    · rw [hsh, hdeg]
      exact (totalDegree_mul _ _).trans (add_le_add h1 hXC)
    · rw [hst, hdeg, add_le_add_iff_right]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rcases h2 with h2 | h2
        · rw [h2, zero_mul, totalDegree_zero]; exact zero_le
        · exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; exact h2)
      · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact h1)

theorem sum_eq (b : K → ℤ) (p : MvPolynomial K ℚ) :
    shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (coeff v p)) ∧
      polyStep b p = ∑ v ∈ p.support, polyStep b (monomial v (coeff v p)) := by
  have hs : shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (coeff v p)) := by
    conv_lhs => rw [p.as_sum]
    simp only [shiftPoly, map_sum]
  refine ⟨hs, ?_⟩
  simp only [polyStep, Finset.sum_sub_distrib]
  rw [← hs, ← p.as_sum]

theorem monomial_le (p : MvPolynomial K ℚ) {v : K →₀ ℕ} (hv : v ∈ p.support) :
    (monomial v (coeff v p)).totalDegree ≤ p.totalDegree :=
  (totalDegree_monomial_le _ _).trans (le_totalDegree hv)

theorem polyStep_deg (b : K → ℤ) (p : MvPolynomial K ℚ) :
    polyStep b p = 0 ∨ (polyStep b p).totalDegree + 1 ≤ p.totalDegree := by
  by_cases h0 : p.totalDegree = 0
  · left
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0]; simp [polyStep, shiftPoly]
  · right
    have : (polyStep b p).totalDegree ≤ p.totalDegree - 1 := by
      rw [(sum_eq b p).2]
      refine totalDegree_finsetSum_le fun v hv => ?_
      rcases (monomial_good b v (coeff v p)).2 with h | h
      · rw [h, totalDegree_zero]; exact zero_le
      · have := monomial_le p hv; omega
    omega

section Eventual

theorem eventuallyPoly_diffStep (b : K → ℤ) {g : (K → ℤ) → ℤ} {q : MvPolynomial K ℚ}
    (hq : EventuallyPoly g q) : EventuallyPoly (diffStep b g) (polyStep b q) := by
  have ht : Tendsto (fun m : K → ℤ => m - b) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-b) tendsto_id
  filter_upwards [hq, ht.eventually hq] with m h1 h2
  simp only [diffStep, polyStep, map_sub, eval_shiftPoly]
  rw [Int.cast_sub, h1, h2]
  simp [Pi.sub_apply]

theorem eventuallyPoly_foldr (L : List (K → ℤ)) {h : (K → ℤ) → ℤ} {p : MvPolynomial K ℚ}
    (hp : EventuallyPoly h p) : EventuallyPoly (L.foldr diffStep h) (L.foldr polyStep p) := by
  induction L with
  | nil => simpa using hp
  | cons b L ih => simpa using eventuallyPoly_diffStep b ih

theorem foldr_polyStep_deg (L : List (K → ℤ)) (p : MvPolynomial K ℚ) :
    L.foldr polyStep p = 0 ∨ (L.foldr polyStep p).totalDegree + L.length ≤ p.totalDegree := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.foldr_cons, List.length_cons]
    rcases ih with h0 | hd
    · left; rw [h0]; simp [polyStep, shiftPoly]
    · rcases polyStep_deg b (L.foldr polyStep p) with h | h
      · exact Or.inl h
      · right; omega

end Eventual

end MixedDiffConst

open MixedDiffConst in

theorem MixedDiffConst.proof (h1 : HilbDegreeBound.Statement.{u})
    (h2 : HilbEventuallyPoly.Statement.{u}) : MixedDiffConst.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn
  obtain ⟨p, hp⟩ := h2 F K ι I hI
  have hdeg : p.totalDegree ≤ n := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · have := (h1 F K ι I hI).1 hrel p hp hp0
      rw [hn] at this
      exact_mod_cast this
  have key : ∀ (r : ℕ) (bs : Fin r → K → ℤ), n ≤ r → ∃ c : ℚ, (n < r → c = 0) ∧
      ∀ᶠ m in atTop, (mixedDiff bs (hilbFn I) m : ℚ) = c := by
    intro r bs hr
    have hE := eventuallyPoly_foldr (List.ofFn bs) hp
    rcases foldr_polyStep_deg (List.ofFn bs) p with h0 | hd
    · refine ⟨0, fun _ => rfl, ?_⟩
      filter_upwards [hE] with m hm
      rw [mixedDiff, hm, h0, map_zero]
    · rw [List.length_ofFn] at hd
      have hq0 : ((List.ofFn bs).foldr polyStep p).totalDegree = 0 := by omega
      refine ⟨coeff 0 ((List.ofFn bs).foldr polyStep p), fun hlt => by omega, ?_⟩
      rw [totalDegree_eq_zero_iff_eq_C] at hq0
      filter_upwards [hE] with m hm
      rw [mixedDiff, hm, hq0, eval_C, coeff_C, if_pos rfl]
  constructor
  · intro bs
    obtain ⟨c, -, hc⟩ := key n bs le_rfl
    obtain ⟨m0, hm0⟩ := hc.exists
    have hc' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = mixedDiff bs (hilbFn I) m0 :=
      hc.mono fun m hm => by exact_mod_cast hm.trans hm0.symm
    have hex : ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = c := ⟨_, hc'⟩
    have hval : intNum F I bs = mixedDiff bs (hilbFn I) m0 := by
      unfold intNum eventualValue
      rw [dif_pos hex]
      obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and hc').exists
      rw [← hm1, hm2]
    filter_upwards [hc'] with m hm
    rw [hm, hval]
  · intro r hr bs
    obtain ⟨c, hc0, hc⟩ := key r bs hr.le
    filter_upwards [hc] with m hm
    rw [hc0 hr] at hm
    exact_mod_cast hm

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR Filter

universe u

section

variable {K : Type*}

theorem diffStep_zero_left (h : (K → ℤ) → ℤ) : diffStep 0 h = 0 := by
  funext m
  simp [diffStep]

theorem diffStep_zero_right (b : K → ℤ) : diffStep b (0 : (K → ℤ) → ℤ) = 0 := by
  funext m
  simp [diffStep]

theorem foldr_diffStep_eq_zero_of_mem (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l)
    (h : (K → ℤ) → ℤ) : l.foldr diffStep h = 0 := by
  induction l with
  | nil => simp at hl
  | cons a t ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hl with rfl | ht
    · exact diffStep_zero_left _
    · rw [ih ht]
      exact diffStep_zero_right a

theorem mixedDiff_coord_zero {n : ℕ} (bs : Fin n → K → ℤ) (i : Fin n) (hi : bs i = 0)
    (h : (K → ℤ) → ℤ) : mixedDiff bs h = 0 :=
  foldr_diffStep_eq_zero_of_mem _ (List.mem_ofFn.mpr ⟨i, hi⟩) h

theorem diffStep_eventually_zero {b : K → ℤ} {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, diffStep b h m = 0 := by
  have hs : ∀ᶠ m in atTop, h (m + -b) = 0 :=
    (tendsto_atTop_add_const_right atTop (-b) tendsto_id).eventually hh
  filter_upwards [hh, hs] with m h1 h2
  simp only [diffStep, h1, ← sub_eq_add_neg] at h2 ⊢
  rw [h2, sub_zero]

theorem mixedDiff_eventually_zero {n : ℕ} (bs : Fin n → K → ℤ) {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, mixedDiff bs h m = 0 := by
  unfold mixedDiff
  induction List.ofFn bs with
  | nil => simpa using hh
  | cons a t ih => exact diffStep_eventually_zero ih

theorem eventualValue_eq_zero {f : (K → ℤ) → ℤ} (hf : ∀ᶠ m in atTop, f m = 0) :
    eventualValue f = 0 := by
  unfold eventualValue
  have hex : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨0, hf⟩
  rw [dif_pos hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hf).exists
  rw [← h1, h2]

end

theorem exists_nat_of_le_of_lt {x : WithBot (WithTop ℤ)} {t n : ℕ}
    (h1 : (t : WithBot (WithTop ℤ)) ≤ x) (h2 : x < n) : ∃ d : ℕ, x = d := by
  rw [← WithBot.coe_natCast, ← WithTop.coe_natCast] at h1 h2
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h1 (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd h2 (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))
    | coe z =>
      have hz : (t : ℤ) ≤ z := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h1)
      refine ⟨z.toNat, ?_⟩
      rw [← WithBot.coe_natCast, ← WithTop.coe_natCast, Int.toNat_of_nonneg (by omega)]

theorem IntNumZeroSlot.proof (h₁ : MixedDiffConst.Statement.{u})
    (h₂ : HilbEventuallyPoly.Statement.{u}) (h₃ : HilbDegreeBound.Statement.{u}) :
    IntNumZeroSlot.Statement.{u} := by
  intro F _ K _ _ ι _ I
  refine ⟨fun n bs i hi => ?_, fun hI n bs hn => ?_⟩
  · unfold intNum
    refine eventualValue_eq_zero (Eventually.of_forall fun m => ?_)
    rw [mixedDiff_coord_zero bs i hi]
    rfl
  · unfold intNum
    apply eventualValue_eq_zero
    by_cases hR : IsRelevant I
    · by_cases hd : ∃ d : ℕ, relDim I = d
      · obtain ⟨d, hd⟩ := hd
        have hdn : d < n := by
          rw [hd] at hn
          exact_mod_cast hn
        exact (h₁ F K ι I hI hR d hd).2 n hdn bs
      · obtain ⟨p, hp⟩ := h₂ F K ι I hI
        have hp0 : p = 0 := by
          by_contra hne
          exact hd (exists_nat_of_le_of_lt ((h₃ F K ι I hI).1 hR p hp hne) hn)
        apply mixedDiff_eventually_zero
        filter_upwards [hp] with m hm
        rw [hp0, map_zero] at hm
        exact_mod_cast hm
    · exact mixedDiff_eventually_zero bs ((h₃ F K ι I hI).2 hR)

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

universe u

namespace MultEqualsCoeff

variable {K : Type*}

theorem tendsto_sub (c : K → ℤ) : Tendsto (fun m : K → ℤ => m - c) atTop atTop :=
  tendsto_atTop_atTop.2 fun a => ⟨a + c, fun _ hm => le_sub_iff_add_le.mpr hm⟩

theorem foldr_diffStep_sum {J : Type*} (s : Finset J) (f : J → (K → ℤ) → ℤ) :
    ∀ L : List (K → ℤ), L.foldr diffStep (∑ j ∈ s, f j) = ∑ j ∈ s, L.foldr diffStep (f j)
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons]
      rw [foldr_diffStep_sum s f L]
      funext m
      simp only [diffStep, Finset.sum_apply, Finset.sum_sub_distrib]

theorem foldr_diffStep_zero : ∀ L : List (K → ℤ), L.foldr diffStep (0 : (K → ℤ) → ℤ) = 0
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons, foldr_diffStep_zero L]
      funext m
      simp [diffStep]

theorem foldr_diffStep_shift (h : (K → ℤ) → ℤ) (c : K → ℤ) :
    ∀ L : List (K → ℤ),
      L.foldr diffStep (fun m => h (m - c)) = fun m => L.foldr diffStep h (m - c)
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons]
      rw [foldr_diffStep_shift h c L]
      funext m
      simp only [diffStep, sub_right_comm m b c]

theorem foldr_diffStep_eventuallyEq {h g : (K → ℤ) → ℤ} (e : h =ᶠ[atTop] g) :
    ∀ L : List (K → ℤ), L.foldr diffStep h =ᶠ[atTop] L.foldr diffStep g
  | [] => e
  | b :: L => by
      have e' := foldr_diffStep_eventuallyEq e L
      filter_upwards [e', (tendsto_sub b).eventually e'] with m h1 h2
      simp only [List.foldr_cons, diffStep]
      rw [h1, h2]

theorem exists_nat_of_nonneg_of_lt {x : WithBot (WithTop ℤ)} {n : ℕ} (h0 : 0 ≤ x)
    (h : x < n) : ∃ d : ℕ, x = d ∧ d < n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd h (not_lt.mpr (by simp))
    | coe z =>
      have hz0 : 0 ≤ z := by exact_mod_cast h0
      obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
      have hdn : (d : ℤ) < n := by exact_mod_cast h
      exact ⟨d, by norm_cast, by omega⟩

variable [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

omit [DecidableEq K] in

theorem relDim_nonneg_of_card_le (I : Ideal (MRing ι F))
    (h : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ I)) : 0 ≤ relDim I := by
  unfold relDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.mpr le_top
    | coe e =>
      have he : Fintype.card K ≤ e := by exact_mod_cast h
      have : (0 : WithTop ℤ) ≤ WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) (e : ℕ∞) := by
        change (0 : WithTop ℤ) ≤ (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)
        exact_mod_cast (by omega : (0 : ℤ) ≤ (e : ℤ) - Fintype.card K)
      exact WithBot.coe_le_coe.mpr this

theorem hilbFn_eventually_zero_of_not_relevant (I : Ideal (MRing ι F)) (hI : ¬ IsRelevant I) :
    ∀ᶠ m in atTop, hilbFn I m = 0 := by
  simp only [IsRelevant, not_forall, not_exists, not_not] at hI
  obtain ⟨k, hk⟩ := hI
  filter_upwards [eventually_ge_atTop (1 : K → ℤ)] with m hm
  unfold hilbFn
  split_ifs with h0
  · have hbot : gradedPiece I (fun k => (m k).toNat) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨f, hf, rfl⟩
      rw [Submodule.mem_bot, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.as_sum f]
      refine Ideal.sum_mem _ fun s hs => ?_
      have hw := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf (mem_support_iff.mp hs)
      obtain ⟨v, hv, hvk⟩ : ∃ v ∈ s.support, v.1 = k := by
        by_contra hne
        simp only [not_exists, not_and] at hne
        have h1 := congrFun hw k
        rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply,
          Finset.sum_eq_zero fun v hv => by
            simp [blockWeight, Ne.symm (hne v hv)]] at h1
        have := hm k
        simp only [Pi.one_apply] at this
        omega
      have hle : Finsupp.single v 1 ≤ s := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
      have hX : (X v : MRing ι F) ∈ I := by
        obtain ⟨k', i⟩ := v
        subst hvk
        exact hk i
      have e : monomial s (coeff s f) = X v * monomial (s - Finsupp.single v 1) (coeff s f) := by
        rw [show (X v : MRing ι F) = monomial (Finsupp.single v 1) 1 from rfl, monomial_mul,
          one_mul, add_tsub_cancel_of_le hle]
      rw [e]
      exact I.mul_mem_right _ hX
    rw [hbot]
    simp
  · rfl

end MultEqualsCoeff

open MultEqualsCoeff in

theorem MultEqualsCoeff.proof (h1 : PrimeFiltration.Statement.{u})
    (h2 : MixedDiffConst.Statement.{u}) (h3 : RelevantPrimeDimGe.Statement.{u}) :
    MultEqualsCoeff.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn bs
  classical
  obtain ⟨r, Q, c, hQ, hsum, hmult, hcase⟩ := h1 F K ι I hI
  let top : Ideal (MRing ι F) → Prop := fun W => W ∈ I.minimalPrimes ∧ IsRelevant W ∧ relDim W = n
  let val : Ideal (MRing ι F) → ℤ := fun W => if top W then intNum F W bs else 0
  have hpiece : ∀ j, ∀ᶠ m in atTop,
      mixedDiff bs (hilbFn (Q j)) (m - fun k => (c j k : ℤ)) = val (Q j) := by
    intro j
    refine (tendsto_sub fun k => (c j k : ℤ)).eventually
      (p := fun x => mixedDiff bs (hilbFn (Q j)) x = val (Q j)) ?_
    obtain ⟨hpr, hhom, -⟩ := hQ j
    by_cases hr : IsRelevant (Q j)
    · rcases (hcase j).resolve_left (not_not.mpr hr) with hlt | ⟨hmin, heq⟩
      · rw [hn] at hlt
        have hnt : ¬ top (Q j) := fun ht => lt_irrefl _ (ht.2.2 ▸ hlt)
        simp only [val, if_neg hnt]
        obtain ⟨d, hd, hdn⟩ := exists_nat_of_nonneg_of_lt
          (relDim_nonneg_of_card_le (Q j) (h3 F K ι (Q j) ⟨hpr, hhom, hr⟩)) hlt
        exact (h2 F K ι (Q j) hhom hr d hd).2 n hdn bs
      · have ht : top (Q j) := ⟨hmin, hr, heq.trans hn⟩
        simp only [val, if_pos ht]
        exact (h2 F K ι (Q j) hhom hr n (heq.trans hn)).1 bs
    · have hnt : ¬ top (Q j) := fun ht => hr ht.2.1
      simp only [val, if_neg hnt]
      filter_upwards [foldr_diffStep_eventuallyEq
        (hilbFn_eventually_zero_of_not_relevant (Q j) hr) (List.ofFn bs)] with m hm
      unfold mixedDiff
      rw [hm]
      exact congrFun (foldr_diffStep_zero _) m
  have hI' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = ∑ j, val (Q j) := by
    have e1 : mixedDiff bs (hilbFn I) =ᶠ[atTop]
        mixedDiff bs (∑ j, fun m => hilbFn (Q j) (m - fun k => (c j k : ℤ))) := by
      apply foldr_diffStep_eventuallyEq
      filter_upwards [hsum] with m hm
      rw [hm, Finset.sum_apply]
    filter_upwards [e1, eventually_all.2 hpiece] with m hm hall
    rw [hm, mixedDiff, foldr_diffStep_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [foldr_diffStep_shift]
    exact hall j
  have hval : intNum F I bs = ∑ j, val (Q j) := by
    obtain ⟨m, ha, hb⟩ := (((h2 F K ι I hI hrel n hn).1 bs).and hI').exists
    rw [← ha, hb]
  have hsupp : (Function.support fun W => topCycle I n W * intNum F W bs) ⊆
      (Finset.univ.image Q : Set (Ideal (MRing ι F))) := by
    intro W hW
    by_contra hWQ
    apply hW
    simp only [topCycle]
    split_ifs with h
    · have hm := hmult W h.1 h.2.1 (h.2.2.trans hn.symm)
      have h0 : (Finset.univ.filter fun j => Q j = W) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro rfl
        exact hWQ (by simp)
      rw [h0, Finset.card_empty] at hm
      rw [← hm]
      simp
    · simp
  rw [hval, cycEval, finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image Q) (g := Q)
      (fun j _ => Finset.mem_image_of_mem Q (Finset.mem_univ j)) (fun j => val (Q j))]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.1 hj).2], Finset.sum_const,
    nsmul_eq_mul]
  simp only [topCycle, val, top]
  split_ifs with h
  · rw [← hmult W h.1 h.2.1 (h.2.2.trans hn.symm)]
    simp
  · simp

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

section Product

variable {K : Type}

def prodFn (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) : (Option K → ℤ) → ℤ :=
  fun m => A (fun k => m (some k)) * B (m none)

def diff1 (g : ℤ → ℤ) : ℤ → ℤ := fun t => g t - g (t - 1)

theorem backwardDifference_apply (g : ℤ → ℤ) (t : ℤ) : diff1 g t = g t - g (t - 1) := rfl

theorem pullDeg_some (c : K → ℤ) (k : K) :
    pullDeg Function.Embedding.some c (some k) = c k :=
  (Function.Embedding.some (α := K)).injective.extend_apply c 0 k

theorem pullDeg_none (c : K → ℤ) : pullDeg Function.Embedding.some c none = 0 := by
  unfold pullDeg
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨a, h⟩
    exact Option.some_ne_none a h

theorem diffStep_pull (c : K → ℤ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    diffStep (pullDeg Function.Embedding.some c) (prodFn A B) = prodFn (diffStep c A) B := by
  funext m
  have h1 : (fun k => (m - pullDeg Function.Embedding.some c) (some k)) =
      (fun k => m (some k)) - c := by
    funext k
    simp [pullDeg_some]
  have h2 : (m - pullDeg Function.Embedding.some c) none = m none := by
    simp [pullDeg_none]
  unfold diffStep prodFn
  rw [h1, h2]
  ring

theorem diffStep_newBlock (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    diffStep (newBlockDeg : Option K → ℤ) (prodFn A B) = prodFn A (diff1 B) := by
  funext m
  have h1 : (fun k => (m - (newBlockDeg : Option K → ℤ)) (some k)) = fun k => m (some k) := by
    funext k
    simp [newBlockDeg]
  have h2 : (m - (newBlockDeg : Option K → ℤ)) none = m none - 1 := by
    simp [newBlockDeg]
  unfold diffStep prodFn diff1
  rw [h1, h2]
  ring

theorem foldr_pull (L : List (K → ℤ)) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    (L.map (pullDeg Function.Embedding.some)).foldr diffStep (prodFn A B) =
      prodFn (L.foldr diffStep A) B := by
  induction L with
  | nil => rfl
  | cons c L ih => simp only [List.map_cons, List.foldr_cons, ih, diffStep_pull]

theorem foldr_newBlock (j : ℕ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    (List.replicate j (newBlockDeg : Option K → ℤ)).foldr diffStep (prodFn A B) =
      prodFn A (diff1^[j] B) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, diffStep_newBlock,
      Function.iterate_succ_apply']

theorem mixedDiff_prodFn {m r : ℕ} (cs : Fin r → K → ℤ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    mixedDiff (Fin.append (fun _ : Fin m => (newBlockDeg : Option K → ℤ))
        (fun i => pullDeg Function.Embedding.some (cs i))) (prodFn A B) =
      prodFn (mixedDiff cs A) (diff1^[m] B) := by
  have h : List.ofFn (fun i => pullDeg Function.Embedding.some (cs i)) =
      (List.ofFn cs).map (pullDeg Function.Embedding.some) := by
    rw [List.map_ofFn]
    rfl
  unfold mixedDiff
  rw [List.ofFn_fin_append, List.foldr_append, List.ofFn_const, h, foldr_pull, foldr_newBlock]

theorem tendsto_restrict :
    Tendsto (fun m : Option K → ℤ => fun k => m (some k)) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨fun o => Option.elim o 0 b, fun _ ha k => ha (some k)⟩

theorem eventually_none_ge (a : ℤ) : ∀ᶠ m : Option K → ℤ in atTop, a ≤ m none :=
  (eventually_ge_atTop (fun _ : Option K => a)).mono fun _ hm => hm none

theorem eventualValue_eq {f : (Option K → ℤ) → ℤ} {c : ℤ} (hf : ∀ᶠ m in atTop, f m = c) :
    eventualValue f = c := by
  have h : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨c, hf⟩
  unfold eventualValue
  rw [dif_pos h]
  obtain ⟨m, h1, h2⟩ := (h.choose_spec.and hf).exists
  exact h1.symm.trans h2

end Product

section Binomial

theorem iter_projSpaceHilb (N : ℕ) : ∀ j : ℕ, j ≤ N → ∀ s : ℕ,
    diff1^[j] (projSpaceHilb N) ((s : ℤ) + j) = (((s + N).choose (N - j) : ℕ) : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro _ s
    simp [projSpaceHilb]
  | succ j ih =>
    intro hj s
    have e1 : (s : ℤ) + ((j + 1 : ℕ) : ℤ) = ((s + 1 : ℕ) : ℤ) + j := by push_cast; ring
    have e2 : (s : ℤ) + ((j + 1 : ℕ) : ℤ) - 1 = (s : ℤ) + j := by push_cast; ring
    rw [Function.iterate_succ_apply', backwardDifference_apply, e2, e1, ih (by omega), ih (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, N - j = k + 1 := ⟨N - (j + 1), by omega⟩
    have hk' : N - (j + 1) = k := by omega
    rw [hk, hk', show s + 1 + N = (s + N) + 1 by omega, Nat.choose_succ_succ']
    push_cast
    ring

theorem backwardDifference_eq_zero_of_eventually_const {g : ℤ → ℤ} {a c : ℤ} (h : ∀ s : ℕ, g (s + a) = c) (s : ℕ) :
    diff1 g (s + (a + 1)) = 0 := by
  rw [backwardDifference_apply, show (s : ℤ) + (a + 1) = ((s + 1 : ℕ) : ℤ) + a by push_cast; ring,
    show ((s + 1 : ℕ) : ℤ) + a - 1 = (s : ℤ) + a by push_cast; ring, h, h, sub_self]

theorem iter_projSpaceHilb_top (N : ℕ) (t : ℤ) (ht : (N : ℤ) ≤ t) :
    diff1^[N] (projSpaceHilb N) t = 1 := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s + N := ⟨(t - N).toNat, by omega⟩
  rw [iter_projSpaceHilb N N le_rfl s, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]

theorem iter_projSpaceHilb_high (N : ℕ) : ∀ i s : ℕ,
    diff1^[N + 1 + i] (projSpaceHilb N) ((s : ℤ) + ((N + 1 + i : ℕ) : ℤ)) = 0 := by
  intro i
  induction i with
  | zero =>
    intro s
    have hN : ∀ s : ℕ, diff1^[N] (projSpaceHilb N) ((s : ℤ) + (N : ℤ)) = 1 := fun s =>
      iter_projSpaceHilb_top N _ (by omega)
    have e : (s : ℤ) + ((N + 1 + 0 : ℕ) : ℤ) = s + ((N : ℤ) + 1) := by push_cast; ring
    rw [e, show N + 1 + 0 = N + 1 from rfl, Function.iterate_succ_apply']
    exact backwardDifference_eq_zero_of_eventually_const hN s
  | succ i ih =>
    intro s
    rw [show N + 1 + (i + 1) = (N + 1 + i) + 1 by omega, Function.iterate_succ_apply',
      Nat.cast_add_one]
    exact backwardDifference_eq_zero_of_eventually_const ih s

theorem iter_projSpaceHilb_above (N j : ℕ) (hj : N < j) (t : ℤ) (ht : (j : ℤ) ≤ t) :
    diff1^[j] (projSpaceHilb N) t = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = N + 1 + i := ⟨j - (N + 1), by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s + ((N + 1 + i : ℕ) : ℤ) :=
    ⟨(t - ((N + 1 + i : ℕ) : ℤ)).toNat, by omega⟩
  exact iter_projSpaceHilb_high N i s

end Binomial

theorem ProductWithProjectiveSpace.proof (h1 : MixedDiffConst.Statement.{u})
    (h2 : HilbAddBlock.Statement.{u}) : ProductWithProjectiveSpace.Statement.{u} := by
  intro F _ K _ _ ι _ P hP e N r m he hrm cs
  have hH : hilbFn (addBlockPrime N P) = prodFn (hilbFn P) (projSpaceHilb N) := by
    funext x
    exact h2 F K ι P N x
  unfold intNum
  rw [hH, mixedDiff_prodFn]
  have hlim := tendsto_restrict (K := K)
  rcases lt_trichotomy m N with hmN | hmN | hmN
  · rw [if_neg hmN.ne]
    apply eventualValue_eq
    have hz := (h1 F K ι P hP.multiHomog hP.relevant e he).2 r (by omega) cs
    filter_upwards [hlim.eventually hz] with x hx
    simp only [prodFn]
    rw [hx, zero_mul]
  · subst hmN
    rw [if_pos rfl]
    obtain rfl : r = e := by omega
    apply eventualValue_eq
    have hc := (h1 F K ι P hP.multiHomog hP.relevant r he).1 cs
    filter_upwards [hlim.eventually hc, eventually_none_ge (m : ℤ)] with x hx hn
    simp only [prodFn]
    rw [hx, iter_projSpaceHilb_top m _ hn, mul_one]
    rfl
  · rw [if_neg hmN.ne']
    apply eventualValue_eq
    filter_upwards [eventually_none_ge (m : ℤ)] with x hn
    simp only [prodFn]
    rw [iter_projSpaceHilb_above N m hmN _ hn, mul_zero]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem GradedFinite.full : GradedFinite.Statement.{u} := GradedFinite.proof

theorem HilbExactDivide.full : HilbExactDivide.Statement.{u} :=
  HilbExactDivide.proof GradedFinite.full

theorem PolyOfDiffs.full : PolyOfDiffs.Statement := PolyOfDiffs.proof

theorem HilbEventuallyPoly.full : HilbEventuallyPoly.Statement.{u} :=
  HilbEventuallyPoly.of_exactDivide_polyOfDiffs HilbExactDivide.full PolyOfDiffs.full

theorem PrimeFiltration.full : PrimeFiltration.Statement.{u} :=
  PrimeFiltration.proof HilbExactDivide.full

theorem EventuallyPolyUnique.full : EventuallyPolyUnique.Statement := EventuallyPolyUnique.proof

theorem EventuallyPolyShift.full : EventuallyPolyShift.Statement := EventuallyPolyShift.proof

theorem HilbIrrelevantZero.full : HilbIrrelevantZero.Statement.{u} := HilbIrrelevantZero.proof

theorem RelevantPrimeDimGe.full : RelevantPrimeDimGe.Statement.{u} := RelevantPrimeDimGe.proof

theorem HilbDegreeBound.full : HilbDegreeBound.Statement.{u} :=
  HilbDegreeBound.proof HilbEventuallyPoly.full HilbExactDivide.full PolyOfDiffs.full
    PrimeFiltration.full EventuallyPolyUnique.full EventuallyPolyShift.full
    HilbIrrelevantZero.full RelevantPrimeDimGe.full

theorem MixedDiffConst.full : MixedDiffConst.Statement.{u} :=
  MixedDiffConst.proof HilbDegreeBound.full HilbEventuallyPoly.full

theorem IntNumSymm.full : IntNumSymm.Statement := IntNumSymm.proof

theorem IntNumAdd.full : IntNumAdd.Statement.{u} := IntNumAdd.proof MixedDiffConst.full

theorem IntNumZeroSlot.full : IntNumZeroSlot.Statement.{u} :=
  IntNumZeroSlot.proof MixedDiffConst.full HilbEventuallyPoly.full HilbDegreeBound.full

theorem IntNumBase.full : IntNumBase.Statement.{u} := IntNumBase.proof MixedDiffConst.full

theorem MultEqualsCoeff.full : MultEqualsCoeff.Statement.{u} :=
  MultEqualsCoeff.proof PrimeFiltration.full MixedDiffConst.full RelevantPrimeDimGe.full

theorem CutRegular.full : CutRegular.Statement.{u} :=
  CutRegular.proof HilbExactDivide.full MultEqualsCoeff.full IntNumSymm.full

theorem CutRational.full : CutRational.Statement.{u} :=
  CutRational.proof CutRegular.full IntNumAdd.full

theorem DivPrincipalDegree.full : DivPrincipalDegree.Statement.{u} :=
  DivPrincipalDegree.proof CutRational.full IntNumBase.full IntNumZeroSlot.full

theorem ExistsForm.full : ExistsForm.Statement.{u} := ExistsForm.proof

theorem DivCycleSupport.full : DivCycleSupport.Statement.{u} := DivCycleSupport.proof

theorem IntNumUnique.full : IntNumUnique.Statement.{u} :=
  IntNumUnique.proof CutRational.full IntNumBase.full ExistsForm.full DivCycleSupport.full

theorem IntNumBaseChange.full : IntNumBaseChange.Statement := IntNumBaseChange.intersectionNumber_baseChange

theorem ProjectionFormulaContracted.full : ProjectionFormulaContracted.Statement.{u} :=
  PFContracted.proof MixedDiffConst.full CutRational.full

theorem HilbAddBlock.full : HilbAddBlock.Statement.{u} := HilbAddBlock.proof

theorem ProductWithProjectiveSpace.full : ProductWithProjectiveSpace.Statement.{u} :=
  ProductWithProjectiveSpace.proof MixedDiffConst.full HilbAddBlock.full

theorem ProjectionFormulaDegree.of_divPushForward (h : DivPushForward.Statement.{u}) :
    ProjectionFormulaDegree.Statement.{u} :=
  ProjectionFormulaDegree.proof CutRational.full IntNumBase.full ProjectionFormulaContracted.full h

theorem RenameMultiHomog.full : RenameMultiHomog.Statement.{u} := RenameMultiHomog.proof

theorem RenameHilbFn.full : RenameHilbFn.Statement.{u} := RenameHilbFn.proof

theorem RenameIntNum.full : RenameIntNum.Statement.{u} := RenameIntNum.proof RenameHilbFn.full

theorem RenameMultiProjPrime.full : RenameMultiProjPrime.Statement.{u} :=
  RenameMultiProjPrime.proof

theorem SplitRelDeg.full : SplitRelDeg.Statement.{u} := SplitRelDeg.proof

end GroundTheory.Heights₂.Heights.FieldNumbers
end
