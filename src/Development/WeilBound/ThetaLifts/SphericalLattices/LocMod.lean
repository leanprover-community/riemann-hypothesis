import Development.WeilBound.ThetaLifts.SphericalLattices.LocCommSt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeConjModularCharacter

section
noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
open scoped Pointwise

section Asm

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem asm_ordL_eq (x : L) : ordL x = -WithZero.log (Valued.v x : WithZero (Multiplicative ℤ)) := by
  unfold ordL
  split_ifs with h
  · rw [h]; simp
  · congr 1
    conv_rhs => rw [← WithZero.coe_unzero h]
    rfl

theorem asm_ordL_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have hx' : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hx
  have hy' : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hy
  rw [asm_ordL_eq, asm_ordL_eq, asm_ordL_eq, map_mul, WithZero.log_mul hx' hy']
  ring

theorem asm_ordL_pow (x : L) (n : ℕ) : ordL (x ^ n) = n * ordL x := by
  rw [asm_ordL_eq, asm_ordL_eq, map_pow, WithZero.log_pow]
  simp

theorem asm_ordL_unit {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) (h : x * y = 1) : ordL x = 0 := by
  have hx' : (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 := hx
  have hy' : (Valued.v y : WithZero (Multiplicative ℤ)) ≤ 1 := hy
  have h1 : (Valued.v x : WithZero (Multiplicative ℤ)) * Valued.v y = 1 := by rw [← map_mul, h, map_one]
  have h2 : (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
    refine le_antisymm hx' ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v y := h1.symm
      _ ≤ Valued.v x * 1 := mul_le_mul_right hy' _
      _ = _ := mul_one _
  rw [asm_ordL_eq, h2]; simp

variable {c : L →+* L} {m : ℕ}

def asmT (p : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m) (Fin m) L :=
  (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₁₁

theorem asm_low {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) :
    (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₂₁ = 0 :=
  GlobalTheory.LGrp.mem_blockQ_two.1 hp.2

theorem asmT_mul (a : GL (Fin m ⊕ Fin m) L) {b : GL (Fin m ⊕ Fin m) L} (hb : b ∈ PW L c m) :
    asmT (a * b) = asmT a * asmT b := by
  unfold asmT
  rw [Units.val_mul]
  conv_lhs => rw [← fromBlocks_toBlocks (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L),
    ← fromBlocks_toBlocks (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L), fromBlocks_multiply, toBlocks_fromBlocks₁₁,
    asm_low hb, Matrix.mul_zero, add_zero]

theorem asmT_one : asmT (1 : GL (Fin m ⊕ Fin m) L) = 1 := by
  unfold asmT
  rw [Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁]

theorem asmT_det_mul_inv {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) :
    (asmT p).det * (asmT p⁻¹).det = 1 := by
  rw [← det_mul, ← asmT_mul p (inv_mem hp), mul_inv_cancel, asmT_one, det_one]

theorem asmT_det_ne {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) : (asmT p).det ≠ 0 :=
  left_ne_zero_of_mul_eq_one (asmT_det_mul_inv hp)

theorem asmT_det_int {k : GL (Fin m ⊕ Fin m) L} (hk : k ∈ IntGL L m) : (asmT k).det ∈ intL L := by
  obtain ⟨g, rfl⟩ := hk
  have e : asmT (Matrix.GeneralLinearGroup.map (intL L).subtype g) =
      (intL L).subtype.mapMatrix (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L)).toBlocks₁₁ := by
    ext i j; rfl
  rw [e, ← RingHom.map_det]
  exact Subtype.property _

theorem asm_ord_K {k : GL (Fin m ⊕ Fin m) L} (hk : k ∈ KPW L c m) : ordL (asmT k).det = 0 :=
  asm_ordL_unit (asmT_det_int hk.2.2) (asmT_det_int (inv_mem hk.2.2)) (asmT_det_mul_inv hk.1)

theorem asm_ord_mul {a b : GL (Fin m ⊕ Fin m) L} (ha : a ∈ PW L c m) (hb : b ∈ PW L c m) :
    ordL (asmT (a * b)).det = ordL (asmT a).det + ordL (asmT b).det := by
  rw [asmT_mul a hb, det_mul, asm_ordL_mul (asmT_det_ne ha) (asmT_det_ne hb)]

theorem ord_det_uniformizer_image_eq {ϖ : L} {q : ℕ} (h : IsUnramInv ϖ c q) (x : Lˣ) (hx : (x : L) = ϖ) :
    ordL (asmT (zW L m x)).det = m := by
  have e : asmT (zW L m x) = (x : L) • (1 : Matrix (Fin m) (Fin m) L) := toBlocks_fromBlocks₁₁ _ _ _ _
  have o : ordL ϖ = 1 := by
    rw [asm_ordL_eq, h.2.2.2.1]
    rfl
  rw [e, det_smul, det_one, mul_one, Fintype.card_fin, asm_ordL_pow, hx, o, mul_one]

end Asm

theorem asm_smul {G : Type} [Group G] (K : Subgroup G) (p : G) :
    MulAut.conj p • K = K.map (MulAut.conj p).toMonoidHom := rfl

theorem asm_relIndex {G : Type} [Group G] (K : Subgroup G) (p : G) :
    K.relIndex (K.map (MulAut.conj p).toMonoidHom) = (K.map (MulAut.conj p⁻¹).toMonoidHom).relIndex K := by
  have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj p⁻¹).toMonoidHom) K
    (K.map (MulAut.conj p).toMonoidHom) (MulAut.conj p⁻¹).injective
  have e : (K.map (MulAut.conj p).toMonoidHom).map (MulAut.conj p⁻¹).toMonoidHom = K := by
    rw [← asm_smul, ← asm_smul, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [e] at h
  exact h.symm

theorem asm_conj_self {G : Type} [Group G] (K : Subgroup G) {k : G} (hk : k ∈ K) : MulAut.conj k • K = K :=
  Subgroup.conj_smul_eq_self_of_mem hk

theorem locMod_of (h1 : LocCommSt) (h2 : ZCountSt) (h3 : GenSt) : LocModSt := by
  intro L _ _ ϖ c q hU m p hp
  have hq : (0 : ℝ) < q := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : 0 < q)
  obtain ⟨hmul, hpos, -, -⟩ := GlobalTheory.T.haarInvVolume_conj_modular_character (PW L c m) (KPW L c m) inf_le_left
    (fun h hh => ⟨(h1 L ϖ c q hU m h hh).2, (h1 L ϖ c q hU m h hh).1⟩)
  have key := h3 L ϖ c q hU m
    (fun a => GlobalTheory.HL.invVol (KPW L c m) (MulAut.conj a • KPW L c m) *
      (q : ℝ) ^ (-(2 * (m : ℤ) * ordL (asmT a).det)))
    (fun a ha b hb => by
      rw [hmul a ha b hb, asm_ord_mul ha hb, mul_add, neg_add, zpow_add₀ hq.ne']
      ring)
    (fun a ha => mul_pos (hpos a ha) (zpow_pos hq _))
    (fun k hk => by
      rw [asm_conj_self _ hk, asm_ord_K hk, GlobalTheory.HL.invVol, Subgroup.relIndex_self]
      simp)
    (fun x hx => by
      obtain ⟨hle, hi⟩ := h2 L ϖ c q hU m x hx
      rw [ord_det_uniformizer_image_eq hU x hx, asm_smul, GlobalTheory.HL.invVol, hi, Subgroup.relIndex_eq_one.2 hle, Nat.cast_one, div_one,
        Nat.cast_pow, ← zpow_natCast, ← zpow_add₀ hq.ne']
      push_cast
      rw [add_neg_cancel, zpow_zero])
    p hp
  have hb := (h1 L ϖ c q hU m p hp).2
  rw [asm_relIndex] at hb
  have hb' : ((((KPW L c m).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (KPW L c m) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hb
  simp only [asm_smul, GlobalTheory.HL.invVol, asm_relIndex] at key
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq hb'] at key
  rw [← key, mul_comm]
  rfl

end PositivityTheory.Sph.M2

end
end

section
noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

namespace Comm

section Abs

variable {L : Type} [Field L] (O : Subring L) {n : Type} [Fintype n] [DecidableEq n]

theorem mem_range_of_entries (g : GL n L) (h1 : ∀ i j, (g : Matrix n n L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL n L) : Matrix n n L) i j ∈ O) :
    g ∈ (Matrix.GeneralLinearGroup.map (n := n) O.subtype).range := by
  let A : Matrix n n O := fun i j => ⟨_, h1 i j⟩
  let B : Matrix n n O := fun i j => ⟨_, h2 i j⟩
  have hA : O.subtype.mapMatrix A = (g : Matrix n n L) := by ext i j; rfl
  have hB : O.subtype.mapMatrix B = ((g⁻¹ : GL n L) : Matrix n n L) := by ext i j; rfl
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix n n O →+* Matrix n n L) := by
    intro X Y h
    ext i j
    exact congrFun (congrFun h i) j
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, hA, hB, map_one]; exact Units.mul_inv g
  · rw [map_mul, hA, hB, map_one]; exact Units.inv_mul g
  · ext1; exact hA

theorem entries_conj (a : L) (A B X : Matrix n n L) (hAB : A * B = 1)
    (h : ∀ i j k l, a * (A i j * B k l) ∈ O) (hX : ∀ i j, ∃ y ∈ O, (X - 1) i j = a * y) (i j : n) :
    (A * X * B) i j ∈ O := by
  have e : A * X * B = 1 + A * (X - 1) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]; abel
  rw [e, Matrix.add_apply]
  refine O.add_mem ?_ ?_
  · rw [Matrix.one_apply]; split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  · rw [Matrix.mul_apply]
    refine O.sum_mem fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine O.sum_mem fun k _ => ?_
    obtain ⟨y, hy, e⟩ := hX k l
    rw [e]
    have : A i k * (a * y) * B l j = a * (A i k * B l j) * y := by ring
    rw [this]
    exact O.mul_mem (h _ _ _ _) hy

theorem ker_entries (a : O) (k : GL n O)
    (hk : k ∈ (Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {a}))).ker) (i j : n) :
    ∃ y ∈ O, (((Matrix.GeneralLinearGroup.map (n := n) O.subtype k : GL n L) : Matrix n n L) - 1) i j = (a : L) * y := by
  have h1 : Ideal.Quotient.mk (Ideal.span {a}) ((k : Matrix n n O) i j) =
      Ideal.Quotient.mk (Ideal.span {a}) ((1 : Matrix n n O) i j) := by
    have := congrArg (fun g : GL n (O ⧸ Ideal.span {a}) => (g : Matrix n n (O ⧸ Ideal.span {a})) i j)
      (MonoidHom.mem_ker.1 hk)
    refine Eq.trans this ?_
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs <;> simp
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, y.2, ?_⟩
  have h2 := congrArg O.subtype hy
  rw [map_sub, map_mul] at h2
  refine Eq.trans ?_ h2
  rw [Matrix.sub_apply]
  congr 1
  simp only [Matrix.one_apply]
  split_ifs <;> simp

theorem ker_le_conj (a : O) (p : GL n L)
    (h : ∀ i j k l, (a : L) * (((p⁻¹ : GL n L) : Matrix n n L) i j * (p : Matrix n n L) k l) ∈ O) :
    ((Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {a}))).ker).map
        (Matrix.GeneralLinearGroup.map (n := n) O.subtype) ≤
      ((Matrix.GeneralLinearGroup.map (n := n) O.subtype).range).map (MulAut.conj p).toMonoidHom := by
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨p⁻¹ * Matrix.GeneralLinearGroup.map (n := n) O.subtype k * p, ?_, ?_⟩
  · refine mem_range_of_entries O _ ?_ ?_
    · intro i j
      rw [Units.val_mul, Units.val_mul]
      exact entries_conj O a _ _ _ (Units.inv_mul p) h (ker_entries O a k hk) i j
    · intro i j
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc, ← map_inv, Units.val_mul, Units.val_mul]
      exact entries_conj O a _ _ _ (Units.inv_mul p) h (ker_entries O a k⁻¹ (Subgroup.inv_mem _ hk)) i j
  · simp [mul_assoc]

theorem relIndex_conj_range (a : O) [Finite (O ⧸ Ideal.span {a})] (p : GL n L)
    (h : ∀ i j k l, (a : L) * (((p⁻¹ : GL n L) : Matrix n n L) i j * (p : Matrix n n L) k l) ∈ O) :
    (((Matrix.GeneralLinearGroup.map (n := n) O.subtype).range).map (MulAut.conj p).toMonoidHom).relIndex
      (Matrix.GeneralLinearGroup.map (n := n) O.subtype).range ≠ 0 := by
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := n) O.subtype) := by
    intro X Y h
    ext i j
    exact congrArg (fun g : GL n L => (g : Matrix n n L) i j) h
  have h1 : (((Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {a}))).ker).map
        (Matrix.GeneralLinearGroup.map (n := n) O.subtype)).relIndex
        (Matrix.GeneralLinearGroup.map (n := n) O.subtype).range ≠ 0 := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  intro h0
  exact h1 (Subgroup.relIndex_eq_zero_of_le_left (ker_le_conj O a p h) h0)

end Abs

section Grp

variable {G : Type} [Group G]

theorem conj_inf (P K : Subgroup G) (p : G) (hp : p ∈ P) :
    (P ⊓ K).map (MulAut.conj p).toMonoidHom = P ⊓ K.map (MulAut.conj p).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨P.mul_mem (P.mul_mem hp h1) (P.inv_mem hp), ⟨x, h2, rfl⟩⟩
  · rintro _ ⟨h1, x, h2, rfl⟩
    refine ⟨x, ⟨?_, h2⟩, rfl⟩
    have h3 : p⁻¹ * (p * x * p⁻¹) * p ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hp) h1) hp
    simpa [mul_assoc] using h3

theorem relIndex_conj_inf (P K : Subgroup G) (p : G) (hp : p ∈ P)
    (h : (K.map (MulAut.conj p).toMonoidHom).relIndex K ≠ 0) :
    ((P ⊓ K).map (MulAut.conj p).toMonoidHom).relIndex (P ⊓ K) ≠ 0 := by
  rw [conj_inf P K p hp, inf_comm P, inf_comm P]
  exact Subgroup.relIndex_inter_ne_zero h P

theorem relIndex_conj_swap (K : Subgroup G) (p : G)
    (h : (K.map (MulAut.conj p⁻¹).toMonoidHom).relIndex K ≠ 0) :
    K.relIndex (K.map (MulAut.conj p).toMonoidHom) ≠ 0 := by
  rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj p).toMonoidHom) _ _ (MulAut.conj p).injective,
    Subgroup.map_map] at h
  have e : (MulAut.conj p).toMonoidHom.comp (MulAut.conj p⁻¹).toMonoidHom = MonoidHom.id G := by
    ext x; simp [mul_assoc]
  rwa [e, Subgroup.map_id] at h

end Grp

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_intL (x : L) : x ∈ intL L ↔ Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) := Iff.rfl

theorem eventually_int (ϖ : L)
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (x : L) :
    ∀ᶠ N : ℕ in Filter.atTop, ϖ ^ N * x ∈ intL L := by
  by_cases hx : Valued.v x = (0 : WithZero (Multiplicative ℤ))
  · refine Filter.Eventually.of_forall fun N => ?_
    rw [mem_intL, map_mul, hx, mul_zero]; exact zero_le_one
  · obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 hx
    refine Filter.eventually_atTop.2 ⟨(Multiplicative.toAdd u).toNat, fun N hN => ?_⟩
    rw [mem_intL, map_mul, map_pow, hv, ← hu, ← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one,
      WithZero.coe_le_coe, ← Multiplicative.toAdd_le]
    simp only [toAdd_mul, toAdd_pow, toAdd_ofAdd, toAdd_one, smul_neg, nsmul_eq_mul, mul_one]
    omega

theorem le_of_lt_one (ϖ : L)
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (x : L)
    (hx : Valued.v x < (1 : WithZero (Multiplicative ℤ))) : x / ϖ ∈ intL L := by
  by_cases h0 : Valued.v x = (0 : WithZero (Multiplicative ℤ))
  · rw [mem_intL, map_div₀, h0, zero_div]; exact zero_le_one
  · obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0
    rw [← hu, ← WithZero.coe_one, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt] at hx
    rw [mem_intL, map_div₀, hv, ← hu, ← WithZero.coe_div, ← WithZero.coe_one,
      WithZero.coe_le_coe, ← Multiplicative.toAdd_le]
    simp only [toAdd_div, toAdd_ofAdd, toAdd_one] at hx ⊢
    omega

theorem finite_quot (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) :
    ∃ a : intL L, (a : L) = ϖ ∧ ∀ N : ℕ, Finite (intL L ⧸ Ideal.span {a ^ N}) := by
  obtain ⟨-, -, -, hv, -, hq, hc⟩ := h
  have hϖ : ϖ ∈ intL L := by
    rw [mem_intL, hv, ← WithZero.coe_one, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]; simp
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.zero_ne_coe hv
  refine ⟨⟨ϖ, hϖ⟩, rfl, fun N => ?_⟩
  let M : Ideal (intL L) :=
    IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hM : Finite (intL L ⧸ M) := by
    have : Nat.card (intL L ⧸ M) = q ^ 2 := hc
    exact Nat.finite_of_card_ne_zero (by rw [this]; positivity)
  have hle : M ≤ Ideal.span {(⟨ϖ, hϖ⟩ : intL L)} := by
    intro x hx
    have hx' : Valued.v (x : L) < (1 : WithZero (Multiplicative ℤ)) :=
      (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) (a := x)).1 hx
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨_, le_of_lt_one ϖ hv x hx'⟩, Subtype.ext ?_⟩
    show (x : L) = ϖ * ((x : L) / ϖ)
    field_simp
  have hF : Finite (intL L ⧸ Ideal.span {(⟨ϖ, hϖ⟩ : intL L)}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  rw [← Ideal.span_singleton_pow]
  exact Ideal.finite_quotient_pow ⟨{⟨ϖ, hϖ⟩}, by simp⟩ N

theorem relIndex_intGL (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) (m : ℕ) (p : GL (Fin m ⊕ Fin m) L) :
    ((IntGL L m).map (MulAut.conj p).toMonoidHom).relIndex (IntGL L m) ≠ 0 := by
  obtain ⟨a, ha, hF⟩ := finite_quot ϖ c q h
  have hev : ∀ᶠ N : ℕ in Filter.atTop, ∀ i j k l,
      ϖ ^ N * (((p⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j *
        (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) k l) ∈ intL L := by
    simp only [Filter.eventually_all]
    intro i j k l
    exact eventually_int ϖ h.2.2.2.1 _
  obtain ⟨N, hN⟩ := hev.exists
  haveI := hF N
  refine relIndex_conj_range (intL L) (a ^ N) p ?_
  rw [SubmonoidClass.coe_pow, ha]
  exact hN

theorem KPW_eq (c : L →+* L) (m : ℕ) : KPW L c m = PW L c m ⊓ IntGL L m := by
  show PW L c m ⊓ (GW L c m ⊓ IntGL L m) = _
  have hle : PW L c m ≤ GW L c m := inf_le_left
  rw [← inf_assoc, inf_eq_left.2 hle]

end Val

end Comm

theorem locComm : LocCommSt := by
  intro L _ _ ϖ c q h m p hp
  rw [Comm.KPW_eq]
  exact ⟨Comm.relIndex_conj_inf _ _ p hp (Comm.relIndex_intGL ϖ c q h m p),
    Comm.relIndex_conj_swap _ p
      (Comm.relIndex_conj_inf _ _ p⁻¹ (Subgroup.inv_mem _ hp) (Comm.relIndex_intGL ϖ c q h m p⁻¹))⟩

end PositivityTheory.Sph.M2

end
end

section
noncomputable section

namespace PositivityTheory.Sph.M2.ZC

open Matrix Formalism.UG

theorem index_comap_of_cover {A G : Type*} [Group A] [Group G] (f : A →* G) (H : Subgroup G)
    (h : ∀ g, ∃ a, (f a)⁻¹ * g ∈ H) : (H.comap f).index = H.index := by
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' f (fun a b hab => ?_) : A ⧸ H.comap f → G ⧸ H) ⟨?_, ?_⟩)
  · rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa using hab
  · intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    intro hab
    have h1 : ((f a : G) : G ⧸ H) = (f b : G) := hab
    rw [QuotientGroup.eq] at h1 ⊢
    simpa using h1
  · intro g
    induction g using QuotientGroup.induction_on with | H g => ?_
    obtain ⟨a, ha⟩ := h g
    exact ⟨(a : A ⧸ H.comap f), (QuotientGroup.eq.mpr ha : ((f a : G) : G ⧸ H) = g)⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_int {y : L} : y ∈ intL L ↔ Valued.v y ≤ (1 : WithZero (Multiplicative ℤ)) := Iff.rfl

def A (r : L) : AddSubgroup L := (intL L).toAddSubgroup.comap (AddMonoidHom.mulLeft r)

theorem mem_A {r y : L} : y ∈ A r ↔ r * y ∈ intL L := Iff.rfl

theorem A_mul (r s : L) : A (r * s) = (A r).comap (AddMonoidHom.mulLeft s) := by
  ext y
  simp [mem_A, mul_assoc]

theorem relIndex_A_mul (r r' s : L) (hs : s ≠ 0) : (A (r * s)).relIndex (A (r' * s)) = (A r).relIndex (A r') := by
  rw [A_mul, A_mul, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]
  intro y
  exact ⟨s⁻¹ * y, by simp [hs]⟩

variable {ϖ : L} {c : L →+* L} {q : ℕ}

theorem pi_ne (h : IsUnramInv ϖ c q) : ϖ ≠ 0 := by
  intro h0
  have := h.2.2.2.1
  rw [h0, map_zero] at this
  exact WithZero.coe_ne_zero this.symm

theorem pi_int (h : IsUnramInv ϖ c q) : ϖ ∈ intL L := by
  rw [mem_int, h.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe]
  decide

theorem mem_A_inv (h : IsUnramInv ϖ c q) {y : L} :
    y ∈ A ϖ⁻¹ ↔ Valued.v y < (1 : WithZero (Multiplicative ℤ)) := by
  rw [mem_A, mem_int, map_mul, map_inv₀, h.2.2.2.1]
  by_cases hy : Valued.v y = (0 : WithZero (Multiplicative ℤ))
  · simp [hy]
  · obtain ⟨n, hn⟩ := WithZero.ne_zero_iff_exists.mp hy
    rw [← hn, ← WithZero.coe_inv, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe, WithZero.coe_lt_coe]
    show (-(-1 : ℤ) + Multiplicative.toAdd n ≤ 0) ↔ Multiplicative.toAdd n < 0
    omega

theorem relIndex_one (h : IsUnramInv ϖ c q) : (A ϖ⁻¹).relIndex (A (1 : L)) = q ^ 2 := by
  have e : A (1 : L) = (intL L).subtype.toAddMonoidHom.range := by
    ext y
    simp [mem_A]
  rw [e, ← AddSubgroup.index_comap, ← h.2.2.2.2.2.2]
  have e2 : (A ϖ⁻¹).comap (intL L).subtype.toAddMonoidHom =
      (IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring).toAddSubgroup := by
    ext y
    rw [AddSubgroup.mem_comap, mem_A_inv h]
    exact (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) (a := y)).symm
  rw [e2]
  rfl

theorem A_le (h : IsUnramInv ϖ c q) (r : L) : A (ϖ⁻¹ * r) ≤ A r := by
  intro y hy
  rw [mem_A] at hy ⊢
  have := (intL L).mul_mem (pi_int h) hy
  rwa [mul_assoc, mul_inv_cancel_left₀ (pi_ne h)] at this

theorem relIndex_two (h : IsUnramInv ϖ c q) : (A (ϖ⁻¹ * ϖ⁻¹)).relIndex (A (1 : L)) = q ^ 4 := by
  have h1 : (A (ϖ⁻¹ * ϖ⁻¹)).relIndex (A ϖ⁻¹) = q ^ 2 := by
    rw [← relIndex_one h, ← relIndex_A_mul ϖ⁻¹ 1 ϖ⁻¹ (inv_ne_zero (pi_ne h)), one_mul]
  have h2 : A ϖ⁻¹ ≤ A (1 : L) := by simpa using A_le h 1
  rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (A_le h _) h2, h1, relIndex_one h]
  ring

def MA (m : ℕ) (r : L) : AddSubgroup (Matrix (Fin m) (Fin m) L) :=
  AddSubgroup.pi Set.univ fun _ => AddSubgroup.pi Set.univ fun _ => A r

theorem mem_MA {m : ℕ} {r : L} {X : Matrix (Fin m) (Fin m) L} : X ∈ MA m r ↔ ∀ i j, r * X i j ∈ intL L :=
  ⟨fun h i j => h i trivial j trivial, fun h i _ j _ => h i j⟩

theorem relIndex_MA (m : ℕ) (r : L) : (MA m r).relIndex (MA m (1 : L)) = ((A r).relIndex (A (1 : L))) ^ (m * m) := by
  let g : (Fin m → Fin m → A (1 : L)) →+ Matrix (Fin m) (Fin m) L :=
    { toFun := fun Y => Matrix.of fun i j => (Y i j : L)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have e : MA m (1 : L) = g.range := by
    ext X
    constructor
    · intro hX
      exact ⟨fun i j => ⟨X i j, mem_MA.mp hX i j⟩, rfl⟩
    · rintro ⟨Y, rfl⟩
      exact mem_MA.mpr fun i j => (Y i j).2
  have e2 : (MA m r).comap g = AddSubgroup.pi Set.univ fun _ => AddSubgroup.pi Set.univ fun _ =>
      (A r).addSubgroupOf (A (1 : L)) := by
    ext Y
    exact ⟨fun h i _ j _ => h i trivial j trivial, fun h i _ j _ => h i trivial j trivial⟩
  rw [e, ← AddSubgroup.index_comap, e2, AddSubgroup.index_pi]
  simp only [AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rfl

def NA (c : L →+* L) (m : ℕ) : AddSubgroup (Matrix (Fin m) (Fin m) L) where
  carrier := {X | (∀ i j, X i j ∈ intL L) ∧ ∀ i j, c (X i j) = -X j i}
  zero_mem' := ⟨fun _ _ => (intL L).zero_mem, fun _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨fun i j => (intL L).add_mem (hX.1 i j) (hY.1 i j), fun i j => by
    simp only [Matrix.add_apply, map_add, hX.2, hY.2, neg_add]⟩
  neg_mem' := fun {X} hX => ⟨fun i j => (intL L).neg_mem (hX.1 i j), fun i j => by
    simp only [Matrix.neg_apply, map_neg, hX.2]⟩

theorem c_int (h : IsUnramInv ϖ c q) {y : L} (hy : y ∈ intL L) : c y ∈ intL L := by
  rw [mem_int, h.2.1]; exact hy

theorem relIndex_NA_sq (h : IsUnramInv ϖ c q) (m : ℕ) (r : L) (hr : c r = r) :
    (MA m r).relIndex (NA c m) * (MA m r).relIndex (NA c m) = (MA m r).relIndex (MA m (1 : L)) := by
  obtain ⟨x, hx, hd⟩ := h.2.2.2.2.1
  have hd0 : c x - x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hd
    exact zero_ne_one hd
  have hd1 : x - c x ≠ 0 := fun h0 => hd0 (by linear_combination -h0)
  have hdi : (c x - x)⁻¹ ∈ intL L := by rw [mem_int, map_inv₀, hd, inv_one]
  let f : NA c m × NA c m →+ Matrix (Fin m) (Fin m) L :=
    { toFun := fun p => (p.1 : Matrix (Fin m) (Fin m) L) + x • (p.2 : Matrix (Fin m) (Fin m) L)
      map_zero' := by simp
      map_add' := fun p p' => by
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, smul_add]
        abel }
  have fa : ∀ p i j, f p i j = (p.1 : Matrix (Fin m) (Fin m) L) i j + x * (p.2 : Matrix (Fin m) (Fin m) L) i j :=
    fun _ _ _ => rfl
  have e : MA m (1 : L) = f.range := by
    ext X
    rw [mem_MA]
    simp only [one_mul]
    constructor
    · intro hX
      have hb : ∀ i j, -((c x - x)⁻¹ * (X i j + c (X j i))) ∈ intL L := fun i j =>
        (intL L).neg_mem ((intL L).mul_mem hdi ((intL L).add_mem (hX i j) (c_int h (hX j i))))
      refine ⟨(⟨Matrix.of fun i j => X i j - x * -((c x - x)⁻¹ * (X i j + c (X j i))), fun i j =>
          (intL L).sub_mem (hX i j) ((intL L).mul_mem hx (hb i j)), fun i j => ?_⟩,
        ⟨Matrix.of fun i j => -((c x - x)⁻¹ * (X i j + c (X j i))), hb, fun i j => ?_⟩), ?_⟩
      · simp only [Matrix.of_apply, map_sub, map_mul, map_neg, map_inv₀, map_add, h.1]
        rw [← neg_sub (c x) x, inv_neg]
        field_simp
        ring
      · simp only [Matrix.of_apply, map_sub, map_mul, map_neg, map_inv₀, map_add, h.1]
        rw [← neg_sub (c x) x, inv_neg]
        ring
      · ext i j
        rw [fa]
        simp
    · rintro ⟨p, rfl⟩ i j
      rw [fa]
      exact (intL L).add_mem (p.1.2.1 i j) ((intL L).mul_mem hx (p.2.2.1 i j))
  have e2 : (MA m r).comap f = ((MA m r).addSubgroupOf (NA c m)).prod ((MA m r).addSubgroupOf (NA c m)) := by
    ext p
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, mem_MA, fa]
    constructor
    · intro hp
      have hb : ∀ i j, r * (p.2 : Matrix (Fin m) (Fin m) L) i j ∈ intL L := fun i j => by
        have h1 := (intL L).neg_mem ((intL L).mul_mem hdi ((intL L).add_mem (hp i j) (c_int h (hp j i))))
        simp only [map_mul, map_add, hr, p.1.2.2, p.2.2.2] at h1
        convert h1 using 1
        field_simp
        ring
      refine ⟨fun i j => ?_, hb⟩
      have h1 := (intL L).sub_mem (hp i j) ((intL L).mul_mem hx (hb i j))
      convert h1 using 1
      ring
    · intro hp i j
      have h1 := (intL L).add_mem (hp.1 i j) ((intL L).mul_mem hx (hp.2 i j))
      convert h1 using 1
      ring
  rw [e, ← AddSubgroup.index_comap, e2, AddSubgroup.index_prod]
  rfl

theorem relIndex_NA (h : IsUnramInv ϖ c q) (m : ℕ) :
    (MA m (ϖ⁻¹ * ϖ⁻¹)).relIndex (NA c m) = q ^ (2 * m * m) := by
  have h1 := relIndex_NA_sq h m (ϖ⁻¹ * ϖ⁻¹) (by rw [map_mul, map_inv₀, h.2.2.1])
  rw [relIndex_MA, relIndex_two h] at h1
  apply Nat.mul_self_inj.mp
  rw [h1]
  ring

end PositivityTheory.Sph.M2.ZC

end
end

section
noncomputable section

namespace PositivityTheory.Sph.M2.ZC

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {c : L →+* L} {q : ℕ} {m : ℕ}

def IntM {α β : Type} (X : Matrix α β L) : Prop := ∀ i j, X i j ∈ intL L

theorem IntM.mul {α β γ : Type} [Fintype β] {X : Matrix α β L} {Y : Matrix β γ L} (hX : IntM X) (hY : IntM Y) :
    IntM (X * Y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem IntM.conjT (h : IsUnramInv ϖ c q) {α β : Type} {X : Matrix α β L} (hX : IntM X) : IntM (X.map c)ᵀ := by
  intro i j
  exact c_int h (hX j i)

theorem intM_one {α : Type} [DecidableEq α] : IntM (1 : Matrix α α L) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem intM_zero {α β : Type} : IntM (0 : Matrix α β L) := by
  intro i j
  exact zero_mem _

theorem intM_fromBlocks {α : Type} {a b c' d : Matrix α α L} :
    IntM (fromBlocks a b c' d) ↔ IntM a ∧ IntM b ∧ IntM c' ∧ IntM d := by
  constructor
  · intro hM
    exact ⟨fun i j => hM (Sum.inl i) (Sum.inl j), fun i j => hM (Sum.inl i) (Sum.inr j),
      fun i j => hM (Sum.inr i) (Sum.inl j), fun i j => hM (Sum.inr i) (Sum.inr j)⟩
  · rintro ⟨ha, hb, hc, hd⟩ i j
    rcases i with i | i <;> rcases j with j | j
    exacts [ha i j, hb i j, hc i j, hd i j]

theorem mem_IntGL {g : GL (Fin m ⊕ Fin m) L} : g ∈ IntGL L m ↔ IntM g.val ∧ IntM (g⁻¹).val := by
  constructor
  · intro hg
    obtain ⟨g', rfl⟩ := MonoidHom.mem_range.mp hg
    exact ⟨fun i j => (g'.val i j).2, fun i j => ((g'⁻¹).val i j).2⟩
  · rintro ⟨h1, h2⟩
    refine MonoidHom.mem_range.mpr
      ⟨⟨Matrix.of fun i j => ⟨g.val i j, h1 i j⟩, Matrix.of fun i j => ⟨(g⁻¹).val i j, h2 i j⟩, ?_, ?_⟩, ?_⟩
    · ext i j
      have e := congrFun (congrFun (Units.mul_inv g) i) j
      rw [Matrix.mul_apply] at e
      rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum]
      simp only [MulMemClass.coe_mul, Matrix.of_apply]
      rw [e, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · ext i j
      have e := congrFun (congrFun (Units.inv_mul g) i) j
      rw [Matrix.mul_apply] at e
      rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum]
      simp only [MulMemClass.coe_mul, Matrix.of_apply]
      rw [e, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · ext i j
      rfl

theorem inv_of_iso (h : IsUnramInv ϖ c q) {g : GL (Fin m ⊕ Fin m) L} (hg : Iso c (Wm L (Fin m)) (Wm L (Fin m)) g.val) :
    (g⁻¹).val = Wm L (Fin m) * (g.val.map c)ᵀ * Wm L (Fin m) := by
  have hcc : ∀ y, c (c y) = y := h.1
  have hW : (Wm L (Fin m)).map c = Wm L (Fin m) := by
    show (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).map c = fromBlocks 0 1 1 0
    rw [Matrix.fromBlocks_map]
    simp
  have hgg : (g.val.map c).map c = g.val := by
    rw [Matrix.map_map]
    ext i j
    exact hcc _
  have hg' : g.valᵀ * Wm L (Fin m) * g.val.map c = Wm L (Fin m) := hg
  have h2 : (g.val.map c)ᵀ * Wm L (Fin m) * g.val = Wm L (Fin m) := by
    have e := congrArg (fun M => M.map c) hg'
    rw [Matrix.map_mul, Matrix.map_mul, hW, hgg, Matrix.transpose_map] at e
    exact e
  apply Units.inv_eq_of_mul_eq_one_left
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (g.val.map c)ᵀ, h2, Wm_mul_self]

theorem mem_KPW (h : IsUnramInv ϖ c q) {g : GL (Fin m ⊕ Fin m) L} :
    g ∈ KPW L c m ↔ g ∈ GW L c m ∧ g.val.toBlocks₂₁ = 0 ∧ IntM g.val := by
  have hB : g ∈ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ g.val.toBlocks₂₁ = 0 := by
    show (g.val).BlockTriangular (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ _
    constructor
    · intro hb
      ext i j
      exact @hb (Sum.inr i) (Sum.inl j) (show (0:ℕ) < 1 from Nat.one_pos)
    · intro h0 i j hij
      rcases i with i | i <;> rcases j with j | j
      · exact absurd hij (lt_irrefl _)
      · exact absurd hij (Nat.not_lt_zero _)
      · exact congrFun (congrFun h0 i) j
      · exact absurd hij (lt_irrefl _)
  have hWint : IntM (Wm L (Fin m)) := by
    show IntM (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    exact intM_fromBlocks.mpr ⟨intM_zero, intM_one, intM_one, intM_zero⟩
  show g ∈ (GW L c m ⊓ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m))) ⊓ (GW L c m ⊓ IntGL L m) ↔ _
  simp only [Subgroup.mem_inf, hB, mem_IntGL]
  constructor
  · rintro ⟨⟨hG, hC⟩, -, hI, -⟩
    exact ⟨hG, hC, hI⟩
  · rintro ⟨hG, hC, hI⟩
    refine ⟨⟨hG, hC⟩, hG, hI, ?_⟩
    rw [inv_of_iso h hG]
    exact IntM.mul (IntM.mul hWint (IntM.conjT h hI)) hWint

theorem zW_mem (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) : zW L m x ∈ GW L c m := by
  have hcx : c (x : L) = x := by rw [hx]; exact h.2.2.1
  have hx0 : (x : L) ≠ 0 := x.ne_zero
  have hcx' : c (x : L)⁻¹ = (x : L)⁻¹ := by rw [map_inv₀, hcx]
  show (fromBlocks ((x : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 (((x⁻¹ : Lˣ) : L) • 1))ᵀ * fromBlocks 0 1 1 0 *
      (fromBlocks ((x : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 (((x⁻¹ : Lˣ) : L) • 1)).map c = fromBlocks 0 1 1 0
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Units.val_inv_eq_inv_val, Matrix.smul_one_eq_diagonal, Matrix.diagonal_map, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, hcx, hcx', hx0]

theorem conj_val (x : Lˣ) (g : GL (Fin m ⊕ Fin m) L) :
    ((zW L m x)⁻¹ * g * zW L m x).val = fromBlocks g.val.toBlocks₁₁ (((x : L)⁻¹ * (x : L)⁻¹) • g.val.toBlocks₁₂)
      (((x : L) * x) • g.val.toBlocks₂₁) g.val.toBlocks₂₂ := by
  have hx0 : (x : L) ≠ 0 := x.ne_zero
  have hg : g.val = fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂ g.val.toBlocks₂₁ g.val.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks _).symm
  show fromBlocks (((x⁻¹ : Lˣ) : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 ((x : L) • 1) * g.val *
      fromBlocks ((x : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 (((x⁻¹ : Lˣ) : L) • 1) = _
  conv_lhs => rw [hg]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Units.val_inv_eq_inv_val, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx0]

theorem mem_conj (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) {g : GL (Fin m ⊕ Fin m) L} :
    g ∈ (KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom ↔ g ∈ GW L c m ∧ g.val.toBlocks₂₁ = 0 ∧
      IntM g.val.toBlocks₁₁ ∧ IntM g.val.toBlocks₂₂ ∧ g.val.toBlocks₁₂ ∈ MA m (ϖ⁻¹ * ϖ⁻¹) := by
  have hz := zW_mem (m := m) h hx
  have key : g ∈ (KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom ↔
      (zW L m x)⁻¹ * g * zW L m x ∈ KPW L c m := by
    constructor
    · intro hg
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
      simpa [mul_assoc] using hk
    · intro hk
      exact Subgroup.mem_map.mpr ⟨_, hk, by simp [mul_assoc]⟩
  have hGW : (zW L m x)⁻¹ * g * zW L m x ∈ GW L c m ↔ g ∈ GW L c m := by
    constructor
    · intro h1
      have := (GW L c m).mul_mem ((GW L c m).mul_mem hz h1) ((GW L c m).inv_mem hz)
      simpa [mul_assoc] using this
    · intro h1
      exact (GW L c m).mul_mem ((GW L c m).mul_mem ((GW L c m).inv_mem hz) h1) hz
  have hp : ϖ ≠ 0 := pi_ne h
  rw [key, mem_KPW h, hGW, conj_val, Matrix.toBlocks_fromBlocks₂₁, intM_fromBlocks, hx]
  constructor
  · rintro ⟨hG, hC, hA, hB, -, hD⟩
    have hC' : g.val.toBlocks₂₁ = 0 := by
      rw [smul_eq_zero] at hC
      exact hC.resolve_left (mul_ne_zero hp hp)
    refine ⟨hG, hC', hA, hD, ?_⟩
    rw [mem_MA]
    intro i j
    exact hB i j
  · rintro ⟨hG, hC, hA, hD, hB⟩
    rw [mem_MA] at hB
    refine ⟨hG, by rw [hC, smul_zero], hA, fun i j => hB i j, by rw [hC, smul_zero]; exact intM_zero, hD⟩

theorem conj_le (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) :
    (KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom ≤ KPW L c m := by
  intro g hg
  rw [mem_conj h hx] at hg
  obtain ⟨hG, hC, hA, hD, hB⟩ := hg
  rw [mem_KPW h]
  refine ⟨hG, hC, ?_⟩
  rw [← Matrix.fromBlocks_toBlocks g.val, intM_fromBlocks]
  refine ⟨hA, ?_, by rw [hC]; exact intM_zero, hD⟩
  intro i j
  rw [mem_MA] at hB
  have hp : ϖ ≠ 0 := pi_ne h
  have e : g.val.toBlocks₁₂ i j = (ϖ * ϖ) * ((ϖ⁻¹ * ϖ⁻¹) * g.val.toBlocks₁₂ i j) := by
    field_simp
  rw [e]
  exact mul_mem (mul_mem (pi_int h) (pi_int h)) (hB i j)

def nU (X : Matrix (Fin m) (Fin m) L) : GL (Fin m ⊕ Fin m) L :=
  ⟨fromBlocks 1 X 0 1, fromBlocks 1 (-X) 0 1, by simp [fromBlocks_multiply, fromBlocks_one],
    by simp [fromBlocks_multiply, fromBlocks_one]⟩

theorem nU_mem (h : IsUnramInv ϖ c q) {X : Matrix (Fin m) (Fin m) L} (hX : X ∈ NA c m) : nU X ∈ KPW L c m := by
  obtain ⟨hXi, hXs⟩ := hX
  rw [mem_KPW h]
  refine ⟨?_, ?_, ?_⟩
  · show Iso c (Wm L (Fin m)) (Wm L (Fin m)) (fromBlocks 1 X 0 1)
    apply iso_n
    ext i j
    exact hXs i j
  · exact Matrix.toBlocks_fromBlocks₂₁ _ _ _ _
  · show IntM (fromBlocks 1 X 0 1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    exact intM_fromBlocks.mpr ⟨intM_one, hXi, intM_zero, intM_one⟩

def nHom (h : IsUnramInv ϖ c q) (m : ℕ) : Multiplicative (NA c m) →* KPW L c m where
  toFun X := ⟨nU (X.toAdd : NA c m).1, nU_mem h (X.toAdd : NA c m).2⟩
  map_one' := Subtype.ext (Units.ext (by simp [nU, fromBlocks_one]))
  map_mul' X Y := Subtype.ext (Units.ext (by simp [nU, fromBlocks_multiply, add_comm]))

theorem skew_of_iso (h : IsUnramInv ϖ c q) {a b d : Matrix (Fin m) (Fin m) L}
    (hg : Iso c (Wm L (Fin m)) (Wm L (Fin m)) (fromBlocks a b 0 d)) :
    (a.map c)ᵀ * d = 1 ∧ (b * (a.map c)ᵀ).map c = -(b * (a.map c)ᵀ)ᵀ := by
  have hcc : ∀ y, c (c y) = y := h.1
  have hmm : ∀ M : Matrix (Fin m) (Fin m) L, (M.map c).map c = M := by
    intro M
    rw [Matrix.map_map]
    ext i j
    exact hcc _
  have hg' : (fromBlocks a b 0 d)ᵀ * fromBlocks 0 1 1 0 * (fromBlocks a b 0 d).map c =
      (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := hg
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hg'
  simp only [Matrix.transpose_zero, Matrix.map_zero, map_zero, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add] at hg'
  obtain ⟨-, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp hg'
  have e1 : (a.map c)ᵀ * d = 1 := by
    have e := congrArg (fun M => M.map c) h12
    simp only [Matrix.map_mul, hmm, Matrix.map_one (⇑c) (map_zero c) (map_one c)] at e
    rw [← Matrix.transpose_map]
    exact e
  have hA : a.map c * dᵀ = 1 := mul_eq_one_comm.mp h21
  have hD : d.map c * aᵀ = 1 := mul_eq_one_comm.mp h12
  have h22' : dᵀ * b.map c = -(bᵀ * d.map c) := eq_neg_of_add_eq_zero_left h22
  refine ⟨e1, ?_⟩
  rw [Matrix.map_mul, Matrix.transpose_map, hmm, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc b.map c * aᵀ = a.map c * dᵀ * b.map c * aᵀ := by rw [hA, Matrix.one_mul]
    _ = a.map c * (dᵀ * b.map c) * aᵀ := by rw [Matrix.mul_assoc (a.map c)]
    _ = -(a.map c * bᵀ * (d.map c * aᵀ)) := by
      rw [h22']
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -(a.map c * bᵀ) := by rw [hD, Matrix.mul_one]

theorem cover (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) (k : KPW L c m) :
    ∃ X, (nHom h m X)⁻¹ * k ∈ ((KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom).subgroupOf (KPW L c m) := by
  have hk := (mem_KPW h).mp k.2
  obtain ⟨hG, hC, hI⟩ := hk
  obtain ⟨A, hA'⟩ : ∃ A, A = (k : GL (Fin m ⊕ Fin m) L).val.toBlocks₁₁ := ⟨_, rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B, B = (k : GL (Fin m ⊕ Fin m) L).val.toBlocks₁₂ := ⟨_, rfl⟩
  obtain ⟨D, hD'⟩ : ∃ D, D = (k : GL (Fin m ⊕ Fin m) L).val.toBlocks₂₂ := ⟨_, rfl⟩
  have hv : (k : GL (Fin m ⊕ Fin m) L).val = fromBlocks A B 0 D := by
    rw [hA', hB', hD', ← hC, Matrix.fromBlocks_toBlocks]
  have hiso : Iso c (Wm L (Fin m)) (Wm L (Fin m)) (fromBlocks A B 0 D) := by
    rw [← hv]
    exact hG
  obtain ⟨e1, e2⟩ := skew_of_iso h hiso
  have hIfb : IntM (fromBlocks A B 0 D) := by
    rw [← hv]
    exact hI
  obtain ⟨hA, hB, -, hD⟩ := intM_fromBlocks.mp hIfb
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix (Fin m) (Fin m) L, X = B * (A.map c)ᵀ := ⟨_, rfl⟩
  have hXNA : X ∈ NA c m := by
    refine ⟨?_, ?_⟩
    · rw [hXdef]
      exact IntM.mul hB (IntM.conjT h hA)
    · intro i j
      rw [hXdef]
      exact congrFun (congrFun e2 i) j
  have hXD : X * D = B := by
    rw [hXdef, Matrix.mul_assoc, e1, Matrix.mul_one]
  refine ⟨Multiplicative.ofAdd ⟨X, hXNA⟩, ?_⟩
  have hprod : (((nHom h m (Multiplicative.ofAdd ⟨X, hXNA⟩))⁻¹ * k : KPW L c m) :
      GL (Fin m ⊕ Fin m) L).val = fromBlocks A 0 0 D := by
    show fromBlocks 1 (-X) 0 1 * (k : GL (Fin m ⊕ Fin m) L).val = _
    rw [hv, Matrix.fromBlocks_multiply]
    simp [hXD]
  rw [Subgroup.mem_subgroupOf, mem_conj h hx, hprod, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₁₂]
  exact ⟨((nHom h m (Multiplicative.ofAdd ⟨X, hXNA⟩))⁻¹ * k).2.1.1, rfl, hA, hD, zero_mem _⟩

theorem comap_eq (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) :
    (((KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom).subgroupOf (KPW L c m)).comap (nHom h m) =
      ((MA m (ϖ⁻¹ * ϖ⁻¹)).addSubgroupOf (NA c m)).toSubgroup := by
  ext X
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_conj h hx]
  show _ ↔ ((Multiplicative.toAdd X : NA c m) : Matrix (Fin m) (Fin m) L) ∈ MA m (ϖ⁻¹ * ϖ⁻¹)
  have hv : ((nHom h m X : KPW L c m) : GL (Fin m ⊕ Fin m) L).val =
      fromBlocks 1 ((Multiplicative.toAdd X : NA c m) : Matrix (Fin m) (Fin m) L) 0 1 := rfl
  rw [hv, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂,
    Matrix.toBlocks_fromBlocks₁₂]
  constructor
  · rintro ⟨-, -, -, -, hM⟩
    exact hM
  · intro hM
    exact ⟨(nHom h m X).2.1.1, rfl, intM_one, intM_one, hM⟩

end PositivityTheory.Sph.M2.ZC

namespace PositivityTheory.Sph.M2

theorem zCount : ZCountSt := by
  intro L _ _ ϖ c q h m x hx
  refine ⟨ZC.conj_le h hx, ?_⟩
  show (((KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom).subgroupOf (KPW L c m)).index = q ^ (2 * m * m)
  rw [← ZC.index_comap_of_cover (ZC.nHom h m) _ (ZC.cover h hx), ZC.comap_eq h hx, AddSubgroup.index_toSubgroup]
  exact ZC.relIndex_NA h m

end PositivityTheory.Sph.M2

end
end

section
noncomputable section

namespace PositivityTheory.Sph.M2.GenA

open Matrix

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

theorem conj_eq (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) {g a b : GL n K} (h : g * a = b * g) : ψ a = ψ b := by
  have := congrArg ψ h
  rw [map_mul, map_mul, mul_comm] at this
  exact mul_right_cancel₀ (hpos g).ne' this

def dg : (n → Kˣ) →* GL n K where
  toFun D := ⟨diagonal fun i => (D i : K), diagonal fun i => (((D i)⁻¹ : Kˣ) : K),
    by simp [diagonal_mul_diagonal], by simp [diagonal_mul_diagonal]⟩
  map_one' := by ext1; simp
  map_mul' a b := by ext1; simp [diagonal_mul_diagonal]

theorem dg_val (D : n → Kˣ) : ((dg D : GL n K) : Matrix n n K) = diagonal fun i => (D i : K) := rfl

def tv {i j : n} (h : i ≠ j) (s : K) : GL n K :=
  ⟨transvection i j s, transvection i j (-s), by rw [transvection_mul_transvection_same i j h]; simp,
    by rw [transvection_mul_transvection_same i j h]; simp⟩

theorem tv_val {i j : n} (h : i ≠ j) (s : K) : ((tv h s : GL n K) : Matrix n n K) = transvection i j s := rfl

theorem tv_mul {i j : n} (h : i ≠ j) (s t : K) : tv h s * tv h t = tv h (s + t) := by
  ext1
  rw [Units.val_mul, tv_val, tv_val, tv_val, transvection_mul_transvection_same i j h]

theorem dg_tv {i j : n} (h : i ≠ j) (d : Kˣ) (s : K) :
    dg (Function.update 1 i d) * tv h s = tv h (d * s) * dg (Function.update 1 i d) := by
  ext a b
  rw [Units.val_mul, Units.val_mul, dg_val, tv_val, tv_val, diagonal_mul, mul_diagonal]
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single, of_apply]
  by_cases h1 : a = b
  · subst h1
    have : ¬ (i = a ∧ j = a) := fun e => h (e.1.trans e.2.symm)
    simp [this]
  · by_cases h2 : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h2
      simp [h1, Function.update_of_ne (Ne.symm h)]
    · simp [h1, h2]

theorem tv_one (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) {w : K} (h0 : w ≠ 0) (h1 : 1 + w ≠ 0) {i j : n} (h : i ≠ j)
    (s : K) : ψ (tv h s) = 1 := by
  have e1 := conj_eq ψ hpos (dg_tv h (Units.mk0 w h0) s)
  have e2 := conj_eq ψ hpos (dg_tv h (Units.mk0 _ h1) s)
  have e3 := congrArg ψ (tv_mul h s (w * s))
  simp only [Units.val_mk0] at e1 e2
  rw [map_mul, ← e1, show s + w * s = (1 + w) * s by ring, ← e2] at e3
  exact mul_left_cancel₀ (hpos _).ne' (e3.trans (mul_one _).symm)

theorem dg_perm (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) (σ : Equiv.Perm n) (D : n → Kˣ) :
    ψ (dg D) = ψ (dg fun i => D (σ i)) := by
  have hd : ((1 : Matrix n n K).submatrix σ id).det ≠ 0 := by
    rw [det_permute, det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
  refine conj_eq ψ hpos (g := GeneralLinearGroup.mkOfDetNeZero _ hd) ?_
  ext a b
  rw [Units.val_mul, Units.val_mul, dg_val, dg_val, diagonal_mul, mul_diagonal]
  show ((1 : Matrix n n K).submatrix σ id) a b * _ = _ * ((1 : Matrix n n K).submatrix σ id) a b
  simp only [submatrix_apply, id, Matrix.one_apply]
  split_ifs with e
  · simp [e]
  · simp

theorem dg_one (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) (hsc : ∀ u : Kˣ, ψ (dg fun _ => u) = 1) (D : n → Kˣ) :
    ψ (dg D) = 1 := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · rw [Subsingleton.elim D 1, map_one, map_one]
  have e1 : (∏ σ : Equiv.Perm n, fun i => D (σ i)) = fun _ => ∏ σ : Equiv.Perm n, D (σ i₀) := by
    funext i
    rw [Finset.prod_apply]
    refine Fintype.prod_equiv (Equiv.mulRight (Equiv.swap i i₀)) _ _ fun σ => ?_
    simp
  have e2 := hsc (∏ σ : Equiv.Perm n, D (σ i₀))
  rw [← e1, ← MonoidHom.comp_apply, map_prod] at e2
  simp only [MonoidHom.comp_apply, ← dg_perm ψ hpos _ D, Finset.prod_const, Finset.card_univ] at e2
  exact (pow_eq_one_iff_of_nonneg (hpos _).le Fintype.card_ne_zero).1 e2

theorem all_one (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) {w : K} (h0 : w ≠ 0) (h1 : 1 + w ≠ 0)
    (hsc : ∀ u : Kˣ, ψ (dg fun _ => u) = 1) (g : GL n K) : ψ g = 1 := by
  have key : ∀ M : Matrix n n K, M.det ≠ 0 → ∀ g : GL n K, (g : Matrix n n K) = M → ψ g = 1 := by
    intro M hM
    refine diagonal_transvection_induction_of_det_ne_zero
      (fun M => ∀ g : GL n K, (g : Matrix n n K) = M → ψ g = 1) M hM ?_ ?_ ?_
    · intro D hD g hg
      rw [det_diagonal] at hD
      have hD' : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      have : g = dg fun i => Units.mk0 (D i) (hD' i) := Units.ext hg
      rw [this]
      exact dg_one ψ hpos hsc _
    · intro t g hg
      have : g = tv t.hij t.c := Units.ext hg
      rw [this]
      exact tv_one ψ hpos h0 h1 _ _
    · intro A B hA hB pA pB g hg
      have : g = GeneralLinearGroup.mkOfDetNeZero A hA * GeneralLinearGroup.mkOfDetNeZero B hB := Units.ext hg
      rw [this, map_mul, pA _ rfl, pB _ rfl, one_mul]
  exact key _ (Matrix.GeneralLinearGroup.det_ne_zero g) g rfl

end PositivityTheory.Sph.M2.GenA

end
end

section
noncomputable section

namespace PositivityTheory.Sph.M2.GenB

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L} {m : ℕ}

theorem mem_PW {g : GL (Fin m ⊕ Fin m) L} : g ∈ PW L c m ↔
    Iso c (Wm L (Fin m)) (Wm L (Fin m)) (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) ∧
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₂₁ = 0 := by
  change g ∈ GW L c m ⊓ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ _
  rw [Subgroup.mem_inf]
  apply and_congr Iff.rfl
  change (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).BlockTriangular
    (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ _
  constructor
  · intro h
    ext i j
    exact h (show GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m) (Sum.inl j) <
      GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m) (Sum.inr i) from Nat.zero_lt_one)
  · intro h i j hij
    cases i with
    | inl i => exact absurd hij (Nat.not_lt_zero _)
    | inr i =>
      cases j with
      | inl j => exact congrFun (congrFun h i) j
      | inr j => exact absurd hij (lt_irrefl 1)

theorem lev_val (t : GL (Fin m) L) :
    ((lev L c m t : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) = levM L c m t := rfl

theorem lev_mem (hc : ∀ x, c (c x) = x) (t : GL (Fin m) L) : lev L c m t ∈ PW L c m := by
  rw [mem_PW, lev_val]
  refine ⟨?_, rfl⟩
  have h1 : (↑t : Matrix (Fin m) (Fin m) L)ᵀ * (↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
  have h2 : (↑t⁻¹ : Matrix (Fin m) (Fin m) L).map c * (↑t : Matrix (Fin m) (Fin m) L).map c = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero c) (map_one c)]
  have h3 : ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c).map c = (↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ := by
    ext i j
    simp [hc]
  have h4 : ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c)ᵀ = (↑t⁻¹ : Matrix (Fin m) (Fin m) L).map c := by
    rw [Matrix.transpose_map, Matrix.transpose_transpose]
  have hlev : levM L c m t = fromBlocks (↑t : Matrix (Fin m) (Fin m) L) 0 0
      ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c) := rfl
  have hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0 := rfl
  change (levM L c m t)ᵀ * Wm L (Fin m) * (levM L c m t).map c = Wm L (Fin m)
  rw [hlev, hW]
  simp only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, h3, h4,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero c), Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, h1, h2]

def un (X : Matrix (Fin m) (Fin m) L) : GL (Fin m ⊕ Fin m) L :=
  ⟨fromBlocks 1 X 0 1, fromBlocks 1 (-X) 0 1, by simp [fromBlocks_multiply, fromBlocks_one],
    by simp [fromBlocks_multiply, fromBlocks_one]⟩

theorem un_val (X : Matrix (Fin m) (Fin m) L) :
    ((un X : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) = fromBlocks 1 X 0 1 := rfl

theorem un_mem {X : Matrix (Fin m) (Fin m) L} (h : X.map c = -Xᵀ) : un X ∈ PW L c m := by
  rw [mem_PW, un_val]
  refine ⟨?_, rfl⟩
  have hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0 := rfl
  change (fromBlocks 1 X 0 1)ᵀ * Wm L (Fin m) * (fromBlocks 1 X 0 1).map c = Wm L (Fin m)
  rw [hW]
  simp only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, h,
    Matrix.transpose_zero, Matrix.transpose_one, Matrix.map_zero _ (map_zero c),
    Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.mul_neg, neg_add_cancel, neg_zero]

theorem un_mul (X Y : Matrix (Fin m) (Fin m) L) : un X * un Y = un (X + Y) := by
  ext1
  rw [Units.val_mul, un_val, un_val, un_val, fromBlocks_multiply]
  simp [add_comm]

theorem zW_val (x : Lˣ) : ((zW L m x : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) =
    fromBlocks ((x : L) • 1) 0 0 (((x⁻¹ : Lˣ) : L) • 1) := rfl

theorem zW_un (x : Lˣ) (X : Matrix (Fin m) (Fin m) L) :
    zW L m x * un X = un (((x : L) * x) • X) * zW L m x := by
  have hx : (↑x⁻¹ : L) * (↑x * ↑x) = ↑x := by rw [← mul_assoc, Units.inv_mul, one_mul]
  ext1
  simp only [Units.val_mul, zW_val, un_val, fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    smul_zero, hx]

theorem decomp (hc : ∀ x, c (c x) = x) {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) :
    ∃ (t : GL (Fin m) L) (X : Matrix (Fin m) (Fin m) L), X.map c = -Xᵀ ∧ p = lev L c m t * un X := by
  rw [mem_PW] at hp
  obtain ⟨hiso, h21⟩ := hp
  set P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L := (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) with hP
  have hPb : P = fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ 0 P.toBlocks₂₂ := by
    rw [← h21]
    exact (Matrix.fromBlocks_toBlocks P).symm
  have hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0 := rfl
  change Pᵀ * Wm L (Fin m) * P.map c = Wm L (Fin m) at hiso
  rw [hPb, hW] at hiso
  simp only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero c), Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.fromBlocks_inj] at hiso
  obtain ⟨-, h12, h21', h22⟩ := hiso
  set A := P.toBlocks₁₁ with hA
  set B := P.toBlocks₁₂ with hB
  set D := P.toBlocks₂₂ with hD
  have hDD : (D.map c).map c = D := by
    ext i j
    simp [hc]
  have hinv1 : (D.map c)ᵀ * A = 1 := by
    have := congrArg Matrix.transpose h12
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hinv2 : A * (D.map c)ᵀ = 1 := by
    first
    | exact mul_eq_one_comm.mp hinv1
    | exact Matrix.mul_eq_one_comm.mp hinv1
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hinv1
  refine ⟨⟨A, (D.map c)ᵀ, hinv2, hinv1⟩, (D.map c)ᵀ * B, ?_, ?_⟩
  · rw [Matrix.map_mul, Matrix.transpose_map, hDD, Matrix.transpose_mul, Matrix.transpose_transpose]
    exact eq_neg_of_add_eq_zero_left h22
  · ext1
    rw [Units.val_mul, lev_val, un_val]
    change P = _
    rw [hPb]
    change _ = fromBlocks (A : Matrix (Fin m) (Fin m) L) 0 0
      ((((⟨A, (D.map c)ᵀ, hinv2, hinv1⟩ : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L)ᵀ.map c) * _
    simp only [Units.inv_mk, Units.val_mk, Matrix.transpose_transpose, hDD, fromBlocks_multiply,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add,
      ← Matrix.mul_assoc, hinv2]

theorem mem_IntGL {g : GL (Fin m ⊕ Fin m) L}
    (h1 : ∀ i j, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j ∈ intL L)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j ∈ intL L) :
    g ∈ IntGL L m := by
  change g ∈ (Matrix.GeneralLinearGroup.map (intL L).subtype).range
  rw [MonoidHom.mem_range]
  let A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L) :=
    Matrix.of fun a b => ⟨(g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) a b, h1 a b⟩
  let B : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L) :=
    Matrix.of fun a b => ⟨((g⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) a b, h2 a b⟩
  have hinj : ∀ M N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L),
      M.map (intL L).subtype = N.map (intL L).subtype → M = N :=
    fun M N h => Matrix.map_injective Subtype.val_injective h
  have hA : A.map (intL L).subtype = (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := by
    ext a b; rfl
  have hB : B.map (intL L).subtype =
      ((g⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := by
    ext a b; rfl
  have hAB : A * B = 1 := hinj _ _ (by
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.mul_inv g)
  have hBA : B * A = 1 := hinj _ _ (by
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.inv_mul g)
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hA

end PositivityTheory.Sph.M2.GenB

end
end

section
noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

namespace GenC

open GenA GenB

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L} {m : ℕ}

theorem lev_sc_val (u : Lˣ) :
    ((lev L c m (dg fun _ => u) : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) =
      fromBlocks ((u : L) • 1) 0 0 (c ((u⁻¹ : Lˣ) : L) • 1) := by
  rw [lev_val, levM, ← map_inv, dg_val, dg_val]
  congr 1
  · ext i j; by_cases h : i = j <;> simp [h]
  · ext i j
    by_cases h : i = j
    · simp [h]
    · simp [h]

theorem lev_sc_int (hv : ∀ x, Valued.v (c x) = Valued.v x) {u : Lˣ} (hu : Valued.v (u : L) = 1) (i j) :
    ((lev L c m (dg fun _ => u) : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j ∈ intL L := by
  have h1 : (u : L) ∈ intL L := hu.le
  have h2 : c ((u⁻¹ : Lˣ) : L) ∈ intL L := by
    show Valued.v (c _) ≤ 1
    rw [hv, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  rw [lev_sc_val]
  rcases i with i | i <;> rcases j with j | j
  · rw [fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact h1
    · rw [mul_zero]; exact zero_mem _
  · exact zero_mem _
  · exact zero_mem _
  · rw [fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact h2
    · rw [mul_zero]; exact zero_mem _

theorem lev_sc_mem (hc : ∀ x, c (c x) = x) (hv : ∀ x, Valued.v (c x) = Valued.v x) {u : Lˣ}
    (hu : Valued.v (u : L) = 1) : lev L c m (dg fun _ => u) ∈ KPW L c m := by
  refine ⟨lev_mem hc _, (lev_mem hc _).1, mem_IntGL (lev_sc_int hv hu) ?_⟩
  rw [← map_inv, ← map_inv]
  exact lev_sc_int (u := u⁻¹) hv (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])

theorem lev_sc_eq {x : Lˣ} (hx : c x = x) : lev L c m (dg fun _ => x) = zW L m x := by
  ext1
  rw [lev_sc_val, zW_val, Units.val_inv_eq_inv_val, map_inv₀, hx]

theorem exists_unit {x : Lˣ} (hx : Valued.v (x : L) = WithZero.exp (-1 : ℤ)) (u : Lˣ) :
    ∃ k : ℤ, Valued.v ((u * x ^ k : Lˣ) : L) = 1 := by
  have h0 : Valued.v (u : L) ≠ 0 := (Valuation.ne_zero_iff _).2 u.ne_zero
  refine ⟨WithZero.log (Valued.v (u : L)), ?_⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, ← WithZero.exp_zsmul]
  conv_lhs => lhs; rw [← WithZero.exp_log h0]
  rw [← WithZero.exp_add]
  simp

theorem one_add_ne {y : L} (hy : Valued.v y < 1) : 1 + y ≠ 0 := fun e => by
  rw [eq_neg_of_add_eq_zero_right e, Valuation.map_neg, map_one] at hy
  exact lt_irrefl _ hy

end GenC

open GenA GenB GenC in
theorem gen : GenSt := by
  intro L _ _ ϖ c q h m χ hmul hpos hK hz a ha
  obtain ⟨hc, hv, hϖ, hvϖ, -⟩ := h
  have hvϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hvϖ
  have hlt : Valued.v ϖ < 1 := by
    rw [hvϖ', ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have h0 : ϖ ≠ 0 := fun e => by
    rw [e, map_zero] at hvϖ'; exact WithZero.exp_ne_zero hvϖ'.symm
  let x : Lˣ := Units.mk0 ϖ h0
  have hzx : χ (zW L m x) = 1 := hz x rfl
  have hzm : zW L m x ∈ PW L c m := by rw [← lev_sc_eq (c := c) (x := x) hϖ]; exact lev_mem hc _
  let ψ : GL (Fin m) L →* ℝ :=
    { toFun := fun t => χ (lev L c m t)
      map_one' := by rw [map_one]; exact hK 1 (one_mem _)
      map_mul' := fun s t => by rw [map_mul]; exact hmul _ (lev_mem hc _) _ (lev_mem hc _) }
  have hψ : ∀ t, ψ t = χ (lev L c m t) := fun _ => rfl
  have hsc : ∀ u : Lˣ, ψ (dg fun _ => u) = 1 := by
    let φ : Lˣ →* ℝ := (ψ.comp dg).comp (Pi.constMonoidHom (Fin m) Lˣ)
    have hφ : ∀ u, φ u = ψ (dg fun _ => u) := fun _ => rfl
    intro u
    obtain ⟨k, hk⟩ := exists_unit (x := x) hvϖ' u
    have e1 : φ (u * x ^ k) = 1 := by rw [hφ, hψ]; exact hK _ (lev_sc_mem hc hv hk)
    have e2 : φ x = 1 := by rw [hφ, hψ, lev_sc_eq (x := x) hϖ]; exact hzx
    have e3 : φ (x ^ k) = 1 := zpow_mem (show x ∈ φ.ker from e2) k
    rw [map_mul, e3, mul_one] at e1
    exact e1
  have hall := all_one ψ (fun t => hpos _ (lev_mem hc t)) h0 (one_add_ne hlt) hsc
  obtain ⟨t, X, hX, rfl⟩ := decomp hc ha
  have hr : 1 + -(ϖ * ϖ) ≠ 0 := one_add_ne (by
    rw [Valuation.map_neg, map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt hlt.le)
  have hs : ∀ r : L, c r = r → (r • X).map c = -(r • X)ᵀ := fun r hr => by
    ext i j
    have : c (X i j) = -X j i := congrFun (congrFun hX i) j
    simp [hr, this]
  set r := (1 + -(ϖ * ϖ))⁻¹ with hrd
  have hcr : c r = r := by simp [hrd, hϖ]
  have m1 := un_mem (hs r hcr)
  have m2 := un_mem (hs (ϖ * ϖ * r) (by simp [hcr, hϖ]))
  have m3 := un_mem hX
  have e1 := congrArg χ (zW_un x (r • X))
  rw [smul_smul] at e1
  have e2 : un (r • X) = un ((ϖ * ϖ * r) • X) * un X := by
    rw [un_mul]
    congr 1
    have : r = ϖ * ϖ * r + 1 := by
      have := mul_inv_cancel₀ hr
      rw [← hrd] at this
      linear_combination this
    conv_lhs => rw [this, add_smul, one_smul]
  have e3 : χ (un (r • X)) = χ (un ((ϖ * ϖ * r) • X)) := by
    rw [hmul _ hzm _ m1, hzx, one_mul] at e1
    rw [e1]
    exact (hmul _ m2 _ hzm).trans (by rw [hzx, mul_one])
  rw [e2, hmul _ m2 _ m3] at e3
  have e4 : χ (un X) = 1 := mul_left_cancel₀ (hpos _ m2).ne' (e3.trans (mul_one _).symm)
  rw [hmul _ (lev_mem hc t) _ m3, e4, mul_one]
  exact hall t

end PositivityTheory.Sph.M2

end
end

section
namespace PositivityTheory.Sph.M2

theorem locMod : LocModSt := locMod_of locComm zCount gen

end PositivityTheory.Sph.M2
end
