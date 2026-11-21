import Mathlib
import Formalism.PadicSubsetSums.StableGradedCounts.ConcreteDictionaryHolds
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.EigenUniformiser

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries

noncomputable abbrev Ia {O : Type*} [CommRing O] (a : O) : Ideal (PowerSeries O) := Ideal.span {X - C a}

theorem mk_X {O : Type*} [CommRing O] (a : O) : Ideal.Quotient.mk (Ia a) X = Ideal.Quotient.mk (Ia a) (C a) :=
  Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr dvd_rfl)

section Ev

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem map_residue_X_sub_C {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    (X - C a : PowerSeries O).map (IsLocalRing.residue O) = X := by
  rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero, sub_zero]

theorem order_map_X_sub_C {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    ((X - C a : PowerSeries O).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat = 1 := by
  change ((X - C a : PowerSeries O).map (IsLocalRing.residue O)).order.toNat = 1
  rw [map_residue_X_sub_C ha, PowerSeries.order_X]
  rfl

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem ev_exists {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) (f : PowerSeries O) :
    ∃ c : O, Ideal.Quotient.mk (Ia a) f = Ideal.Quotient.mk (Ia a) (C c) := by
  have hg : (X - C a : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    rw [map_residue_X_sub_C ha]
    exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hW⟩ := f.exists_isWeierstrassDivision hg
  obtain ⟨hdeg, heq⟩ := hW
  rw [order_map_X_sub_C ha] at hdeg
  have hr : r = Polynomial.C (r.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (by exact_mod_cast hdeg))
  refine ⟨r.coeff 0, ?_⟩
  rw [heq, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)),
    zero_add]
  congr 1
  conv_lhs => rw [hr]
  exact Polynomial.coe_C _

theorem ev_inj {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) {c c' : O}
    (h : Ideal.Quotient.mk (Ia a) (C c) = Ideal.Quotient.mk (Ia a) (C c')) : c = c' := by
  rw [Ideal.Quotient.eq, ← map_sub] at h
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp h
  have hrec : ∀ n, PowerSeries.coeff (R := O) n H = a * PowerSeries.coeff (R := O) (n + 1) H := by
    intro n
    have hn := congrArg (PowerSeries.coeff (R := O) (n + 1)) hH
    rw [PowerSeries.coeff_C, if_neg (by omega : n + 1 ≠ 0), sub_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul] at hn
    linear_combination -hn
  have hmem : ∀ n, PowerSeries.coeff (R := O) 0 H ∈ (IsLocalRing.maximalIdeal O) ^ n := by
    intro n
    have hpow : PowerSeries.coeff (R := O) 0 H = a ^ n * PowerSeries.coeff (R := O) n H := by
      induction n with
      | zero => simp
      | succ n ih => rw [ih, hrec n, pow_succ]; ring
    rw [hpow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha n)
  have h0 : PowerSeries.coeff (R := O) 0 H = 0 := by
    apply IsHausdorff.haus' (I := IsLocalRing.maximalIdeal O)
    intro n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact hmem n
  have hc := congrArg (PowerSeries.coeff (R := O) 0) hH
  rw [PowerSeries.coeff_zero_C, sub_mul, map_sub, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul, h0,
    mul_zero, sub_zero] at hc
  exact sub_eq_zero.mp hc

theorem ev_zero {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) {c : O}
    (h : Ideal.Quotient.mk (Ia a) (C c) = 0) : c = 0 := by
  exact ev_inj ha (by rw [h, map_zero, map_zero])

end Ev

theorem ev_subst {O : Type*} [CommRing O] {P : PowerSeries O} (hP : constantCoeff P = 0) {a b c : O}
    {F : PowerSeries O}
    (hPb : Ideal.Quotient.mk (Ideal.span {X - C a}) P = Ideal.Quotient.mk (Ideal.span {X - C a}) (C b))
    (hF : Ideal.Quotient.mk (Ideal.span {X - C b}) F = Ideal.Quotient.mk (Ideal.span {X - C b}) (C c)) :
    Ideal.Quotient.mk (Ideal.span {X - C a}) (PowerSeries.subst P F) =
      Ideal.Quotient.mk (Ideal.span {X - C a}) (C c) := by
  have hs : HasSubst P := HasSubst.of_constantCoeff_zero' hP
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton'] at hF
  obtain ⟨k, hk⟩ := hF
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hPb ⊢
  have e : PowerSeries.subst P F - C c = PowerSeries.subst P k * (P - C b) := by
    have := congrArg (PowerSeries.subst P) hk
    rw [subst_mul hs, subst_sub hs, subst_sub hs, subst_X hs, subst_C, subst_C] at this
    exact this.symm
  rw [e]; exact Ideal.mul_mem_left _ _ hPb

section Dvd

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsDomain O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]


theorem prod_dvd (T : Finset O) (hT : ∀ t ∈ T, t ∈ IsLocalRing.maximalIdeal O) (f : PowerSeries O)
    (hf : ∀ t ∈ T, Ideal.Quotient.mk (Ia t) f = 0) : (∏ t ∈ T, (X - C t)) ∣ f := by
  classical
  induction T using Finset.induction_on generalizing f with
  | empty => simp
  | @insert t0 T ht0 ih =>
    rw [Finset.prod_insert ht0]
    have h0 : (X - C t0) ∣ f :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (hf t0 (Finset.mem_insert_self _ _)))
    obtain ⟨g, rfl⟩ := h0
    apply mul_dvd_mul_left
    apply ih (fun t ht => hT t (Finset.mem_insert_of_mem ht))
    intro t ht
    have htm := hT t (Finset.mem_insert_of_mem ht)
    obtain ⟨c, hc⟩ := ev_exists htm g
    have hft := hf t (Finset.mem_insert_of_mem ht)
    have key : Ideal.Quotient.mk (Ia t) (C ((t - t0) * c)) = 0 := by
      rw [← hft]
      simp only [map_mul, map_sub, mk_X, hc]
    have hz := ev_zero htm key
    have hne : t - t0 ≠ 0 := sub_ne_zero.mpr (fun h => ht0 (h ▸ ht))
    have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_left hne
    rw [hc, hc0, map_zero, map_zero]

end Dvd

section Order

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem card_le_of_dvd {f v k : PowerSeries O} {s : ℕ} (T : Finset O)
    (hT : ∀ t ∈ T, t ∈ IsLocalRing.maximalIdeal O) (hv : IsUnit v)
    (hf : f.map (IsLocalRing.residue O) = (X ^ s * v).map (IsLocalRing.residue O))
    (hk : f = (∏ t ∈ T, (X - C t)) * k) :
    T.card ≤ s ∧ (T.card = s → IsUnit k) := by
  set κ := IsLocalRing.ResidueField O
  have hprod : (∏ t ∈ T, (X - C t) : PowerSeries O).map (IsLocalRing.residue O) = X ^ T.card := by
    rw [map_prod]
    rw [Finset.prod_congr rfl fun t ht => (map_residue_X_sub_C (hT t ht))]
    rw [Finset.prod_const]
  have e : (X : PowerSeries κ) ^ s * v.map (IsLocalRing.residue O) =
      X ^ T.card * k.map (IsLocalRing.residue O) := by
    rw [← map_X (IsLocalRing.residue O), ← map_pow, ← map_mul, ← hf, hk, map_mul, hprod, map_X]
  have hv' : constantCoeff (v.map (IsLocalRing.residue O)) ≠ 0 := by
    have := (hv.map (PowerSeries.map (IsLocalRing.residue O)))
    rw [isUnit_iff_constantCoeff] at this
    exact this.ne_zero
  have hX : (X : PowerSeries κ) ≠ 0 := X_ne_zero
  by_cases hle : T.card ≤ s
  · refine ⟨hle, fun hcs => ?_⟩
    rw [hcs] at e
    have e2 := mul_left_cancel₀ (pow_ne_zero _ hX) e
    rw [isUnit_iff_constantCoeff]
    by_contra hnu
    apply hv'
    rw [e2, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)]
  · exfalso
    replace hle := not_le.mp hle
    have e2 : (X : PowerSeries κ) ^ s * v.map (IsLocalRing.residue O) =
        X ^ s * (X ^ (T.card - s) * k.map (IsLocalRing.residue O)) := by
      rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle.le]
    have e3 := mul_left_cancel₀ (pow_ne_zero _ hX) e2
    apply hv'
    rw [e3, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), zero_mul]

end Order

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums

variable {l : ℕ} [hl : Fact l.Prime]



section O

variable {O : Type*} [CommRing O] [Algebra ℤ_[l] O] {a ζ : O}

local notation "toO" => PowerSeries.map (algebraMap ℤ_[l] O)








end O

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums Classical

variable {l : ℕ} [hl : Fact l.Prime]

theorem isUnit_of_toZMod_ne_zero {x : ℤ_[l]} (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal x).mpr (mem_nonunits_iff.mpr hx)
  rw [← PadicInt.ker_toZMod] at hm
  exact RingHom.mem_ker.mp hm

theorem natCast_ne_zero_zmod {n : ℕ} (h0 : 0 < n) (hn : n < l) : (n : ZMod l) ≠ 0 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt h0 hn ((CharP.cast_eq_zero_iff (ZMod l) l n).mp h)

theorem isUnit_natCast {n : ℕ} (h0 : 0 < n) (hn : n < l) : IsUnit (n : ℤ_[l]) := by
  apply isUnit_of_toZMod_ne_zero
  rw [map_natCast]
  exact natCast_ne_zero_zmod h0 hn

theorem toZMod_ne_zero_of_pow {s : ℕ} (hs : 0 < s) {ω : ℤ_[l]} (hω : ω ^ s = 1) :
    PadicInt.toZMod ω ≠ 0 := by
  intro h
  have h1 := congrArg PadicInt.toZMod hω
  rw [map_pow, h, zero_pow hs.ne', map_one] at h1
  exact zero_ne_one h1

theorem val_pos_of_pow {s : ℕ} (hs : 0 < s) {ω : ℤ_[l]} (hω : ω ^ s = 1) :
    0 < (PadicInt.toZMod ω).val := by
  exact ZMod.val_pos.mpr (toZMod_ne_zero_of_pow hs hω)

theorem val_lt (ω : ℤ_[l]) : (PadicInt.toZMod ω).val < l := ZMod.val_lt _


theorem natCast_l_ne_zero {O : Type*} [CommRing O] [IsDomain O] {ζ : O} (hζ : IsPrimitiveRoot ζ l) :
    ((l : ℕ) : O) ≠ 0 := by
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  exact (hζ.neZero').out

theorem algebraMap_injective {O : Type*} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    (hl0 : ((l : ℕ) : O) ≠ 0) : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  have hu := (PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[l] O)
  rcases mul_eq_zero.mp hx with h | h
  · exact hu.ne_zero h
  · exact absurd h (pow_ne_zero _ hl0)

theorem sub_one_mem {O : Type*} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {ζ : O}
    (hζ : IsPrimitiveRoot ζ l) (hmax : (algebraMap ℤ_[l] O) l ∈ IsLocalRing.maximalIdeal O) :
    ζ - 1 ∈ IsLocalRing.maximalIdeal O := by
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), ← map_natCast (algebraMap ℤ_[l] O)]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  have : CharP (IsLocalRing.ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl.out).mpr hl0
  have h2 : (IsLocalRing.residue O (ζ - 1)) ^ l = 0 := by
    rw [map_sub, map_one, sub_pow_char, ← map_pow, hζ.pow_eq_one, map_one, one_pow, sub_self]
  exact (IsLocalRing.residue_eq_zero_iff _).mp ((pow_eq_zero_iff hl.out.ne_zero).mp h2)

theorem pow_sub_one_mem {O : Type*} [CommRing O] [IsLocalRing O] {ζ : O}
    (h : ζ - 1 ∈ IsLocalRing.maximalIdeal O) (n : ℕ) : ζ ^ n - 1 ∈ IsLocalRing.maximalIdeal O := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow ζ 1 n
  rw [one_pow] at hc
  rw [hc]
  exact Ideal.mul_mem_right _ _ h

noncomputable instance instFintypeRoots (s : ℕ) [NeZero s] : Fintype (rootsOfUnity s ℤ_[l]) := Fintype.ofFinite _

theorem prod_roots {M : Type*} [CommMonoid M] (s : ℕ) [NeZero s] (hs : 0 < s) (f : ℤ_[l] → M) :
    ∏ δ : rootsOfUnity s ℤ_[l], f ((δ : ℤ_[l]ˣ) : ℤ_[l]) =
      ∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]), f ω := by
  rw [← Finset.prod_image (f := f) (s := Finset.univ)
    (g := fun δ : rootsOfUnity s ℤ_[l] => ((δ : ℤ_[l]ˣ) : ℤ_[l]))
    (by intro δ _ ε _ h; exact Subtype.ext (Units.ext h))]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Polynomial.mem_nthRootsFinset hs]
  constructor
  · rintro ⟨δ, rfl⟩
    have h1 := δ.2
    rw [mem_rootsOfUnity] at h1
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  · intro hx
    have hu : IsUnit x := IsUnit.of_pow_eq_one hx hs.ne'
    refine ⟨⟨hu.unit, ?_⟩, rfl⟩
    rw [mem_rootsOfUnity]; apply Units.ext; simp [hx]

section Act

variable {O : Type*} [CommRing O] [Algebra ℤ_[l] O]

local notation "toO" => PowerSeries.map (algebraMap ℤ_[l] O)

theorem toO_const_zero {a : PowerSeries ℤ_[l]} (ha : constantCoeff a = 0) : constantCoeff (toO a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, ha, map_zero]

theorem toO_brk_const (a : ℤ_[l]) : constantCoeff (toO (brk l a)) = 0 :=
  toO_const_zero (by rw [(Classical.choose_spec (ConcreteDictionaryLemmas.brk_factor a)).1, map_mul, constantCoeff_X, zero_mul])

theorem hasSubst_brk (a : ℤ_[l]) : HasSubst (toO (brk l a)) :=
  HasSubst.of_constantCoeff_zero (toO_brk_const a)

theorem toO_subst {a : PowerSeries ℤ_[l]} (ha : constantCoeff a = 0) (f : PowerSeries ℤ_[l]) :
    toO (subst a f) = subst (toO a) (toO f) :=
  map_subst (HasSubst.of_constantCoeff_zero' ha) f

theorem subst_brk_brk (a b : ℤ_[l]) (f : PowerSeries O) :
    subst (toO (brk l b)) (subst (toO (brk l a)) f) = subst (toO (brk l (a * b))) f := by
  rw [subst_comp_subst_apply (hasSubst_brk a) (hasSubst_brk b),
    ← toO_subst (ConcreteDictionaryLemmas.brk_const b), ConcreteDictionaryLemmas.brk_comp]

theorem brk_one : brk l (1 : ℤ_[l]) = X := by
  unfold brk
  rw [← Nat.cast_one, PowerSeries.binomialSeries_nat, pow_one, add_sub_cancel_left]

theorem subst_brk_one (f : PowerSeries O) : subst (toO (brk l 1)) f = f := by
  rw [brk_one, map_X, X_subst]

noncomputable def rhoE (δ : ℤ_[l]ˣ) : PowerSeries O ≃ₐ[O] PowerSeries O :=
  AlgEquiv.ofAlgHom (substAlgHom (hasSubst_brk (O := O) (δ : ℤ_[l])))
    (substAlgHom (hasSubst_brk (O := O) ((δ⁻¹ : ℤ_[l]ˣ) : ℤ_[l])))
    (AlgHom.ext fun f => by
      simp only [AlgHom.comp_apply, coe_substAlgHom, AlgHom.id_apply]
      rw [subst_brk_brk, ← Units.val_mul, inv_mul_cancel, Units.val_one, subst_brk_one])
    (AlgHom.ext fun f => by
      simp only [AlgHom.comp_apply, coe_substAlgHom, AlgHom.id_apply]
      rw [subst_brk_brk, ← Units.val_mul, mul_inv_cancel, Units.val_one, subst_brk_one])

theorem rhoE_apply (δ : ℤ_[l]ˣ) (f : PowerSeries O) : rhoE δ f = subst (toO (brk l δ)) f := by
  exact congrFun (coe_substAlgHom (hasSubst_brk (O := O) (δ : ℤ_[l]))) f

noncomputable def rhoHom (s : ℕ) : rootsOfUnity s ℤ_[l] →* (PowerSeries O ≃ₐ[O] PowerSeries O) where
  toFun δ := rhoE (δ : ℤ_[l]ˣ)
  map_one' := AlgEquiv.ext fun f => by
    rw [rhoE_apply]; simp only [OneMemClass.coe_one, Units.val_one, subst_brk_one, AlgEquiv.one_apply]
  map_mul' δ ε := AlgEquiv.ext fun f => by
    simp only [AlgEquiv.mul_apply, rhoE_apply, subst_brk_brk]
    congr 3
    simp only [MulMemClass.coe_mul, Units.val_mul]
    ring

theorem rhoHom_apply (s : ℕ) (δ : rootsOfUnity s ℤ_[l]) (f : PowerSeries O) :
    rhoHom s δ f = subst (toO (brk l ((δ : ℤ_[l]ˣ) : ℤ_[l]))) f :=
  rhoE_apply _ f

noncomputable def vS (a : ℤ_[l]) : PowerSeries ℤ_[l] := Classical.choose (ConcreteDictionaryLemmas.brk_factor a)

theorem brk_eq_X_mul (a : ℤ_[l]) : brk l a = X * vS a :=
  (Classical.choose_spec (ConcreteDictionaryLemmas.brk_factor a)).1

theorem vS_const (a : ℤ_[l]) : constantCoeff (vS a) = a :=
  (Classical.choose_spec (ConcreteDictionaryLemmas.brk_factor a)).2

variable [IsDomain O]

noncomputable def dataS (s : ℕ) [NeZero s] (hinj : Function.Injective (algebraMap ℤ_[l] O)) :
    EigenUniformiser.Data O (rootsOfUnity s ℤ_[l]) where
  ρ := rhoHom s
  ω := (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (rootsOfUnity s ℤ_[l]).subtype
  hω := by
    intro δ ε h
    apply Subtype.ext; apply Units.ext
    have h2 := congrArg Units.val h
    exact hinj h2
  v δ := toO (vS ((δ : ℤ_[l]ˣ) : ℤ_[l]))
  hv δ := by
    show rhoHom s δ X = _
    rw [rhoHom_apply, subst_X (hasSubst_brk _), brk_eq_X_mul, map_mul, map_X]
  hv0 δ := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, vS_const]
    rfl


theorem card_roots {s e : ℕ} [NeZero s] (hes : e * s = l - 1) : Fintype.card (rootsOfUnity s ℤ_[l]) = s := by
  obtain ⟨ω₀, hω₀⟩ := ConcreteDictionaryLemmas.exists_prim (l := l) e s hes
  rw [← Nat.card_eq_fintype_card]
  exact hω₀.card_rootsOfUnity

theorem isUnit_card {s e : ℕ} [NeZero s] (hes : e * s = l - 1) :
    IsUnit ((Fintype.card (rootsOfUnity s ℤ_[l]) : ℕ) : O) := by
  have hl2 := hl.out.two_le
  have hs0 : s ≠ 0 := NeZero.ne s
  have he0 : e ≠ 0 := by
    rintro rfl
    omega
  have hse : s ≤ e * s := Nat.le_mul_of_pos_left s (Nat.pos_of_ne_zero he0)
  have hsl : s < l := by
    generalize e * s = q at hes hse
    omega
  rw [card_roots hes]
  have hu := (isUnit_natCast (l := l) (Nat.pos_of_ne_zero hs0) hsl).map (algebraMap ℤ_[l] O)
  rwa [map_natCast] at hu

end Act

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums Classical

variable {l : ℕ} [hl : Fact l.Prime]




section Fiber

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra ℤ_[l] O]

local notation "toO" => PowerSeries.map (algebraMap ℤ_[l] O)

noncomputable def vp (l s : ℕ) [Fact l.Prime] (ζ : O) : O :=
  ∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]), (ζ ^ (PadicInt.toZMod ω).val - 1)

noncomputable def PRt (l : ℕ) (O : Type*) [CommRing O] [IsDomain O] : Finset O :=
  (Polynomial.nthRoots l (1 : O)).toFinset.filter fun z => IsPrimitiveRoot z l


theorem coprime_val {s : ℕ} (hs : 0 < s) {δ : ℤ_[l]} (hδ : δ ^ s = 1) :
    (PadicInt.toZMod δ).val.Coprime l :=
  ((Nat.Prime.coprime_iff_not_dvd hl.out).mpr
    (Nat.not_dvd_of_pos_of_lt (val_pos_of_pow hs hδ) (val_lt δ))).symm

theorem pow_eq_pow_val {ζ : O} (hζ : IsPrimitiveRoot ζ l) (n : ℕ) :
    ζ ^ n = ζ ^ ((n : ZMod l).val) := by
  conv_lhs => rw [← Nat.mod_add_div n l]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one, ZMod.val_natCast]

theorem vp_pow {s : ℕ} (hs : 0 < s) {ζ : O} (hζ : IsPrimitiveRoot ζ l) {δ : ℤ_[l]} (hδ : δ ^ s = 1) :
    vp l s (ζ ^ (PadicInt.toZMod δ).val) = vp l s ζ := by
  have : NeZero l := ⟨hl.out.ne_zero⟩
  unfold vp
  have key : ∀ ω : ℤ_[l], (ζ ^ (PadicInt.toZMod δ).val) ^ (PadicInt.toZMod ω).val =
      ζ ^ (PadicInt.toZMod (δ * ω)).val := by
    intro ω
    rw [← pow_mul, pow_eq_pow_val hζ, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      map_mul]
  simp_rw [key]
  have hμ : ∀ ω, ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]) ↔ ω ^ s = 1 := fun ω =>
    Polynomial.mem_nthRootsFinset hs 1
  have h02 : δ * δ ^ (s - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hs, hδ]
  refine Finset.prod_nbij' (fun ω => δ * ω) (fun ω => δ ^ (s - 1) * ω) ?_ ?_ ?_ ?_ ?_
  · intro ω hω; rw [hμ] at hω ⊢; rw [mul_pow, hω, hδ, one_mul]
  · intro ω hω
    rw [hμ] at hω ⊢
    rw [mul_pow, hω, ← pow_mul, mul_comm (s - 1) s, pow_mul, hδ, one_pow, one_mul]
  · intro ω _; rw [← mul_assoc, mul_comm (δ ^ (s - 1)) δ, h02, one_mul]
  · intro ω _; rw [← mul_assoc, h02, one_mul]
  · intro ω _; rfl




noncomputable def Tp (l s : ℕ) [Fact l.Prime] (ζ : O) : Finset O :=
  (Polynomial.nthRootsFinset s (1 : ℤ_[l])).image fun δ => ζ ^ (PadicInt.toZMod δ).val - 1




variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]




end Fiber

end DualFramesAlt.eigenRingInvariants
