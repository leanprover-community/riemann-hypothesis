import Mathlib
import GroundTheory.LocalFields.BrauerInductionInduced

section
noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section OneDim

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem eq_trace_smul_id_of_finrank_eq_one (h : finrank ℂ V = 1) (f : V →ₗ[ℂ] V) :
    f = LinearMap.trace ℂ V f • LinearMap.id := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ h
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).mp (by omega)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp h (f v)
  have hf : f = c • LinearMap.id := by
    ext w
    obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp h w
    simp [map_smul, ← hc]
  rw [hf, map_smul, LinearMap.trace_id, h]
  simp

end OneDim

section Comm

variable {G : Type*} [Group G] [IsMulCommutative G]

theorem IsIrrCharacter.exists_monoidHom {χ : G → ℂ} (h : IsIrrCharacter χ) :
    ∃ l : G →* ℂˣ, ∀ g, χ g = l g := by
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := h
  have h1 : finrank ℂ V = 1 := IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  have hmul : ∀ g k, ρ.character (g * k) = ρ.character g * ρ.character k := by
    intro g k
    have hg := eq_trace_smul_id_of_finrank_eq_one h1 (ρ g)
    have hk := eq_trace_smul_id_of_finrank_eq_one h1 (ρ k)
    simp only [Representation.character, map_mul]
    conv_lhs => rw [hg, hk]
    rw [smul_mul_smul, map_smul, Module.End.mul_eq_comp, LinearMap.id_comp, LinearMap.trace_id, h1]
    simp
  let f : G →* ℂ :=
    { toFun := ρ.character
      map_one' := by rw [char_one, h1]; simp
      map_mul' := hmul }
  exact ⟨f.toHomUnits, fun g ↦ rfl⟩

end Comm

section Values

variable {G : Type*} [Group G] [Fintype G]

theorem IsCharacter.exists_sum_zpow {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) :
    ∃ (m : (Subgroup.zpowers s → ℂ) → ℕ) (β : (Subgroup.zpowers s → ℂ) → ℂ),
      (∀ ψ, β ψ ^ orderOf s = 1) ∧
        ∀ a : ℤ, χ (s ^ a) = ∑ ψ ∈ irrChars (Subgroup.zpowers s), (m ψ : ℂ) * β ψ ^ a := by
  classical
  set C := Subgroup.zpowers s
  obtain ⟨m, hm⟩ := (hχ.comp C.subtype).exists_nat
  have hl : ∀ ψ ∈ irrChars C, ∃ l : C →* ℂˣ, ∀ c, ψ c = l c := fun ψ hψ ↦
    (mem_irrChars.mp hψ).exists_monoidHom
  choose! l hl using hl
  let s' : C := ⟨s, Subgroup.mem_zpowers s⟩
  refine ⟨m, fun ψ ↦ if ψ ∈ irrChars C then (l ψ s' : ℂ) else 1, fun ψ ↦ ?_, fun a ↦ ?_⟩
  · dsimp only
    split_ifs
    · rw [← Units.val_pow_eq_pow_val, ← map_pow]
      have : s' ^ orderOf s = 1 := by
        ext
        simp [s', pow_orderOf_eq_one]
      rw [this, map_one, Units.val_one]
    · exact one_pow _
  · have h := congrFun hm (s' ^ a)
    simp only [Function.comp_apply, Subgroup.coe_subtype, Subgroup.coe_zpow, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    refine Finset.sum_congr rfl fun ψ hψ ↦ ?_
    dsimp only
    rw [if_pos hψ, hl ψ hψ, map_zpow, Units.val_zpow_eq_zpow_val]

theorem IsCharacter.apply_mem_adjoin {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) {N : ℕ} [NeZero N]
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hN : orderOf s ∣ N) :
    χ s ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  obtain ⟨m, β, hβ, h⟩ := hχ.exists_sum_zpow s
  have hβN : ∀ ψ, β ψ ^ N = 1 := by
    intro ψ
    obtain ⟨k, hk⟩ := hN
    rw [hk, pow_mul, hβ, one_pow]
  have hmem : ∀ ψ, β ψ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
    intro ψ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (hβN ψ)
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _
  have h1 : χ s = ∑ ψ ∈ irrChars (Subgroup.zpowers s), (m ψ : ℂ) * β ψ := by
    simpa using h 1
  rw [h1]
  exact Subalgebra.sum_mem _ fun ψ _ ↦ Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hmem ψ)

theorem IsCharacter.apply_mem_adjoin_card {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Nat.card G)) : χ s ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  exact hχ.apply_mem_adjoin s hζ (orderOf_dvd_natCard s)

end Values

section Retraction

theorem exists_retraction_adjoin {ζ : ℂ} (hζ : IsIntegral ℤ ζ) :
    ∃ π : Algebra.adjoin ℤ ({ζ} : Set ℂ) →ₗ[ℤ] ℤ, π 1 = 1 := by
  let pb := Algebra.adjoin.powerBasis' hζ
  have hdim : 0 < pb.dim := pb.dim_pos
  refine ⟨pb.basis.coord ⟨0, hdim⟩, ?_⟩
  have h0 : pb.basis ⟨0, hdim⟩ = 1 := by
    rw [pb.coe_basis]
    simp
  rw [← h0, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

theorem exists_int_of_mul_eq_int {ζ : ℂ} (hζ : IsIntegral ℤ ζ) {a : ℂ}
    (ha : a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) {d k : ℤ} (hd : d ≠ 0) (h : (d : ℂ) * a = k) :
    ∃ z : ℤ, a = z ∧ d * z = k := by
  obtain ⟨π, hπ⟩ := exists_retraction_adjoin hζ
  let a' : Algebra.adjoin ℤ ({ζ} : Set ℂ) := ⟨a, ha⟩
  have h' : d • a' = k • (1 : Algebra.adjoin ℤ ({ζ} : Set ℂ)) := by
    apply Subtype.ext
    simp [a', h]
  have h'' := congrArg π h'
  rw [map_zsmul, map_zsmul, hπ, smul_eq_mul, smul_eq_mul, mul_one] at h''
  refine ⟨π a', ?_, h''⟩
  have hd' : (d : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hd
  apply mul_left_cancel₀ hd'
  rw [h, ← h'']
  push_cast
  ring

end Retraction

section Frobenius

variable {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
include hp

theorem exists_sum_pow_prime_pow_eq {ι : Type*} (s : Finset ι) (b : ι → R) (n : ℕ) :
    ∃ r : R, (∑ i ∈ s, b i) ^ p ^ n = ∑ i ∈ s, b i ^ p ^ n + p * r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp [zero_pow (pow_ne_zero n hp.ne_zero)]
  | insert a s ha ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hp (b a) (∑ i ∈ s, b i) n
    refine ⟨r + b a * (∑ i ∈ s, b i) * r', ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]
    ring

end Frobenius

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

variable {G : Type*} [Group G]

def IsElementaryAt (p : ℕ) (H : Subgroup G) : Prop :=
  ∃ C P : Subgroup G, C ≤ H ∧ P ≤ H ∧ IsCyclic C ∧ (Nat.card C).Coprime p ∧ IsPGroup p P ∧
    (∀ c ∈ C, ∀ y ∈ P, c * y = y * c) ∧ ∀ h ∈ H, ∃ c ∈ C, ∃ y ∈ P, h = c * y

def IsElementary (H : Subgroup G) : Prop := ∃ p : ℕ, p.Prime ∧ IsElementaryAt p H

variable [Finite G] {p : ℕ}

theorem exists_zpow_mul_zpow_eq (hp : p.Prime) (s : G) :
    ∃ a b : ℤ, s ^ a * s ^ b = s ∧ (orderOf (s ^ a)).Coprime p ∧
      (s ^ b) ^ (p ^ (orderOf s).factorization p) = 1 := by
  set o := orderOf s
  have ho : o ≠ 0 := (orderOf_pos s).ne'
  set k := o.factorization p
  set r := o / p ^ k
  have hor : p ^ k * r = o := Nat.ordProj_mul_ordCompl_eq_self o p
  have hr : r.Coprime p := (Nat.coprime_ordCompl hp ho).symm
  have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (r : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left k hr.symm)
  obtain ⟨u, v, huv⟩ := hcop
  have hso : s ^ (o : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  refine ⟨u * (p ^ k : ℕ), v * r, ?_, ?_, ?_⟩
  · rw [← zpow_add, huv, zpow_one]
  · have h1 : (s ^ (u * (p ^ k : ℕ) : ℤ)) ^ r = 1 := by
      rw [← zpow_natCast, ← zpow_mul, show u * ((p ^ k : ℕ) : ℤ) * (r : ℤ) = u * (o : ℤ) by
        rw [← hor]; push_cast; ring, zpow_mul', hso, one_zpow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1) hr
  · rw [← zpow_natCast, ← zpow_mul, show v * (r : ℤ) * ((p ^ k : ℕ) : ℤ) = v * (o : ℤ) by
      rw [← hor]; push_cast; ring, zpow_mul', hso, one_zpow]

theorem isElementaryAt_zpowers (hp : p.Prime) (s : G) : IsElementaryAt p (Subgroup.zpowers s) := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_zpow_mul_zpow_eq hp s
  refine ⟨Subgroup.zpowers (s ^ a), Subgroup.zpowers (s ^ b), ?_, ?_, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.zpow_mem_zpowers s a
  · rw [Subgroup.zpowers_le]
    exact Subgroup.zpow_mem_zpowers s b
  · rwa [Nat.card_zpowers]
  · intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨(orderOf s).factorization p, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
  · intro c hc y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add, add_comm]
  · intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine ⟨(s ^ a) ^ m, Subgroup.zpow_mem_zpowers _ m, (s ^ b) ^ m, Subgroup.zpow_mem_zpowers _ m, ?_⟩
    have hab' : s ^ (a + b) = s := by rw [zpow_add, hab]
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← add_mul, zpow_mul, hab']

omit [Finite G] in

theorem IsElementaryAt.mono {H L : Subgroup G} (hH : IsElementaryAt p H) (hLH : L ≤ H) :
    IsElementaryAt p L := by
  obtain ⟨C, P, hCH, hPH, hC, hCp, hP, hcomm, hdec⟩ := hH
  refine ⟨L ⊓ C, L ⊓ P, inf_le_left, inf_le_left, Subgroup.isCyclic_of_le inf_le_right, ?_,
    hP.to_le inf_le_right, fun c hc y hy ↦ hcomm c hc.2 y hy.2, ?_⟩
  · exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_right) hCp
  · intro l hl
    obtain ⟨c, hc, y, hy, rfl⟩ := hdec l (hLH hl)
    obtain ⟨j, hj⟩ := hP ⟨y, hy⟩
    have hyj : y ^ p ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hoc : orderOf c ∣ Nat.card C := by
      rw [← Subgroup.orderOf_mk c hc]
      exact orderOf_dvd_natCard _
    have hcop : (orderOf c).Coprime (p ^ j) :=
      Nat.Coprime.pow_right j (Nat.Coprime.coprime_dvd_left hoc hCp)
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hcy : Commute c y := hcomm c hc y hy
    have hpow : (c * y) ^ (v * ((p ^ j : ℕ) : ℤ)) = c := by
      rw [hcy.mul_zpow, zpow_mul' y, zpow_natCast y, hyj, one_zpow, mul_one,
        show v * ((p ^ j : ℕ) : ℤ) = 1 - u * (orderOf c : ℤ) by rw [← huv]; ring, zpow_sub, zpow_one,
        zpow_mul', zpow_natCast c, pow_orderOf_eq_one, one_zpow, inv_one, mul_one]
    have hcL : c ∈ L := hpow ▸ L.zpow_mem hl _
    have hyL : y ∈ L := by
      have := L.mul_mem (L.inv_mem hcL) hl
      rwa [inv_mul_cancel_left] at this
    exact ⟨c, ⟨hcL, hc⟩, y, ⟨hyL, hy⟩, rfl⟩

theorem IsElementaryAt.isNilpotent (hp : p.Prime) {H : Subgroup G} (hH : IsElementaryAt p H) :
    Group.IsNilpotent H := by
  obtain ⟨C, P, hCH, hPH, hC, hCp, hP, hcomm, hdec⟩ := hH
  have : Fact p.Prime := ⟨hp⟩
  let C' : Subgroup H := C.subgroupOf H
  have hCcomm : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c := by
    intro c hc c' hc'
    have := hC.commGroup.mul_comm ⟨c, hc⟩ ⟨c', hc'⟩
    exact congrArg Subtype.val this
  have hcent : C' ≤ Subgroup.center H := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨c0, hc0, y0, hy0, hh⟩ := hdec h h.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hh]
    have hc' : (c : G) ∈ C := hc
    have key : (c : G) * (c0 * y0) = (c0 * y0) * c := by
      rw [← mul_assoc, hCcomm c hc' c0 hc0, mul_assoc, hcomm c hc' y0 hy0, mul_assoc]
    first
    | exact key
    | exact key.symm
  have hnorm : C'.Normal := ⟨fun n hn g ↦ by
    have := Subgroup.mem_center_iff.mp (hcent hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩
  have hQ : IsPGroup p (H ⧸ C') := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c0, hc0, y0, hy0, hh⟩ := hdec h h.2
    obtain ⟨j, hj⟩ := hP ⟨y0, hy0⟩
    refine ⟨j, ?_⟩
    have hyj : y0 ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hmk : (QuotientGroup.mk h : H ⧸ C') = QuotientGroup.mk ⟨y0, hPH hy0⟩ := by
      rw [QuotientGroup.eq]
      change ((h⁻¹ * ⟨y0, hPH hy0⟩ : H) : G) ∈ C
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hh, mul_inv_rev, mul_assoc, hcomm _ (C.inv_mem hc0) y0 hy0, inv_mul_cancel_left]
      exact C.inv_mem hc0
    rw [hmk, ← QuotientGroup.mk_pow]
    have : (⟨y0, hPH hy0⟩ : H) ^ p ^ j = 1 := Subtype.ext (by simpa using hyj)
    rw [this, QuotientGroup.mk_one]
  have hnil : Group.IsNilpotent (H ⧸ C') := hQ.isNilpotent
  exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' C')
    (by rw [QuotientGroup.ker_mk']; exact hcent)

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

section OneDim

variable {K : Type*} [Group K]

theorem isCharacter_monoidHom (l : K →* ℂˣ) : IsCharacter (fun k ↦ (l k : ℂ)) := by
  let ρ : Representation ℂ K ℂ :=
    { toFun := fun k ↦ (l k : ℂ) • LinearMap.id
      map_one' := by simp; rfl
      map_mul' := fun k k' ↦ by
        ext
        simp [mul_comm] }
  refine ⟨ℂ, inferInstance, inferInstance, inferInstance, ρ, ?_⟩
  funext k
  simp [Representation.character, ρ, LinearMap.trace_id]

end OneDim

variable {G : Type*} [Group G] [Fintype G]

def indLin (K : Subgroup G) (l : K →* ℂˣ) : G → ℂ := indFun K.subtype (fun k ↦ (l k : ℂ))

theorem IsCharacter.indLin (K : Subgroup G) (l : K →* ℂˣ) : IsCharacter (indLin K l) :=
  (isCharacter_monoidHom l).indFun K.subtype

section Transport

variable {H H' : Type*} [Group H] [Fintype H] [Group H'] [Fintype H']

theorem indFun_comp_toMonoidHom (φ : H →* G) (e : H' ≃* H) (ψ : H → ℂ) :
    indFun (φ.comp e.toMonoidHom) (ψ ∘ e) = indFun φ ψ := by
  classical
  funext s
  simp only [indFun_apply]
  rw [Nat.card_congr e.toEquiv]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  exact Fintype.sum_equiv e.toEquiv _ _ fun h' ↦ by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    exact if_congr Iff.rfl rfl rfl

theorem indFun_subtype_indLin (K : Subgroup G) (L : Subgroup K) (μ : L →* ℂˣ) :
    indFun K.subtype (indLin L μ) = indLin (L.map K.subtype)
      (μ.comp (L.equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom) := by
  set e := L.equivMapOfInjective K.subtype K.subtype_injective
  rw [indLin, indFun_indFun, indLin, ← indFun_comp_toMonoidHom _ e]
  congr 1
  ext l
  simp [e]

end Transport

section Spans

variable (E : Subgroup G → Prop)

def monomialSet : Set (G → ℂ) := {f | ∃ K : Subgroup G, E K ∧ ∃ l : K →* ℂˣ, f = indLin K l}

def spanZ : Submodule ℤ (G → ℂ) := Submodule.span ℤ (monomialSet E)

def spanA (ζ : ℂ) : Submodule ℤ (G → ℂ) :=
  Submodule.span ℤ {f | ∃ a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ), ∃ g ∈ spanZ E, f = a • g}

variable {E}

theorem indLin_mem_spanZ {K : Subgroup G} (hK : E K) (l : K →* ℂˣ) : indLin K l ∈ spanZ E :=
  Submodule.subset_span ⟨K, hK, l, rfl⟩


theorem smul_mem_spanA {ζ : ℂ} {a : ℂ} (ha : a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) {g : G → ℂ}
    (hg : g ∈ spanZ E) : a • g ∈ spanA E ζ :=
  Submodule.subset_span ⟨a, ha, g, hg, rfl⟩

theorem spanZ_mono {E' : Subgroup G → Prop} (h : ∀ K, E K → E' K) : spanZ E ≤ spanZ E' :=
  Submodule.span_mono fun _ ⟨K, hK, l, hf⟩ ↦ ⟨K, h K hK, l, hf⟩

theorem smul_mem_spanA_of_mem {ζ : ℂ} {a : ℂ} (ha : a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) {f : G → ℂ}
    (hf : f ∈ spanA E ζ) : a • f ∈ spanA E ζ := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, g, hg, rfl⟩ := hy
    rw [smul_smul]
    exact smul_mem_spanA (Subalgebra.mul_mem _ ha hb) hg
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ n hx

theorem isClassFun_of_mem_spanZ {f : G → ℂ} (hf : f ∈ spanZ E) : IsClassFun f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, -, l, rfl⟩ := hx
    exact isClassFun_indFun _ _
  | zero => intro g h; rfl
  | add x y _ _ hx hy => intro g h; simp [hx g h, hy g h]
  | smul n x _ hx => intro g h; simp [hx g h]

theorem isClassFun_of_mem_spanA {ζ : ℂ} {f : G → ℂ} (hf : f ∈ spanA E ζ) : IsClassFun f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, g, hg, rfl⟩ := hx
    intro s t
    simp [isClassFun_of_mem_spanZ hg s t]
  | zero => intro g h; rfl
  | add x y _ _ hx hy => intro g h; simp [hx g h, hy g h]
  | smul n x _ hx => intro g h; simp [hx g h]

theorem exists_int_charInner_of_mem_spanZ {f : G → ℂ} (hf : f ∈ spanZ E) {ψ : G → ℂ}
    (hψ : IsIrrCharacter ψ) : ∃ k : ℤ, charInner G f ψ = k := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, -, l, rfl⟩ := hx
    obtain ⟨n, hn⟩ := (IsCharacter.indLin K l).exists_nat_charInner hψ.isCharacter
    exact ⟨n, by rw [hn]; simp⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, LinearMap.add_apply, ha, hb]; push_cast; ring⟩
  | smul n x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨n * a, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, LinearMap.smul_apply, ha, smul_eq_mul]
    push_cast
    ring

end Spans

section Mono

variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hE hmono

theorem indFun_mem_spanZ {K : Subgroup G} (hK : E K) {χ : K → ℂ} (hχ : IsCharacter χ) :
    indFun K.subtype χ ∈ spanZ E := by
  classical
  obtain ⟨m, hm⟩ := hχ.exists_nat
  rw [hm, map_sum]
  refine Submodule.sum_mem _ fun ψ hψ ↦ ?_
  obtain ⟨L, μ, hLμ⟩ := hmono K hK ψ (mem_irrChars.mp hψ)
  rw [map_smul, Nat.cast_smul_eq_nsmul ℂ, hLμ, indFun_subtype_indLin]
  exact Submodule.smul_of_tower_mem _ _
    (indLin_mem_spanZ (hE K _ hK (Subgroup.map_subtype_le L)) _)

theorem mul_mem_spanZ {χ : G → ℂ} (hχ : IsCharacter χ) {f : G → ℂ} (hf : f ∈ spanZ E) :
    χ * f ∈ spanZ E := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, hK, l, rfl⟩ := hx
    rw [mul_comm, indLin, ← indFun_mul_comp _ _ hχ.isClassFun]
    exact indFun_mem_spanZ hE hmono hK ((isCharacter_monoidHom l).mul (hχ.comp K.subtype))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ n hx

theorem mul_mem_spanZ_of_mem {f g : G → ℂ} (hf : f ∈ spanZ E) (hg : g ∈ spanZ E) :
    f * g ∈ spanZ E := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, hK, l, rfl⟩ := hx
    exact mul_mem_spanZ hE hmono (IsCharacter.indLin K l) hg
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ n hx

theorem mul_mem_spanA_of_mem_spanZ {ζ : ℂ} {f g : G → ℂ} (hf : f ∈ spanA E ζ) (hg : g ∈ spanZ E) :
    f * g ∈ spanA E ζ := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, g', hg', rfl⟩ := hx
    rw [smul_mul_assoc]
    exact smul_mem_spanA ha (mul_mem_spanZ_of_mem hE hmono hg' hg)
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ n hx

theorem mul_mem_spanA {ζ : ℂ} {f g : G → ℂ} (hf : f ∈ spanA E ζ) (hg : g ∈ spanA E ζ) :
    f * g ∈ spanA E ζ := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, g', hg', rfl⟩ := hx
    rw [mul_smul_comm]
    exact smul_mem_spanA_of_mem ha (mul_mem_spanA_of_mem_spanZ hE hmono hf hg')
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ n hx

theorem pow_mem_spanA {ζ : ℂ} {f : G → ℂ} (hf : f ∈ spanA E ζ) {M : ℕ} (hM : M ≠ 0) :
    f ^ M ∈ spanA E ζ := by
  induction M with
  | zero => exact absurd rfl hM
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with rfl | hM'
    · simpa using hf
    · rw [pow_succ]
      exact mul_mem_spanA hE hmono (ih hM'.ne') hf

end Mono

section Descent

variable {E : Subgroup G → Prop}

theorem mem_spanZ_of_mem_spanA {ζ : ℂ} (hζ : IsIntegral ℤ ζ) {f : G → ℂ} (hf : f ∈ spanA E ζ)
    (hint : ∀ ψ ∈ irrChars G, ∃ k : ℤ, charInner G f ψ = k) : f ∈ spanZ E := by
  obtain ⟨π, hπ⟩ := exists_retraction_adjoin hζ
  obtain ⟨n, c, x, hx⟩ := (Submodule.mem_span_set').mp hf
  have hS : ∀ i, ∃ a : Algebra.adjoin ℤ ({ζ} : Set ℂ), ∃ g ∈ spanZ E,
      (x i : G → ℂ) = (a : ℂ) • g := fun i ↦ by
    obtain ⟨a, ha, g, hg, h⟩ := (x i).2
    exact ⟨⟨a, ha⟩, g, hg, h⟩
  choose a g hg hxag using hS
  set f' : G → ℂ := ∑ i, (c i * π (a i)) • g i with hf'def
  have hf' : f' ∈ spanZ E := Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hg i)
  have hfeq : f = ∑ i, c i • ((a i : ℂ) • g i) := by
    rw [← hx]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hxag i]
  suffices f = f' by rw [this]; exact hf'
  apply eq_of_isClassFun_of_charInner (isClassFun_of_mem_spanA hf) (isClassFun_of_mem_spanZ hf')
  intro ψ hψ
  obtain ⟨k, hk⟩ := hint ψ hψ
  have hn : ∀ i, ∃ m : ℤ, charInner G (g i) ψ = m := fun i ↦
    exists_int_charInner_of_mem_spanZ (hg i) (mem_irrChars.mp hψ)
  choose m hm using hn
  have h1 : charInner G f ψ = ∑ i, ((c i * m i : ℤ) : ℂ) * (a i : ℂ) := by
    rw [hfeq, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hm i,
      smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  have hA : (∑ i, (c i * m i) • a i) = k • (1 : Algebra.adjoin ℤ ({ζ} : Set ℂ)) := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, zsmul_eq_mul, mul_one]
    push_cast
    rw [← hk, h1]
    push_cast
    rfl
  have hπA := congrArg π hA
  rw [map_sum, map_zsmul, hπ, smul_eq_mul, mul_one] at hπA
  simp only [map_zsmul, smul_eq_mul] at hπA
  rw [hk, hf'def, map_sum, LinearMap.sum_apply]
  rw [← hπA]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, LinearMap.smul_apply, hm i, smul_eq_mul]
  push_cast
  ring

end Descent

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

universe u

variable {G : Type u} [Group G] [Fintype G]

section ClassCount

def classCount (s : G) (g : G) : ℂ := ∑ t : G, if t⁻¹ * g * t = s then 1 else 0

theorem indFun_zpowers_delta (s : G) :
    indFun (Subgroup.zpowers s).subtype
      (fun c ↦ if c = ⟨s, Subgroup.mem_zpowers s⟩ then (Nat.card (Subgroup.zpowers s) : ℂ) else 0) =
      classCount s := by
  funext g
  have hN : (Nat.card (Subgroup.zpowers s) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [indFun_apply, classCount, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have hin : ∀ c : Subgroup.zpowers s, (if (Subgroup.zpowers s).subtype c = t⁻¹ * g * t then
      (if c = ⟨s, Subgroup.mem_zpowers s⟩ then (Nat.card (Subgroup.zpowers s) : ℂ) else 0) else 0) =
      if c = ⟨s, Subgroup.mem_zpowers s⟩ then
        (if t⁻¹ * g * t = s then (Nat.card (Subgroup.zpowers s) : ℂ) else 0) else 0 := by
    intro c
    by_cases hc : c = ⟨s, Subgroup.mem_zpowers s⟩
    · subst hc
      simp only [Subgroup.coe_subtype, if_true]
      by_cases h : s = t⁻¹ * g * t
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    · simp [hc]
  rw [Finset.sum_congr rfl fun c _ ↦ hin c, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  split_ifs
  · field_simp
  · simp

variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
  (hcyc : ∀ s : G, E (Subgroup.zpowers s))
  {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))

include hE hmono hcyc hζ in

theorem classCount_mem_spanA (s : G) : classCount s ∈ spanA E ζ := by
  set C := Subgroup.zpowers s
  set s' : C := ⟨s, Subgroup.mem_zpowers s⟩
  set δ : C → ℂ := fun c ↦ if c = s' then (Nat.card C : ℂ) else 0
  have hcomm : ∀ a b : C, a * b = b * a := fun a b ↦
    (Subgroup.zpowers_isMulCommutative s).is_comm.comm a b
  have hδ : IsClassFun δ := by
    intro g h
    simp only [δ]
    rw [hcomm h g, mul_inv_cancel_right]
  have hN : (Nat.card C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcoef : ∀ ψ : C → ℂ, charInner C δ ψ = ψ s'⁻¹ := by
    intro ψ
    rw [charInner_apply]
    simp only [δ, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  rw [← indFun_zpowers_delta]
  change indFun C.subtype δ ∈ spanA E ζ
  rw [eq_sum_irrChars_of_isClassFun hδ, map_sum]
  refine Submodule.sum_mem _ fun ψ hψ ↦ ?_
  rw [map_smul, hcoef]
  refine smul_mem_spanA ?_ (indFun_mem_spanZ hE hmono (hcyc s) (mem_irrChars.mp hψ).isCharacter)
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  refine (mem_irrChars.mp hψ).isCharacter.apply_mem_adjoin _ hζ ?_
  rw [← Subgroup.orderOf_coe]
  exact orderOf_dvd_natCard _

end ClassCount

section Divisible

theorem card_smul_eq_sum_classCount {F : G → ℂ} (hF : IsClassFun F) :
    (Nat.card G : ℂ) • F = ∑ s : G, F s • classCount s := by
  funext g
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, classCount, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ t : G, ∑ s : G, F s * (if t⁻¹ * g * t = s then 1 else 0) = F g := by
    intro t
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    simpa using hF g t⁻¹
  rw [Finset.sum_congr rfl fun t _ ↦ h t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
  (hcyc : ∀ s : G, E (Subgroup.zpowers s))
  {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))

include hE hmono hcyc hζ in

theorem mem_spanA_of_dvd {F : G → ℂ} (hF : IsClassFun F)
    (hdiv : ∀ g, ∃ k : ℤ, F g = (Nat.card G : ℂ) * k) : F ∈ spanA E ζ := by
  choose k hk using hdiv
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hF' : F = ∑ s : G, k s • classCount s := by
    have h := card_smul_eq_sum_classCount hF
    funext g
    have hg := congrFun h g
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hg
    simp only [Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
    apply mul_left_cancel₀ hG
    rw [hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [hk s]
    ring
  rw [hF']
  exact Submodule.sum_mem _ fun s _ ↦ Submodule.smul_mem _ _ (classCount_mem_spanA hE hmono hcyc hζ s)

end Divisible

section Values

variable {E : Subgroup G → Prop} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
include hζ

theorem apply_mem_adjoin_of_mem_spanZ {f : G → ℂ} (hf : f ∈ spanZ E) (g : G) :
    f g ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, -, l, rfl⟩ := hx
    exact (IsCharacter.indLin K l).apply_mem_adjoin_card g hζ
  | zero => exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
  | smul n x _ hx =>
    rw [Pi.smul_apply, zsmul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ n) hx

theorem apply_mem_adjoin_of_mem_spanA {f : G → ℂ} (hf : f ∈ spanA E ζ) (g : G) :
    f g ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, g', hg', rfl⟩ := hx
    rw [Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.mul_mem _ ha (apply_mem_adjoin_of_mem_spanZ hζ hg' g)
  | zero => exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
  | smul n x _ hx =>
    rw [Pi.smul_apply, zsmul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ n) hx

end Values

section Congruence

def CongrData (ζ : ℂ) (N : ℕ) (s : G) (a : ℤ) (f : G → ℂ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (c β β' : ι → Algebra.adjoin ℤ ({ζ} : Set ℂ)),
    (∀ i, β i ^ N = β' i ^ N) ∧ f s = ∑ i, (c i : ℂ) * β i ∧ f (s ^ a) = ∑ i, (c i : ℂ) * β' i

variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}

omit [Fintype G] in
theorem congrData_zero : CongrData ζ N s a (0 : G → ℂ) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, PEmpty.elim, fun i ↦ i.elim, by simp, by simp⟩

omit [Fintype G] in
theorem CongrData.add {f g : G → ℂ} (hf : CongrData ζ N s a f) (hg : CongrData ζ N s a g) :
    CongrData ζ N s a (f + g) := by
  obtain ⟨ι, _, c, β, β', hβ, h1, h2⟩ := hf
  obtain ⟨ι', _, c', γ, γ', hγ, h1', h2'⟩ := hg
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim c c', Sum.elim β γ, Sum.elim β' γ', ?_, ?_, ?_⟩
  · rintro (i | i)
    · exact hβ i
    · exact hγ i
  · simp [Fintype.sum_sum_type, h1, h1']
  · simp [Fintype.sum_sum_type, h2, h2']

omit [Fintype G] in
theorem CongrData.smul {f : G → ℂ} (hf : CongrData ζ N s a f) (x : Algebra.adjoin ℤ ({ζ} : Set ℂ)) :
    CongrData ζ N s a ((x : ℂ) • f) := by
  obtain ⟨ι, _, c, β, β', hβ, h1, h2⟩ := hf
  refine ⟨ι, inferInstance, fun i ↦ x * c i, β, β', hβ, ?_, ?_⟩
  · simp [h1, Finset.mul_sum, mul_assoc]
  · simp [h2, Finset.mul_sum, mul_assoc]

omit [Fintype G] in
theorem CongrData.zsmul {f : G → ℂ} (hf : CongrData ζ N s a f) (n : ℤ) : CongrData ζ N s a (n • f) := by
  have := hf.smul (n : Algebra.adjoin ℤ ({ζ} : Set ℂ))
  rwa [show ((n : Algebra.adjoin ℤ ({ζ} : Set ℂ)) : ℂ) = (n : ℂ) by simp, Int.cast_smul_eq_zsmul] at this

theorem IsCharacter.congrData {χ : G → ℂ} (hχ : IsCharacter χ) (hζ : IsPrimitiveRoot ζ (Nat.card G))
    {b : ℤ} (hab : s ^ a * s ^ b = s) (hb : (s ^ b) ^ N = 1) : CongrData ζ N s a χ := by
  set C := Subgroup.zpowers s
  set s' : C := ⟨s, Subgroup.mem_zpowers s⟩
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨m, hm⟩ := (hχ.comp C.subtype).exists_nat
  have hval : ∀ ψ ∈ irrChars C, ∀ x : C, ψ x ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := fun ψ hψ x ↦
    (mem_irrChars.mp hψ).isCharacter.apply_mem_adjoin x hζ
      (by rw [← Subgroup.orderOf_coe]; exact orderOf_dvd_natCard _)
  have hsN : s' ^ N = (s' ^ a) ^ N := by
    apply Subtype.ext
    simp only [s', Subgroup.coe_pow, Subgroup.coe_zpow]
    have hc : Commute (s ^ a) (s ^ b) := (Commute.refl s).zpow_zpow a b
    rw [← hab, hc.mul_pow, hb, mul_one, hab]
  refine ⟨irrChars C, inferInstance, fun ψ ↦ (m ψ : Algebra.adjoin ℤ ({ζ} : Set ℂ)),
    fun ψ ↦ ⟨ψ.1 s', hval ψ.1 ψ.2 s'⟩, fun ψ ↦ ⟨ψ.1 (s' ^ a), hval ψ.1 ψ.2 _⟩, ?_, ?_, ?_⟩
  · intro ψ
    obtain ⟨l, hl⟩ := (mem_irrChars.mp ψ.2).exists_monoidHom
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow]
    rw [hl, hl, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow, hsN]
  · have h := congrFun hm s'
    simp only [Function.comp_apply, Subgroup.coe_subtype, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    change χ (s' : G) = _
    rw [h, ← Finset.sum_coe_sort]
    simp
  · have h := congrFun hm (s' ^ a)
    simp only [Function.comp_apply, Subgroup.coe_subtype, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Subgroup.coe_zpow] at h
    change χ ((s' : G) ^ a) = _
    rw [h, ← Finset.sum_coe_sort]
    simp

variable {E : Subgroup G → Prop}

theorem congrData_of_mem_spanZ (hζ : IsPrimitiveRoot ζ (Nat.card G)) {b : ℤ} (hab : s ^ a * s ^ b = s)
    (hb : (s ^ b) ^ N = 1) {f : G → ℂ} (hf : f ∈ spanZ E) : CongrData ζ N s a f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, -, l, rfl⟩ := hx
    exact (IsCharacter.indLin K l).congrData hζ hab hb
  | zero => exact congrData_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul n x _ hx => exact hx.zsmul n

theorem congrData_of_mem_spanA (hζ : IsPrimitiveRoot ζ (Nat.card G)) {b : ℤ} (hab : s ^ a * s ^ b = s)
    (hb : (s ^ b) ^ N = 1) {f : G → ℂ} (hf : f ∈ spanA E ζ) : CongrData ζ N s a f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x', hx', g, hg, rfl⟩ := hx
    exact (congrData_of_mem_spanZ hζ hab hb hg).smul ⟨x', hx'⟩
  | zero => exact congrData_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul n x _ hx => exact hx.zsmul n

omit [Fintype G] in

theorem CongrData.exists_pow_eq {p k : ℕ} (hp : p.Prime) {f : G → ℂ} (hf : CongrData ζ (p ^ k) s a f) :
    ∃ r ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ), f s ^ p ^ k = f (s ^ a) ^ p ^ k + p * r := by
  obtain ⟨ι, _, c, β, β', hβ, h1, h2⟩ := hf
  obtain ⟨r1, hr1⟩ := exists_sum_pow_prime_pow_eq hp Finset.univ (fun i ↦ c i * β i) k
  obtain ⟨r2, hr2⟩ := exists_sum_pow_prime_pow_eq hp Finset.univ (fun i ↦ c i * β' i) k
  have heq : ∑ i, (c i * β i) ^ p ^ k = ∑ i, (c i * β' i) ^ p ^ k :=
    Finset.sum_congr rfl fun i _ ↦ by rw [mul_pow, mul_pow, hβ i]
  refine ⟨(r1 - r2 : Algebra.adjoin ℤ ({ζ} : Set ℂ)), (r1 - r2).2, ?_⟩
  have hx : f s = ((∑ i, c i * β i : Algebra.adjoin ℤ ({ζ} : Set ℂ)) : ℂ) := by
    rw [h1]
    push_cast
    rfl
  have hy : f (s ^ a) = ((∑ i, c i * β' i : Algebra.adjoin ℤ ({ζ} : Set ℂ)) : ℂ) := by
    rw [h2]
    push_cast
    rfl
  rw [hx, hy]
  have key : (∑ i, c i * β i) ^ p ^ k = (∑ i, c i * β' i) ^ p ^ k + p * (r1 - r2) := by
    rw [hr1, hr2, heq]
    ring
  have := congrArg (fun z : Algebra.adjoin ℤ ({ζ} : Set ℂ) ↦ (z : ℂ)) key
  simpa using this

theorem int_modEq_of_mem_spanA (hζ : IsPrimitiveRoot ζ (Nat.card G)) {p k : ℕ} (hp : p.Prime) {b : ℤ}
    (hab : s ^ a * s ^ b = s) (hb : (s ^ b) ^ p ^ k = 1) {f : G → ℂ} (hf : f ∈ spanA E ζ) {u v : ℤ}
    (hu : f s = u) (hv : f (s ^ a) = v) : (u : ZMod p) = v := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr, hrr⟩ := (congrData_of_mem_spanA hζ hab hb hf).exists_pow_eq hp
  rw [hu, hv] at hrr
  have hint := hζ.isIntegral Nat.card_pos
  obtain ⟨z, -, hz⟩ := exists_int_of_mul_eq_int hint hr (d := p) (k := u ^ p ^ k - v ^ p ^ k)
    (Int.natCast_ne_zero.mpr hp.ne_zero) (by push_cast; rw [hrr]; ring)
  have hmod : ((u ^ p ^ k : ℤ) : ZMod p) = ((v ^ p ^ k : ℤ) : ZMod p) := by
    rw [← sub_eq_zero, ← Int.cast_sub, ← hz]
    push_cast
    simp
  push_cast at hmod
  rwa [ZMod.pow_card_pow, ZMod.pow_card_pow] at hmod

end Congruence

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

universe u

variable {G : Type u} [Group G]

section MulSubgroup

def mulSubgroup (C P : Subgroup G) (hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c) : Subgroup G where
  carrier := {h | ∃ c ∈ C, ∃ y ∈ P, h = c * y}
  one_mem' := ⟨1, C.one_mem, 1, P.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, hc, y, hy, rfl⟩ ⟨c', hc', y', hy', rfl⟩
    refine ⟨c * c', C.mul_mem hc hc', y * y', P.mul_mem hy hy', ?_⟩
    rw [show c * y * (c' * y') = c * (y * c') * y' by group, ← hcomm c' hc' y hy]
    group
  inv_mem' := by
    rintro _ ⟨c, hc, y, hy, rfl⟩
    refine ⟨c⁻¹, C.inv_mem hc, y⁻¹, P.inv_mem hy, ?_⟩
    rw [mul_inv_rev]
    exact (hcomm c⁻¹ (C.inv_mem hc) y⁻¹ (P.inv_mem hy)).symm

theorem mem_mulSubgroup {C P : Subgroup G} {hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c} {h : G} :
    h ∈ mulSubgroup C P hcomm ↔ ∃ c ∈ C, ∃ y ∈ P, h = c * y := Iff.rfl

theorem left_le_mulSubgroup {C P : Subgroup G} (hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c) :
    C ≤ mulSubgroup C P hcomm := fun c hc ↦ ⟨c, hc, 1, P.one_mem, (mul_one c).symm⟩

theorem right_le_mulSubgroup {C P : Subgroup G} (hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c) :
    P ≤ mulSubgroup C P hcomm := fun y hy ↦ ⟨1, C.one_mem, y, hy, (one_mul y).symm⟩

end MulSubgroup

variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)

def sylowCent : Subgroup G :=
  ((Classical.arbitrary (Sylow p (Subgroup.centralizer {x}))) : Subgroup (Subgroup.centralizer {x})).map
    (Subgroup.centralizer {x}).subtype

variable {p x}

omit [Fintype G] hp in
theorem commute_of_mem_sylowCent {y : G} (hy : y ∈ sylowCent p x) : y * x = x * y := by
  have : y ∈ Subgroup.centralizer {x} := Subgroup.map_subtype_le _ hy
  exact Subgroup.mem_centralizer_singleton_iff.mp this

omit [Fintype G] hp in
variable (p x) in
theorem isPGroup_sylowCent : IsPGroup p (sylowCent p x) :=
  (Classical.arbitrary (Sylow p (Subgroup.centralizer {x}))).isPGroup'.map _

variable (p x) in

theorem exists_card_centralizer_eq :
    ∃ m : ℕ, Nat.card (Subgroup.centralizer {x}) = Nat.card (sylowCent p x) * m ∧ ¬ p ∣ m := by
  set P0 := Classical.arbitrary (Sylow p (Subgroup.centralizer {x}))
  refine ⟨(P0 : Subgroup (Subgroup.centralizer {x})).index, ?_, P0.not_dvd_index⟩
  rw [sylowCent, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Subgroup.card_mul_index]

omit [Fintype G] hp in
theorem commute_zpowers_sylowCent :
    ∀ c ∈ Subgroup.zpowers x, ∀ y ∈ sylowCent p x, c * y = y * c := by
  intro c hc y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact ((Commute.symm (commute_of_mem_sylowCent hy)).zpow_left i).eq

variable (p x) in

def elemSub : Subgroup G := mulSubgroup (Subgroup.zpowers x) (sylowCent p x) commute_zpowers_sylowCent

omit [Fintype G] hp in
theorem mem_elemSub_self : x ∈ elemSub p x :=
  left_le_mulSubgroup _ (Subgroup.mem_zpowers x)

omit [Fintype G] hp in
theorem sylowCent_le_elemSub : sylowCent p x ≤ elemSub p x := right_le_mulSubgroup _

omit [Fintype G] hp in
theorem isElementaryAt_elemSub (hx : (orderOf x).Coprime p) : IsElementaryAt p (elemSub p x) :=
  ⟨Subgroup.zpowers x, sylowCent p x, left_le_mulSubgroup _, right_le_mulSubgroup _, inferInstance,
    by rwa [Nat.card_zpowers], isPGroup_sylowCent p x, commute_zpowers_sylowCent,
    fun _ hh ↦ hh⟩

variable (p x) in

abbrev sylowCentIn : Subgroup (elemSub p x) := (sylowCent p x).subgroupOf (elemSub p x)

instance normal_sylowCentIn : (sylowCentIn p x).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨c, hc, y, hy, hg⟩ := mem_mulSubgroup.mp g.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]
  have hw : y * n * y⁻¹ ∈ sylowCent p x :=
    (sylowCent p x).mul_mem ((sylowCent p x).mul_mem hy hn) ((sylowCent p x).inv_mem hy)
  rw [show c * y * (n : G) * (c * y)⁻¹ = c * (y * n * y⁻¹) * c⁻¹ by group,
    commute_zpowers_sylowCent c hc _ hw, mul_inv_cancel_right]
  exact hw

omit [Fintype G] hp in
theorem quotient_mul_comm (a b : elemSub p x ⧸ sylowCentIn p x) : a * b = b * a := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  obtain ⟨c1, hc1, y1, hy1, ha⟩ := mem_mulSubgroup.mp a.2
  obtain ⟨c2, hc2, y2, hy2, hb⟩ := mem_mulSubgroup.mp b.2
  have hcc : c1 * c2 = c2 * c1 := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc2
    rw [← zpow_add, ← zpow_add, add_comm]
  have hab : ((a * b : elemSub p x) : G) = (c1 * c2) * (y1 * y2) := by
    simp only [Subgroup.coe_mul, ha, hb]
    rw [show c1 * y1 * (c2 * y2) = c1 * (y1 * c2) * y2 by group,
      ← commute_zpowers_sylowCent c2 hc2 y1 hy1]
    group
  have hba : ((b * a : elemSub p x) : G) = (c1 * c2) * (y2 * y1) := by
    simp only [Subgroup.coe_mul, ha, hb]
    rw [show c2 * y2 * (c1 * y1) = c2 * (y2 * c1) * y1 by group,
      ← commute_zpowers_sylowCent c1 hc1 y2 hy2, hcc]
    group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hab hba ⊢
  rw [hab, hba, show (c1 * c2 * (y1 * y2))⁻¹ * (c1 * c2 * (y2 * y1)) = (y1 * y2)⁻¹ * (y2 * y1) by group]
  exact (sylowCent p x).mul_mem ((sylowCent p x).inv_mem ((sylowCent p x).mul_mem hy1 hy2))
    ((sylowCent p x).mul_mem hy2 hy1)

section Theta

variable (p x) in

def xIn : elemSub p x := ⟨x, mem_elemSub_self⟩

variable (p x) in

def theta (h : elemSub p x) : ℂ :=
  if (h : elemSub p x ⧸ sylowCentIn p x) = (xIn p x : elemSub p x ⧸ sylowCentIn p x) then
    (Nat.card (elemSub p x ⧸ sylowCentIn p x) : ℂ) else 0

omit [Fintype G] hp in
theorem mk_eq_mk_xIn_iff (h : elemSub p x) :
    (h : elemSub p x ⧸ sylowCentIn p x) = (xIn p x : elemSub p x ⧸ sylowCentIn p x) ↔
      x⁻¹ * (h : G) ∈ sylowCent p x := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, ← (sylowCent p x).inv_mem_iff]
  simp [xIn]

omit hp in

theorem card_mul_indFun_theta (g : G) :
    (Nat.card (sylowCent p x) : ℂ) * indFun (elemSub p x).subtype (theta p x) g =
      ∑ t : G, if x⁻¹ * (t⁻¹ * g * t) ∈ sylowCent p x then 1 else 0 := by
  set H := elemSub p x
  set P := sylowCent p x
  set Q := H ⧸ sylowCentIn p x
  have hinner : ∀ z : G, ∑ h : H, (if (H.subtype h) = z then theta p x h else 0) =
      if x⁻¹ * z ∈ P then (Nat.card Q : ℂ) else 0 := by
    intro z
    by_cases hz : z ∈ H
    · rw [Finset.sum_eq_single ⟨z, hz⟩]
      · rw [show H.subtype ⟨z, hz⟩ = z from rfl, if_pos rfl, theta]
        have hiff := mk_eq_mk_xIn_iff (p := p) (x := x) ⟨z, hz⟩
        by_cases hc : x⁻¹ * z ∈ P
        · rw [if_pos (hiff.mpr hc), if_pos hc]
        · rw [if_neg (fun h ↦ hc (hiff.mp h)), if_neg hc]
      · intro h _ hne
        rw [if_neg]
        intro h'
        exact hne (Subtype.ext h')
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · rw [Finset.sum_eq_zero, if_neg]
      · intro hP
        apply hz
        have := H.mul_mem (mem_elemSub_self (p := p)) (sylowCent_le_elemSub hP)
        rwa [mul_inv_cancel_left] at this
      · intro h _
        rw [if_neg]
        intro h'
        exact hz (h' ▸ h.2)
  have hcard : (Nat.card H : ℂ) = Nat.card Q * Nat.card P := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (sylowCentIn p x),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowCent_le_elemSub).toEquiv]
    push_cast
    rfl
  have hQ : (Nat.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hP : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [indFun_apply, Finset.sum_congr rfl fun t _ ↦ hinner _, hcard, ← mul_assoc, mul_inv,
    mul_comm (Nat.card Q : ℂ)⁻¹, ← mul_assoc, mul_inv_cancel₀ hP, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  split_ifs
  · exact inv_mul_cancel₀ hQ
  · simp

omit [Fintype G] in

theorem mem_sylowCent_iff (hx : (orderOf x).Coprime p) {z : G} (hz : (orderOf z).Coprime p) :
    x⁻¹ * z ∈ sylowCent p x ↔ z = x := by
  constructor
  · intro hw
    have hxw : x * (x⁻¹ * z) = (x⁻¹ * z) * x := (commute_of_mem_sylowCent hw).symm
    have hxz : Commute x z := by
      have h1 : Commute x (x⁻¹ * z) := hxw
      have := (Commute.refl x).mul_right h1
      rwa [mul_inv_cancel_left] at this
    have hcomm : Commute x⁻¹ z := hxz.inv_left
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_sylowCent p x)) ⟨_, hw⟩
    rw [Subgroup.orderOf_mk] at hj
    have hdvd := hcomm.orderOf_mul_dvd_lcm
    rw [orderOf_inv, hj] at hdvd
    have hcop : (Nat.lcm (orderOf x) (orderOf z)).Coprime p :=
      Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _) (Nat.Coprime.mul_left hx hz)
    have hj0 : j = 0 := by
      by_contra hj0
      have : p ∣ Nat.lcm (orderOf x) (orderOf z) :=
        (dvd_pow_self p hj0).trans hdvd
      exact hp.out.one_lt.ne' ((Nat.coprime_comm.mp hcop).eq_one_of_dvd this)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    calc z = x * (x⁻¹ * z) := by group
      _ = x := by rw [hj, mul_one]
  · intro h
    rw [h, inv_mul_cancel]
    exact (sylowCent p x).one_mem

end Theta

section ThetaSpan

variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)

omit hp in
include hζ hmono in

theorem indFun_theta_mem_spanA (hx : (orderOf x).Coprime p) :
    indFun (elemSub p x).subtype (theta p x) ∈ spanA (G := G) (IsElementaryAt p) ζ := by
  set H := elemSub p x
  set Q := H ⧸ sylowCentIn p x
  set xb : Q := (xIn p x : Q)
  set δ : Q → ℂ := fun q ↦ if q = xb then (Nat.card Q : ℂ) else 0
  have hδ : IsClassFun δ := by
    intro g h
    simp only [δ]
    rw [quotient_mul_comm h g, mul_inv_cancel_right]
  have hN : (Nat.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcoef : ∀ ψ : Q → ℂ, charInner Q δ ψ = ψ xb⁻¹ := by
    intro ψ
    rw [charInner_apply]
    simp only [δ, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  have htheta : theta p x = δ ∘ QuotientGroup.mk' (sylowCentIn p x) := rfl
  rw [htheta, eq_sum_irrChars_of_isClassFun hδ]
  have hcomp : (∑ ψ ∈ irrChars Q, charInner Q δ ψ • ψ) ∘ QuotientGroup.mk' (sylowCentIn p x) =
      ∑ ψ ∈ irrChars Q, charInner Q δ ψ • (ψ ∘ QuotientGroup.mk' (sylowCentIn p x)) := by
    funext h
    simp [Finset.sum_apply]
  rw [hcomp, map_sum]
  refine Submodule.sum_mem _ fun ψ hψ ↦ ?_
  rw [map_smul, hcoef]
  have hψc := (mem_irrChars.mp hψ).isCharacter
  refine smul_mem_spanA ?_ (indFun_mem_spanZ (fun K L hK hLK ↦ hK.mono hLK) hmono
    (isElementaryAt_elemSub hx) (hψc.comp _))
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  refine hψc.apply_mem_adjoin _ hζ ?_
  rw [orderOf_inv]
  refine (orderOf_map_dvd (QuotientGroup.mk' (sylowCentIn p x)) (xIn p x)).trans ?_
  rw [xIn, Subgroup.orderOf_mk]
  exact orderOf_dvd_natCard x

omit hp in
include hζ hmono in

theorem exists_int_indFun_theta (hx : (orderOf x).Coprime p) (g : G) :
    ∃ k : ℤ, indFun (elemSub p x).subtype (theta p x) g = k := by
  have hA := apply_mem_adjoin_of_mem_spanA hζ (indFun_theta_mem_spanA hζ hmono hx) g
  have hcount := card_mul_indFun_theta (p := p) (x := x) g
  obtain ⟨z, hz, -⟩ := exists_int_of_mul_eq_int (hζ.isIntegral Nat.card_pos) hA
    (d := Nat.card (sylowCent p x)) (k := ∑ t : G, if x⁻¹ * (t⁻¹ * g * t) ∈ sylowCent p x then 1 else 0)
    (Int.natCast_ne_zero.mpr Nat.card_pos.ne') (by push_cast; exact hcount)
  exact ⟨z, hz⟩

end ThetaSpan

section Count

theorem card_mul_indFun_theta_of_coprime (hx : (orderOf x).Coprime p) {g : G}
    (hg : (orderOf g).Coprime p) :
    (Nat.card (sylowCent p x) : ℂ) * indFun (elemSub p x).subtype (theta p x) g =
      ∑ t : G, if t⁻¹ * g * t = x then 1 else 0 := by
  rw [card_mul_indFun_theta]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have ht : (orderOf (t⁻¹ * g * t)).Coprime p := by
    have : t⁻¹ * g * t = (MulAut.conj t⁻¹) g := by simp
    rw [this, MulEquiv.orderOf_eq]
    exact hg
  by_cases h : t⁻¹ * g * t = x
  · rw [if_pos h, if_pos ((mem_sylowCent_iff hx ht).mpr h)]
  · rw [if_neg h, if_neg fun h' ↦ h ((mem_sylowCent_iff hx ht).mp h')]

omit [Fintype G] hp in
theorem sum_conj_eq_card_centralizer [Fintype G] {g : G} (hc : IsConj x g) :
    (∑ t : G, if t⁻¹ * g * t = x then (1 : ℂ) else 0) = Nat.card (Subgroup.centralizer {x}) := by
  obtain ⟨u, hu⟩ := isConj_iff.mp hc
  rw [← hu]
  rw [Fintype.sum_equiv (Equiv.mulLeft u⁻¹) _ (fun t ↦ if t ∈ Subgroup.centralizer {x} then (1 : ℂ) else 0)
    (fun t ↦ ?_)]
  · rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · simp only [Equiv.coe_mulLeft, Subgroup.mem_centralizer_singleton_iff]
    congr 1
    apply propext
    constructor
    · intro h
      calc u⁻¹ * t * x = u⁻¹ * (t * (t⁻¹ * (u * x * u⁻¹) * t)) := by rw [h]; group
        _ = x * (u⁻¹ * t) := by group
    · intro h
      calc t⁻¹ * (u * x * u⁻¹) * t = t⁻¹ * u * (x * (u⁻¹ * t)) := by group
        _ = t⁻¹ * u * (u⁻¹ * t * x) := by rw [h]
        _ = x := by group

omit [Fintype G] hp in
theorem sum_conj_eq_zero [Fintype G] {g : G} (hc : ¬ IsConj x g) :
    (∑ t : G, if t⁻¹ * g * t = x then (1 : ℂ) else 0) = 0 := by
  refine Finset.sum_eq_zero fun t _ ↦ if_neg fun h ↦ hc ?_
  rw [isConj_iff]
  exact ⟨t, by rw [← h]; group⟩

end Count

section Main

def classRep (c : ConjClasses G) : G := Classical.choose c.exists_rep

omit [Fintype G] hp in
theorem mk_classRep (c : ConjClasses G) : ConjClasses.mk (classRep c) = c :=
  Classical.choose_spec c.exists_rep

variable (p) in

def brauerFun : G → ℂ := ∑ c : ConjClasses G,
  if (orderOf (classRep c)).Coprime p then
    indFun (elemSub p (classRep c)).subtype (theta p (classRep c)) else 0

variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hζ hmono

omit hp in
theorem brauerFun_mem_spanA : brauerFun p ∈ spanA (G := G) (IsElementaryAt p) ζ := by
  refine Submodule.sum_mem _ fun c _ ↦ ?_
  split_ifs with h
  · exact indFun_theta_mem_spanA hζ hmono h
  · exact Submodule.zero_mem _

omit hp in
theorem exists_int_brauerFun (g : G) : ∃ k : ℤ, brauerFun p g = k := by
  have h : ∀ c : ConjClasses G, ∃ k : ℤ, (if (orderOf (classRep c)).Coprime p then
      indFun (elemSub p (classRep c)).subtype (theta p (classRep c)) else 0) g = k := by
    intro c
    split_ifs with h
    · exact exists_int_indFun_theta hζ hmono h g
    · exact ⟨0, by simp⟩
  choose k hk using h
  refine ⟨∑ c, k c, ?_⟩
  rw [brauerFun, Finset.sum_apply]
  push_cast
  exact Finset.sum_congr rfl fun c _ ↦ hk c

omit hζ hmono in

theorem brauerFun_of_coprime {y : G} (hy : (orderOf y).Coprime p) :
    ∃ m : ℕ, brauerFun p y = m ∧ ¬ p ∣ m := by
  set c0 := ConjClasses.mk y
  set x := classRep c0
  have hxy : IsConj x y := ConjClasses.mk_eq_mk_iff_isConj.mp (mk_classRep c0)
  have hx : (orderOf x).Coprime p := by
    obtain ⟨u, hu⟩ := isConj_iff.mp hxy
    rw [show x = (MulAut.conj u⁻¹) y by rw [MulAut.conj_apply, ← hu]; group, MulEquiv.orderOf_eq]
    exact hy
  obtain ⟨m, hm, hpm⟩ := exists_card_centralizer_eq p x
  refine ⟨m, ?_, hpm⟩
  rw [brauerFun, Finset.sum_apply, Finset.sum_eq_single c0]
  · rw [if_pos hx]
    have h := card_mul_indFun_theta_of_coprime hx hy
    rw [sum_conj_eq_card_centralizer hxy, hm] at h
    have hP : (Nat.card (sylowCent p x) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    push_cast at h
    exact mul_left_cancel₀ hP h
  · intro c _ hc
    split_ifs with hxc
    · have h := card_mul_indFun_theta_of_coprime hxc hy
      have hnc : ¬ IsConj (classRep c) y := by
        intro hcj
        apply hc
        rw [← mk_classRep c]
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr hcj
      rw [sum_conj_eq_zero hnc] at h
      have hP : (Nat.card (sylowCent p (classRep c)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      exact (mul_eq_zero.mp h).resolve_left hP
    · simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem not_dvd_brauerFun (s : G) : ∃ k : ℤ, brauerFun p s = k ∧ ¬ (p : ℤ) ∣ k := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_zpow_mul_zpow_eq hp.out s
  obtain ⟨k, hk⟩ := exists_int_brauerFun hζ hmono s
  obtain ⟨m, hm, hpm⟩ := brauerFun_of_coprime ha
  refine ⟨k, hk, fun hdiv ↦ hpm ?_⟩
  have hcong := int_modEq_of_mem_spanA hζ hp.out hab hb (brauerFun_mem_spanA hζ hmono) hk
    (v := (m : ℤ)) (by rw [hm]; push_cast; rfl)
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd k p).mpr hdiv] at hcong
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (m : ℤ) p).mp hcong.symm
  exact Int.natCast_dvd_natCast.mp h0

theorem exists_smul_one_mem_spanZ :
    ∃ m : ℕ, ¬ p ∣ m ∧ ((m : ℤ) • (1 : G → ℂ)) ∈ spanZ (IsElementaryAt p) := by
  have hE : ∀ K L : Subgroup G, IsElementaryAt p K → L ≤ K → IsElementaryAt p L :=
    fun K L hK hLK ↦ hK.mono hLK
  have hcyc : ∀ s : G, IsElementaryAt p (Subgroup.zpowers s) := fun s ↦ isElementaryAt_zpowers hp.out s
  set n := Nat.card G
  set e := n.factorization p
  set q := p ^ e
  set m := n / q
  have hn : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  set M := Nat.totient q
  have hq0 : 0 < q := pow_pos hp.out.pos e
  have hM : M ≠ 0 := (Nat.totient_pos.mpr hq0).ne'
  have : NeZero q := ⟨hq0.ne'⟩
  set f : G → ℂ := brauerFun p
  have hfA : f ∈ spanA (G := G) (IsElementaryAt p) ζ := brauerFun_mem_spanA hζ hmono
  have hval : ∀ s, ∃ j : ℤ, (f ^ M - 1) s = (q : ℂ) * j := by
    intro s
    obtain ⟨k, hk, hpk⟩ := not_dvd_brauerFun hζ hmono s
    have hcop : Nat.Coprime k.natAbs q := Nat.Coprime.pow_right e
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h ↦ hpk (Int.natCast_dvd.mpr h)).symm
    have hunit : IsUnit (k : ZMod q) := by
      rcases Int.natAbs_eq k with h | h
      · rw [h, Int.cast_natCast]
        exact (ZMod.isUnit_iff_coprime _ _).mpr hcop
      · rw [h, Int.cast_neg, Int.cast_natCast]
        exact ((ZMod.isUnit_iff_coprime _ _).mpr hcop).neg
    have hpow : ((k ^ M - 1 : ℤ) : ZMod q) = 0 := by
      have h2 : (k : ZMod q) ^ M = 1 := by
        have := congrArg Units.val (ZMod.pow_totient hunit.unit)
        rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at this
      push_cast
      rw [h2, sub_self]
    obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hpow
    refine ⟨j, ?_⟩
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.one_apply]
    rw [show f s = (k : ℂ) from hk, show ((k : ℂ) ^ M - 1) = ((k ^ M - 1 : ℤ) : ℂ) by push_cast; ring, hj]
    push_cast
    ring
  have hcl : IsClassFun f := isClassFun_of_mem_spanA hfA
  have hF1 : ((m : ℤ) • (f ^ M - 1)) ∈ spanA (G := G) (IsElementaryAt p) ζ := by
    apply mem_spanA_of_dvd hE hmono hcyc hζ
    · intro g h
      simp [hcl g h]
    · intro g
      obtain ⟨j, hj⟩ := hval g
      refine ⟨j, ?_⟩
      have hn' : (Nat.card G : ℂ) = q * m := by exact_mod_cast hn.symm
      rw [Pi.smul_apply, hj, zsmul_eq_mul, hn']
      push_cast
      ring
  have hfM := pow_mem_spanA hE hmono hfA hM
  have h1 : ((m : ℤ) • (1 : G → ℂ)) = (m : ℤ) • f ^ M - (m : ℤ) • (f ^ M - 1) := by
    rw [smul_sub]
    abel
  have hA1 : ((m : ℤ) • (1 : G → ℂ)) ∈ spanA (G := G) (IsElementaryAt p) ζ := by
    rw [h1]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hfM) hF1
  refine ⟨m, Nat.not_dvd_ordCompl hp.out Nat.card_pos.ne', ?_⟩
  apply mem_spanZ_of_mem_spanA (hζ.isIntegral Nat.card_pos) hA1
  intro ψ hψ
  obtain ⟨j, hj⟩ := isCharacter_one.exists_nat_charInner (mem_irrChars.mp hψ).isCharacter
  refine ⟨m * j, ?_⟩
  rw [map_zsmul, LinearMap.smul_apply, hj, zsmul_eq_mul]
  push_cast
  ring

end Main

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

universe u

variable {G : Type u} [Group G] [Fintype G]

omit [Fintype G] in
theorem IsElementary.mono {H L : Subgroup G} (hH : IsElementary H) (hLH : L ≤ H) : IsElementary L :=
  let ⟨p, hp, hHp⟩ := hH
  ⟨p, hp, hHp.mono hLH⟩

variable (hmono : ∀ K : Subgroup G, IsElementary K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hmono

theorem one_mem_spanZ_of_mono : (1 : G → ℂ) ∈ spanZ (IsElementary (G := G)) := by
  let T : ℤ →ₗ[ℤ] (G → ℂ) := LinearMap.toSpanSingleton ℤ (G → ℂ) 1
  let I : Submodule ℤ ℤ := (spanZ (IsElementary (G := G))).comap T
  have hmem : ∀ k : ℤ, k ∈ I ↔ k • (1 : G → ℂ) ∈ spanZ (IsElementary (G := G)) := fun k ↦ Iff.rfl
  have hprimes : ∀ p : ℕ, p.Prime → ∃ m : ℕ, ¬ p ∣ m ∧ (m : ℤ) ∈ I := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hpm, hm⟩ := exists_smul_one_mem_spanZ (p := p) (Complex.isPrimitiveRoot_exp _
      Nat.card_pos.ne') (fun K hK χ hχ ↦ hmono K ⟨p, hp, hK⟩ χ hχ)
    exact ⟨m, hpm, (hmem _).mpr (spanZ_mono (fun K hK ↦ ⟨p, hp, hK⟩) hm)⟩
  set d := Submodule.IsPrincipal.generator I
  have hdvd : ∀ k ∈ I, d ∣ k := fun k hk ↦ by
    obtain ⟨s, hs⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hk
    exact ⟨s, by rw [hs, smul_eq_mul, mul_comm]⟩
  have hd : d.natAbs = 1 := by
    by_contra hd
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
    obtain ⟨m, hpm, hm⟩ := hprimes p hp
    apply hpm
    have h1 : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hpd
    exact Int.natCast_dvd_natCast.mp (h1.trans (hdvd _ hm))
  have hd1 : (1 : ℤ) ∈ I := by
    have hdI : d ∈ I := Submodule.IsPrincipal.generator_mem I
    rcases Int.natAbs_eq d with h | h
    · rw [hd] at h
      rwa [h] at hdI
    · rw [hd] at h
      have := I.smul_mem (-1) hdI
      rwa [h, smul_eq_mul, Nat.cast_one, neg_mul_neg, one_mul] at this
  simpa using (hmem 1).mp hd1

theorem mem_spanZ_of_mono {χ : G → ℂ} (hχ : IsCharacter χ) : χ ∈ spanZ (IsElementary (G := G)) := by
  have h := mul_mem_spanZ (fun K L hK hLK ↦ hK.mono hLK) hmono hχ (one_mem_spanZ_of_mono hmono)
  rwa [mul_one] at h

end GroundTheory.LocalField
end
end
