import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.ValuationPiNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualCountBound.MatIdxB

section
noncomputable section

open Matrix GroundTheory.Automorphic ValuativeRel

namespace PositivityTheory.RgUd.T.Desc.SLT.Bi

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.T.Desc.SLT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem one_add_mem_zero_lattice (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {j : ℕ} {x : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ Lat Z j) : 1 + x ∈ Lat Z 0 := by
  obtain ⟨hxB, hxv⟩ := hx
  refine ⟨fun a ha => ?_, fun r s => ?_⟩
  · rw [mul_add, add_mul, mul_one, one_mul, hxB a ha]
  · have hpi : valuation k (pi k) ^ j ≤ 1 := pow_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le j
    rw [pow_zero, Matrix.add_apply]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ((hxv r s).trans hpi))
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]
      exact zero_le'

theorem exists_unit {m : ℕ} (hm : 1 ≤ m) {a : Matrix (Fin n) (Fin n) k}
    (ha : ∀ i j, valuation k (a i j) ≤ valuation k (pi k) ^ m) :
    ∃ h ∈ GLnLocal.congruenceSubgroup k n m, h.val = 1 + a := by
  have hpi1 : valuation k (pi k) ^ m ≤ 1 :=
    pow_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le m
  have hpim : valuation k (pi k) ^ m ≤ valuation k (pi k) ^ 1 :=
    pow_le_pow_right_of_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le hm
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨a i j, (ha i j).trans hpi1⟩
  have hBm : ∀ i j, B i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro i j
    have := (GLnLocal.mem_maximalIdeal_pow_iff k (m := 1) (y := B i j)).2 ((ha i j).trans hpim)
    rwa [pow_one] at this
  have hone : ∀ i j, (((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j : 𝒪[k]) : k) = (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit (1 + B).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, map_add, map_one]
    have h0 : (IsLocalRing.residue 𝒪[k]).mapMatrix B = 0 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
      exact (IsLocalRing.residue_eq_zero_iff _).2 (hBm i j)
    rw [h0, add_zero, Matrix.det_one]
    exact one_ne_zero
  have hcoe : ∀ i j, ((((1 + B) i j : 𝒪[k])) : k) = (1 + a) i j := by
    intro i j
    rw [Matrix.add_apply, Subring.coe_add, hone, Matrix.add_apply]
  let U : GL (Fin n) 𝒪[k] := Matrix.nonsingInvUnit (1 + B) hdet
  refine ⟨GLnLocal.integralGLHom k n U, ⟨U, ?_, rfl⟩, ?_⟩
  · refine (GLnLocal.mem_ker_reduction_iff k n).2 fun i j => ?_
    have : ((U : Matrix (Fin n) (Fin n) 𝒪[k]) i j : k) = (1 + a) i j := hcoe i j
    rw [this, Matrix.add_apply, add_sub_cancel_left]
    exact ha i j
  · ext i j
    rw [GLnLocal.integralGLHom_apply]
    exact hcoe i j

theorem mem_Lc_iff (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {m : ℕ} (hm : 1 ≤ m) (h : GL (Fin n) k) :
    h ∈ Lc Z m ↔ h.val - 1 ∈ Lat Z m := by
  constructor
  · rintro ⟨hG, hC⟩
    have hG' : h ∈ Gz Z := hG
    have hC' : h ∈ GLnLocal.congruenceSubgroup k n m := hC
    rw [GLnLocal.mem_congruenceSubgroup_iff] at hC'
    refine ⟨fun a ha => ?_, fun i j => ?_⟩
    · rw [mul_sub, sub_mul, mul_one, one_mul, hG' a ha]
    · rw [Matrix.sub_apply]
      exact hC'.2 i j
  · intro hx
    obtain ⟨h', hh', hv⟩ := exists_unit hm hx.2
    have heq : h' = h := Units.ext (by rw [hv]; abel)
    have hG : h ∈ Gz Z := by
      intro a ha
      have := hx.1 a ha
      rw [mul_sub, sub_mul, mul_one, one_mul] at this
      exact sub_left_inj.mp this
    exact ⟨hG, heq ▸ hh'⟩

theorem exists_Lc (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {m : ℕ} (hm : 1 ≤ m)
    {a : Matrix (Fin n) (Fin n) k} (ha : a ∈ Lat Z m) : ∃ h ∈ Lc Z m, h.val = 1 + a := by
  obtain ⟨h, -, e⟩ := exists_unit hm ha.2
  refine ⟨h, (mem_Lc_iff Z hm h).mpr ?_, e⟩
  rw [e, add_sub_cancel_left]; exact ha

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem relIndex_eq_of_coset (H K : Subgroup (GL (Fin n) k)) (A N : AddSubgroup (Matrix (Fin n) (Fin n) k))
    (h1 : ∀ h ∈ H, h.val - 1 ∈ A) (h2 : ∀ a ∈ A, ∃ h ∈ H, h.val = 1 + a)
    (h3 : ∀ h ∈ H, ∀ x ∈ N, h.val * x ∈ N) (h4 : ∀ h, h ∈ K ↔ h.val - 1 ∈ N) :
    K.relIndex H = N.relIndex A := by
  let e : H ≃ A :=
    { toFun := fun x => ⟨(x : GL (Fin n) k).val - 1, h1 x x.2⟩
      invFun := fun a => ⟨(h2 a a.2).choose, (h2 a a.2).choose_spec.1⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Units.ext
        rw [(h2 _ (h1 x x.2)).choose_spec.2]
        abel
      right_inv := fun a => by
        apply Subtype.ext
        change (h2 a a.2).choose.val - 1 = a
        rw [(h2 a a.2).choose_spec.2]
        abel }
  have key : ∀ x y : H, x⁻¹ * y ∈ K.subgroupOf H ↔ -(e x) + e y ∈ N.addSubgroupOf A := by
    intro x y
    rw [Subgroup.mem_subgroupOf, AddSubgroup.mem_addSubgroupOf, h4]
    have hx : (x : GL (Fin n) k) ∈ H := x.2
    have hinv : (x : GL (Fin n) k)⁻¹ ∈ H := H.inv_mem x.2
    change ((x : GL (Fin n) k)⁻¹ * (y : GL (Fin n) k)).val - 1 ∈ N ↔
      -((x : GL (Fin n) k).val - 1) + ((y : GL (Fin n) k).val - 1) ∈ N
    have h6 : -((x : GL (Fin n) k).val - 1) + ((y : GL (Fin n) k).val - 1) =
        (y : GL (Fin n) k).val - (x : GL (Fin n) k).val := by abel
    have h5 : ((x : GL (Fin n) k)⁻¹ * (y : GL (Fin n) k)).val - 1 =
        ((x : GL (Fin n) k)⁻¹).val * ((y : GL (Fin n) k).val - (x : GL (Fin n) k).val) := by
      rw [Units.val_mul, mul_sub, Units.inv_mul]
    rw [h5, h6]
    constructor
    · intro hN
      have := h3 _ hx _ hN
      rwa [← mul_assoc, Units.mul_inv, one_mul] at this
    · intro hN
      exact h3 _ hinv _ hN
  change Nat.card (H ⧸ K.subgroupOf H) = Nat.card (A ⧸ N.addSubgroupOf A)
  exact Nat.card_congr (Quotient.congr e fun x y => by
    rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]
    exact key x y)

private theorem mul_mem_Lat_of_mem_Lat_zero (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {j : ℕ}
    {y x : Matrix (Fin n) (Fin n) k} (hy : y ∈ Lat Z 0) (hx : x ∈ Lat Z j) : y * x ∈ Lat Z j := by
  refine ⟨fun a ha => ?_, fun r s => ?_⟩
  · rw [← mul_assoc, hy.1 a ha, mul_assoc, hx.1 a ha, mul_assoc]
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * valuation k (pi k) ^ j :=
          mul_le_mul' ((hy.2 r l).trans_eq (pow_zero _)) (hx.2 l s)
      _ = _ := one_mul _

theorem relIndex_Lc (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {m m' : ℕ} (hm : 1 ≤ m) (hmm : m ≤ m') :
    (Lc Z m').relIndex (Lc Z m) = (Lat Z m').relIndex (Lat Z m) := by
  apply relIndex_eq_of_coset
  · intro h hh
    exact (mem_Lc_iff Z hm h).1 hh
  · intro a ha
    exact exists_Lc Z hm ha
  · intro h hh x hx
    have := one_add_mem_zero_lattice Z ((mem_Lc_iff Z hm h).1 hh)
    rw [add_sub_cancel] at this
    exact mul_mem_Lat_of_mem_Lat_zero Z this hx
  · intro h
    exact mem_Lc_iff Z (hm.trans hmm) h

theorem relIndex_Lc_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g : GL (Fin n) k) (hg : g ∈ Gz Z)
    (c : ℕ) (hc : ∀ j : ℕ, ∀ x ∈ Lat Z (j + c), conjA g x ∈ Lat Z j ∧ conjA g⁻¹ x ∈ Lat Z j)
    {m m' : ℕ} (hm : 1 ≤ m) (hcm : c ≤ m) (hmm : m ≤ m') :
    (Lc Z m').relIndex ((Lc Z m).map (MulAut.conj g).toMonoidHom) =
      (Lat Z m').relIndex ((Lat Z m).map (conjA g)) := by
  apply relIndex_eq_of_coset
  · intro h hh
    obtain ⟨h0, hh0, rfl⟩ := Subgroup.mem_map.1 hh
    refine AddSubgroup.mem_map.2 ⟨h0.val - 1, (mem_Lc_iff Z hm h0).1 hh0, ?_⟩
    rw [conjA_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Units.val_mul,
      mul_sub, sub_mul, mul_one, Units.mul_inv]
  · intro a ha
    obtain ⟨a0, ha0, rfl⟩ := AddSubgroup.mem_map.1 ha
    obtain ⟨h0, hh0, hv⟩ := exists_Lc Z hm ha0
    refine ⟨g * h0 * g⁻¹, Subgroup.mem_map.2 ⟨h0, hh0, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩, ?_⟩
    rw [conjA_apply, Units.val_mul, Units.val_mul, hv, mul_add, add_mul, mul_one, Units.mul_inv]
  · intro h hh x hx
    obtain ⟨h0, hh0, rfl⟩ := Subgroup.mem_map.1 hh
    have hd : h0.val - 1 ∈ Lat Z ((m - c) + c) := by
      rw [Nat.sub_add_cancel hcm]
      exact (mem_Lc_iff Z hm h0).1 hh0
    have hy := one_add_mem_zero_lattice Z (hc _ _ hd).1
    have he : 1 + conjA g (h0.val - 1) = ((MulAut.conj g).toMonoidHom h0).val := by
      rw [conjA_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Units.val_mul,
        mul_sub, sub_mul, mul_one, Units.mul_inv]
      abel
    rw [he] at hy
    exact mul_mem_Lat_of_mem_Lat_zero Z hy hx
  · intro h
    exact mem_Lc_iff Z (hm.trans hmm) h

theorem Lc_le (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g : GL (Fin n) k) (hg : g ∈ Gz Z)
    (c : ℕ) (hc : ∀ j : ℕ, ∀ x ∈ Lat Z (j + c), conjA g x ∈ Lat Z j ∧ conjA g⁻¹ x ∈ Lat Z j)
    {m m' : ℕ} (hm : 1 ≤ m) (hmm : m + c ≤ m') :
    Lc Z m' ≤ Lc Z m ⊓ (Lc Z m).map (MulAut.conj g).toMonoidHom := by
  intro h hh
  have hm' : 1 ≤ m' := by omega
  have hx := (mem_Lc_iff Z hm' h).1 hh
  refine ⟨(mem_Lc_iff Z hm h).2 (Lat_anti Z (by omega) hx), ?_⟩
  have hx' : h.val - 1 ∈ Lat Z (m + c) := Lat_anti Z hmm hx
  have h0 : g⁻¹ * h * g ∈ Lc Z m := by
    refine (mem_Lc_iff Z hm _).2 ?_
    have := (hc m _ hx').2
    rw [conjA_apply, inv_inv] at this
    convert this using 1
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
  refine Subgroup.mem_map.2 ⟨_, h0, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end PositivityTheory.RgUd.T.Desc.SLT.Bi
end
end

section
noncomputable section

set_option linter.unusedSectionVars false

open Matrix GroundTheory.Automorphic ValuativeRel

namespace PositivityTheory.RgUd.T.Desc.SLT.Bi

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.T.Desc.SLT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def LatO (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Submodule 𝒪[k] (Matrix (Fin n) (Fin n) k) where
  carrier := Lat Z 0
  add_mem' := (Lat Z 0).add_mem
  zero_mem' := (Lat Z 0).zero_mem
  smul_mem' c x hx := by
    obtain ⟨hB, hv⟩ := (mem_Lat).1 hx
    refine (mem_Lat).2 ⟨fun a ha => ?_, fun i j => ?_⟩
    · have e : c • x = (c : k) • x := rfl
      rw [e, Matrix.mul_smul, Matrix.smul_mul, hB a ha]
    · have e : (c • x) i j = (c : k) * x i j := rfl
      rw [e, map_mul]
      have h1 : valuation k (c : k) ≤ 1 := (Valuation.mem_integer_iff _ _).mp c.2
      calc valuation k (c : k) * valuation k (x i j) ≤ 1 * valuation k (pi k) ^ 0 :=
            mul_le_mul' h1 (hv i j)
        _ = valuation k (pi k) ^ 0 := one_mul _

theorem mem_LatO {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x : Matrix (Fin n) (Fin n) k} :
    x ∈ LatO Z ↔ x ∈ Lat Z 0 := Iff.rfl

instance (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Module.Finite 𝒪[k] (LatO Z) := by
  let L : Matrix (Fin n) (Fin n) 𝒪[k] →ₗ[𝒪[k]] Matrix (Fin n) (Fin n) k :=
    (Algebra.linearMap 𝒪[k] k).mapMatrix
  have hle : LatO Z ≤ LinearMap.range L := by
    intro x hx
    refine ⟨Matrix.of fun i j => ⟨x i j, ?_⟩, ?_⟩
    · have h := (mem_Lat.1 hx).2 i j
      rw [pow_zero] at h
      exact (Valuation.mem_integer_iff _ _).mpr h
    · ext i j; rfl
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

instance (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Module.IsTorsionFree 𝒪[k] (LatO Z) :=
  Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    have h' : (r : k) • (m : Matrix (Fin n) (Fin n) k) = 0 := congrArg Subtype.val h
    rcases smul_eq_zero.1 h' with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)

example (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Module.Free 𝒪[k] (LatO Z) := inferInstance

theorem LatO_le (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ LatO Z) :
    x ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) :=
  (Subalgebra.mem_centralizer_iff k).2 fun a ha => hx.1 a ha

theorem dt_exists_scale_fin {ι : Type*} [Fintype ι] (c : ι → k) :
    ∃ N : ℕ, ∀ i, valuation k (pi k) ^ N * valuation k (c i) ≤ 1 := by
  choose N hN using fun i => exists_scale (c i)
  refine ⟨∑ i, N i, fun i => le_trans ?_ (hN i)⟩
  have h1 : valuation k (pi k) ^ (∑ i, N i) ≤ valuation k (pi k) ^ N i :=
    pow_le_pow_right_of_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le
      (Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i))
  exact mul_le_mul_left h1 _

theorem dt_smul_coe_O (o : 𝒪[k]) (x : Matrix (Fin n) (Fin n) k) : o • x = (o : k) • x := rfl

theorem det_transfer (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (F : Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) →ₗ[k]
      Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)))
    (f : LatO Z →ₗ[𝒪[k]] LatO Z) (hf : ∀ x : LatO Z, ((F ⟨x, LatO_le Z x.2⟩ : _) : Matrix (Fin n) (Fin n) k) = (f x : _)) :
    algebraMap 𝒪[k] k (LinearMap.det f) = LinearMap.det F := by
  classical
  let b := Module.Free.chooseBasis 𝒪[k] (LatO Z)
  let v : Module.Free.ChooseBasisIndex 𝒪[k] (LatO Z) → Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) :=
    fun i => ⟨(b i : Matrix (Fin n) (Fin n) k), LatO_le Z (b i).2⟩
  have hpi : pi k ≠ 0 := fun h => valuation_pi_ne_zero (k := k) (by rw [h, map_zero])
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    obtain ⟨N, hN⟩ := dt_exists_scale_fin c
    let d : _ → 𝒪[k] := fun i => ⟨pi k ^ N * c i, by
      rw [Valuation.mem_integer_iff, map_mul, map_pow]; exact hN i⟩
    have hd : ∑ i, d i • b i = 0 := by
      apply Subtype.ext
      have hc' := congrArg Subtype.val hc
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] at hc' ⊢
      simp only [dt_smul_coe_O, d]
      simp_rw [mul_smul]
      rw [← Finset.smul_sum]
      have : ∑ x, c x • (b x : Matrix (Fin n) (Fin n) k) = 0 := by
        simpa [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, v] using hc'
      rw [this, smul_zero]
    have := (Fintype.linearIndependent_iff.mp b.linearIndependent) d hd i
    have h2 : pi k ^ N * c i = 0 := congrArg Subtype.val this
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hpi)
  have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
    rintro x -
    obtain ⟨N, hN⟩ := dt_exists_scale_fin (fun p : Fin n × Fin n => (x : Matrix (Fin n) (Fin n) k) p.1 p.2)
    have hy : pi k ^ N • (x : Matrix (Fin n) (Fin n) k) ∈ LatO Z := by
      rw [mem_LatO, mem_Lat]
      refine ⟨fun a ha => ?_, fun i j => ?_⟩
      · have hx := (Subalgebra.mem_centralizer_iff k).1 x.2 a ha
        rw [mul_smul_comm, smul_mul_assoc, hx]
      · rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, pow_zero]
        exact hN (i, j)
    let y : LatO Z := ⟨_, hy⟩
    have hyx : (x : Matrix (Fin n) (Fin n) k) = ∑ i, ((pi k ^ N)⁻¹ * (b.repr y i : k)) • (b i : Matrix (Fin n) (Fin n) k) := by
      have h := congrArg Subtype.val (b.sum_repr y)
      simp only [Submodule.coe_sum, Submodule.coe_smul, dt_smul_coe_O] at h
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, h]
      show (x : Matrix (Fin n) (Fin n) k) = (pi k ^ N)⁻¹ • (pi k ^ N • (x : Matrix (Fin n) (Fin n) k))
      rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hpi), one_smul]
    have hx : x = ∑ i, ((pi k ^ N)⁻¹ * (b.repr y i : k)) • v i := by
      apply Subtype.ext
      rw [hyx]
      simp [v]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bB := Module.Basis.mk hli hsp
  have hbB : ∀ i, bB i = v i := fun i => Module.Basis.mk_apply hli hsp i
  have key : ∀ j, F (v j) = ∑ i, algebraMap 𝒪[k] k (LinearMap.toMatrix b b f i j) • v i := by
    intro j
    apply Subtype.ext
    have h1 : ((F (v j) : _) : Matrix (Fin n) (Fin n) k) = (f (b j) : _) := hf (b j)
    have h2 := congrArg Subtype.val (b.sum_repr (f (b j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, dt_smul_coe_O] at h2
    rw [h1, ← h2]
    simp only [v, LinearMap.toMatrix_apply, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    rfl
  have hM : LinearMap.toMatrix bB bB F = (LinearMap.toMatrix b b f).map (algebraMap 𝒪[k] k) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hbB, key, Matrix.map_apply]
    simp_rw [← hbB]
    rw [bB.repr_sum_self]
  rw [← LinearMap.det_toMatrix bB, hM, ← LinearMap.det_toMatrix b f, RingHom.map_det, RingHom.mapMatrix_apply]

theorem relIndex_eq_card (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (H : AddSubgroup (Matrix (Fin n) (Fin n) k))
    (f : LatO Z →ₗ[𝒪[k]] LatO Z) (hH : ∀ x, x ∈ H ↔ ∃ y, (f y : Matrix (Fin n) (Fin n) k) = x) :
    H.relIndex (Lat Z 0) = Nat.card (LatO Z ⧸ LinearMap.range f) := by
  let φ : LatO Z →+ Lat Z 0 :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := fun x => ⟨⟨x.1, x.2⟩, rfl⟩
  have e : (H.addSubgroupOf (Lat Z 0)).comap φ = (LinearMap.range f).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hH, Submodule.mem_toAddSubgroup,
      LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, Subtype.ext hy⟩
    · rintro ⟨y, hy⟩; exact ⟨y, congrArg Subtype.val hy⟩
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφ, e]
  rfl

theorem card_quot_ne_zero {c : 𝒪[k]} (hc : c ≠ 0) : Nat.card (𝒪[k] ⧸ Ideal.span {c}) ≠ 0 := by
  have : Finite (𝒪[k] ⧸ Ideal.span {c}) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := Ideal.span {c}) (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hc) hϖ
    rw [IsLocalRing.finite_quotient_iff]
    refine ⟨m, ?_⟩
    rw [hm, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact Nat.card_pos.ne'

theorem core [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (g : GL (Fin n) k)
    (hg : g ∈ Gz Z) : ∃ c : ℕ, ∀ r ≥ c, ((Lat Z r).map (conjA g⁻¹)).relIndex (Lat Z 0) = (Lat Z r).relIndex (Lat Z 0) ∧
      (Lat Z r).relIndex (Lat Z 0) ≠ 0 := by
  obtain ⟨c, -, hc⟩ := exists_shift Z g hg
  refine ⟨c, fun r hr => ?_⟩
  have hg' : g⁻¹ ∈ Gz Z := (GzS Z).inv_mem hg
  have hL : Lat Z r = (Lat Z 0).map (smulA (pi k ^ r)) := by simpa using Lat_add Z r 0
  have hmem : ∀ y ∈ Lat Z 0, pi k ^ r • conjA g⁻¹ y ∈ Lat Z 0 := by
    intro y hy
    have h1 : smulA (pi k ^ r) y ∈ Lat Z ((r - c) + c) := by
      rw [show r - c + c = r by omega, hL]; exact ⟨y, hy, rfl⟩
    have h2 := (hc _ _ h1).2
    rw [conjA_smulA] at h2
    exact Lat_anti Z (Nat.zero_le _) h2
  let ϖ : 𝒪[k] := GLnLocal.uniformizer k
  have hϖ0 : ϖ ≠ 0 := (GLnLocal.irreducible_uniformizer k).ne_zero
  have hϖk : ((ϖ ^ r : 𝒪[k]) : k) = pi k ^ r := by simp [ϖ]
  let f1 : LatO Z →ₗ[𝒪[k]] LatO Z := (ϖ ^ r) • LinearMap.id
  let f2 : LatO Z →ₗ[𝒪[k]] LatO Z :=
    { toFun := fun y => ⟨pi k ^ r • conjA g⁻¹ y, hmem y y.2⟩
      map_add' := fun x y => Subtype.ext (by simp [mul_add, add_mul, smul_add])
      map_smul' := fun a y => Subtype.ext (by
        change pi k ^ r • conjA g⁻¹ ((a : k) • (y : Matrix (Fin n) (Fin n) k)) =
          (a : k) • (pi k ^ r • conjA g⁻¹ (y : Matrix (Fin n) (Fin n) k))
        rw [← smulA_apply (a : k), conjA_smulA, smulA_apply, smul_comm]) }
  let B := Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))
  let F1 : B →ₗ[k] B := (pi k ^ r) • LinearMap.id
  let F2 : B →ₗ[k] B := (pi k ^ r) • PositivityTheory.RgUd.T.Desc.UniPf.conjL Z g⁻¹ hg'
  have t1 := det_transfer Z F1 f1 (fun x => by
    change pi k ^ r • (x : Matrix (Fin n) (Fin n) k) = ((ϖ ^ r : 𝒪[k]) : k) • (x : Matrix (Fin n) (Fin n) k)
    rw [hϖk])
  have t2 := det_transfer Z F2 f2 (fun x => rfl)
  have dF : LinearMap.det F1 = LinearMap.det F2 := by
    simp only [F1, F2, LinearMap.det_smul, LinearMap.det_id,
      PositivityTheory.RgUd.T.Desc.UniPf.det_conjL Z hZ g⁻¹ hg']
  have df : LinearMap.det f1 = LinearMap.det f2 := Subtype.val_injective (t1.trans (dF.trans t2.symm))
  have hf1 : LinearMap.det f1 ≠ 0 := by
    simp only [f1, LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ (pow_ne_zero _ hϖ0)
  have i1 : (Lat Z r).relIndex (Lat Z 0) = Nat.card (LatO Z ⧸ LinearMap.range f1) := by
    refine relIndex_eq_card Z _ f1 fun x => ?_
    rw [hL, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      change ((ϖ ^ r : 𝒪[k]) : k) • y = smulA (pi k ^ r) y
      rw [hϖk]; rfl
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      change smulA (pi k ^ r) (y : Matrix (Fin n) (Fin n) k) = ((ϖ ^ r : 𝒪[k]) : k) • (y : Matrix (Fin n) (Fin n) k)
      rw [hϖk]; rfl
  have i2 : ((Lat Z r).map (conjA g⁻¹)).relIndex (Lat Z 0) = Nat.card (LatO Z ⧸ LinearMap.range f2) := by
    refine relIndex_eq_card Z _ f2 fun x => ?_
    rw [hL, AddSubgroup.map_map, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      change pi k ^ r • conjA g⁻¹ y = conjA g⁻¹ (smulA (pi k ^ r) y)
      rw [conjA_smulA]; rfl
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      change conjA g⁻¹ (smulA (pi k ^ r) (y : Matrix (Fin n) (Fin n) k)) = pi k ^ r • conjA g⁻¹ (y : Matrix (Fin n) (Fin n) k)
      rw [conjA_smulA]; rfl
  have c1 := PI.NGStepBBW.card_coker_endo f1 hf1
  have c2 := PI.NGStepBBW.card_coker_endo f2 (df ▸ hf1)
  refine ⟨?_, ?_⟩
  · rw [i1, i2, c1, c2, df]
  · rw [i1, c1]
    exact card_quot_ne_zero hf1

end PositivityTheory.RgUd.T.Desc.SLT.Bi
end
end

section
noncomputable section

open Matrix GroundTheory.Automorphic

namespace PositivityTheory.RgUd.T.Desc.SLT

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.T.Desc.SLT.Bi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem Bi.Lat_eq_map (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) :
    Lat Z m = (Lat Z 0).map (smulA (pi k ^ m)) := by
  simpa using Lat_add Z m 0

private theorem smulA_injective' (m : ℕ) :
    Function.Injective (smulA (k := k) (n := n) (pi k ^ m)) := by
  have hp : pi k ^ m ≠ 0 :=
    pow_ne_zero _ ((Valuation.ne_zero_iff _).1 (GLnLocal.valuation_uniformizer_ne_zero k))
  intro x y hxy
  exact smul_right_injective (Matrix (Fin n) (Fin n) k) hp hxy

theorem Bi.relIndex_lat (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m r : ℕ) :
    (Lat Z (m + r)).relIndex (Lat Z m) = (Lat Z r).relIndex (Lat Z 0) := by
  rw [Lat_add Z m r, Lat_eq_map Z m,
    AddSubgroup.relIndex_map_map_of_injective _ _ (smulA_injective' m)]

theorem Bi.relIndex_lat_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g : GL (Fin n) k) (m r : ℕ) :
    (Lat Z (m + r)).relIndex ((Lat Z m).map (conjA g)) = ((Lat Z r).map (conjA g⁻¹)).relIndex (Lat Z 0) := by
  rw [Lat_add Z m r, Lat_eq_map Z m]
  have hcomm : ((Lat Z 0).map (smulA (pi k ^ m))).map (conjA g) =
      ((Lat Z 0).map (conjA g)).map (smulA (pi k ^ m)) := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    ext1 x
    exact conjA_smulA g _ x
  rw [hcomm, AddSubgroup.relIndex_map_map_of_injective _ _ (smulA_injective' m)]
  have hid : (conjA g⁻¹).comp (conjA g) = AddMonoidHom.id _ := by
    ext1 x
    exact conjA_inv_conjA g x
  have := AddSubgroup.relIndex_map_map_of_injective (Lat Z r) ((Lat Z 0).map (conjA g))
    (conjA_injective g⁻¹)
  rw [AddSubgroup.map_map, hid, AddSubgroup.map_id] at this
  exact this.symm

theorem indexSym [CharZero k] : IndexSym (k := k) := by
  intro n Z hZ g hg
  obtain ⟨c0, hc01, hc0⟩ := exists_shift Z g hg
  obtain ⟨c1, hc1⟩ := core Z hZ g hg
  refine ⟨c0 + c1, fun m hm m' hm' => ?_⟩
  have h1m : 1 ≤ m := by omega
  obtain ⟨r, rfl⟩ : ∃ r, m' = m + r := ⟨m' - m, by omega⟩
  have hr : c1 ≤ r := by omega
  refine ⟨Lc_le Z g hg c0 hc0 h1m (by omega), ?_, ?_⟩
  · rw [relIndex_Lc_conj Z g hg c0 hc0 h1m (by omega) (by omega), relIndex_Lc Z h1m (by omega),
      Bi.relIndex_lat_conj, Bi.relIndex_lat]
    exact (hc1 r hr).1
  · rw [relIndex_Lc Z h1m (by omega), Bi.relIndex_lat]
    exact (hc1 r hr).2

end PositivityTheory.RgUd.T.Desc.SLT
end
end
