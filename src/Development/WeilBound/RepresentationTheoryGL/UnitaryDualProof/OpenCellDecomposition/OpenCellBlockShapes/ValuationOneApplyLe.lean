import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellBlockShapes.VolRelIndex
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.BlockIndexOfWeylShuffle

section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped NNReal ENNReal Pointwise

namespace PositivityTheory.RgUd.CellB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem addHaar_smul_set_eq_distribHaarChar_mul {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]
    [DistribMulAction kˣ A] [ContinuousConstSMul kˣ A] (μ : Measure A) [μ.IsAddHaarMeasure]
    (z : kˣ) {s : Set A} (hs : IsCompact (closure s)) :
    μ (z • s) = distribHaarChar A z * μ s := by
  have h := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure (DomMulAct.mk z • μ) μ hs
  rw [addHaarScalarFactor_smul_eq_distribHaarChar] at h
  have h2 : (DomMulAct.mk z • μ) s = μ (z • s) := by simp [Measure.domSMul_apply]
  rw [← h2, h, ENNReal.smul_def, smul_eq_mul]

theorem distribHaarChar_pi (ι : Type) [Fintype ι] (z : kˣ) :
    ((distribHaarChar (ι → k) z : ℝ≥0) : ℝ) = nabs k z ^ Fintype.card ι := by
  borelize k
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : k)
  have hK1 : (Measure.addHaar : Measure k) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hK2 : (Measure.addHaar : Measure k) K ≠ ∞ := hK.measure_lt_top.ne
  have e1 : (Measure.addHaar : Measure k) (z • K) =
      distribHaarChar k z * (Measure.addHaar : Measure k) K :=
    addHaar_smul_set_eq_distribHaarChar_mul _ z hK.closure
  have hs : IsCompact (Set.univ.pi (fun _ : ι => K)) := isCompact_univ_pi (fun _ => hK)
  have e2 := addHaar_smul_set_eq_distribHaarChar_mul (Measure.pi (fun _ : ι => (Measure.addHaar : Measure k))) z hs.closure
  rw [Set.smul_set_univ_pi, Measure.pi_pi, Measure.pi_pi] at e2
  simp only [Pi.smul_apply, e1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at e2
  have e3 : ((distribHaarChar k z : ℝ≥0∞)) ^ Fintype.card ι = (distribHaarChar (ι → k) z : ℝ≥0∞) :=
    (ENNReal.mul_left_inj (pow_ne_zero _ hK1) (ENNReal.pow_ne_top hK2)).1 e2
  rw [← ENNReal.coe_pow, ENNReal.coe_inj] at e3
  simp only [nabs, ← e3, NNReal.coe_pow]

private theorem relIndex_map_smul_eq_inv_distribHaarChar {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]
    [MeasurableAdd A] [DistribMulAction kˣ A] [ContinuousConstSMul kˣ A] (μ : Measure A)
    [μ.IsAddHaarMeasure] (S : AddSubgroup A) (hc : IsCompact (S : Set A))
    (ho : IsOpen (S : Set A)) (z : kˣ) (hz : ∀ x ∈ S, z • x ∈ S) :
    ((S.map (DistribSMul.toAddMonoidHom A z)).relIndex S : ℝ) =
      ((distribHaarChar A z : ℝ≥0) : ℝ)⁻¹ := by
  set T := S.map (DistribSMul.toAddMonoidHom A z) with hT
  have hTset : (T : Set A) = z • (S : Set A) := by
    rw [hT, AddSubgroup.coe_map]
    rfl
  have hTS : T ≤ S := by
    intro x hx
    rw [← SetLike.mem_coe, hTset] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hz y hy
  have hTo : IsOpen (T : Set A) := by
    rw [hTset]
    exact ho.smul z
  have hne : T.relIndex S ≠ 0 := addRelIndex_ne_zero hTS le_rfl hc hTo (Set.inter_eq_left.2 hTS)
  have hSm : MeasurableSet (S : Set A) := ho.measurableSet
  have hemb : MeasurableEmbedding (S.subtype) := MeasurableEmbedding.subtype_coe hSm
  haveI : (μ.comap S.subtype).IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ hemb
  haveI : (T.addSubgroupOf S).FiniteIndex := ⟨hne⟩
  have hHm : MeasurableSet ((T.addSubgroupOf S : AddSubgroup S) : Set S) :=
    measurable_subtype_coe hTo.measurableSet
  have key := AddSubgroup.index_mul_measure (T.addSubgroupOf S) hHm (μ.comap S.subtype)
  rw [hemb.comap_apply, hemb.comap_apply, Set.image_univ, AddSubgroup.coe_addSubgroupOf,
    Set.image_preimage_eq_inter_range] at key
  simp only [AddSubgroup.coe_subtype, Subtype.range_coe_subtype, SetLike.setOf_mem_eq] at key
  rw [Set.inter_eq_left.2 hTS, hTset, addHaar_smul_set_eq_distribHaarChar_mul μ z hc.closure, ← mul_assoc] at key
  have hS0 : μ S ≠ 0 := (ho.measure_pos μ ⟨0, S.zero_mem⟩).ne'
  have hSt : μ S ≠ ∞ := hc.measure_lt_top.ne
  have h1 : ((T.relIndex S : ℝ≥0∞)) * (distribHaarChar A z : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hS0 hSt).1 (key.trans (one_mul _).symm)
  have h2 : (T.relIndex S : ℝ) * ((distribHaarChar A z : ℝ≥0) : ℝ) = 1 := by
    have := congrArg ENNReal.toReal h1
    simpa using this
  exact eq_inv_of_mul_eq_one_left h2

theorem relIndex_smul (ι : Type) [Fintype ι] (S : AddSubgroup (ι → k)) (hc : IsCompact (S : Set (ι → k)))
    (ho : IsOpen (S : Set (ι → k))) (z : kˣ) (hz : ∀ x ∈ S, z • x ∈ S) :
    ((S.map (DistribSMul.toAddMonoidHom (ι → k) z)).relIndex S : ℝ) = (nabs k z)⁻¹ ^ Fintype.card ι := by
  borelize k
  rw [relIndex_map_smul_eq_inv_distribHaarChar (Measure.pi (fun _ : ι => (Measure.addHaar : Measure k))) S hc ho z hz,
    distribHaarChar_pi, inv_pow]

theorem relIndex_conj {G : Type*} [Group G] (ι : Type) [Fintype ι] (U : Subgroup G)
    (φ : U ≃* Multiplicative (ι → k)) (a : G) (z : kˣ) (haU : ∀ u ∈ U, a * u * a⁻¹ ∈ U)
    (hφ : ∀ (u : G) (hu : u ∈ U),
      Multiplicative.toAdd (φ ⟨a * u * a⁻¹, haU u hu⟩) = z • Multiplicative.toAdd (φ ⟨u, hu⟩))
    (L₀ : Subgroup G) (hL₀ : L₀ ≤ U) (S : AddSubgroup (ι → k))
    (hS : ∀ (u : G) (hu : u ∈ U), u ∈ L₀ ↔ Multiplicative.toAdd (φ ⟨u, hu⟩) ∈ S)
    (hc : IsCompact (S : Set (ι → k))) (ho : IsOpen (S : Set (ι → k))) (hz : ∀ x ∈ S, z • x ∈ S) :
    L₀.map (MulAut.conj a).toMonoidHom ≤ L₀ ∧
      ((L₀.map (MulAut.conj a).toMonoidHom).relIndex L₀ : ℝ) = (nabs k z)⁻¹ ^ Fintype.card ι := by
  set f : Multiplicative (ι → k) →* G := U.subtype.comp φ.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp φ.symm.injective
  set m : Multiplicative (ι → k) →* Multiplicative (ι → k) :=
    AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom (ι → k) z) with hmdef
  set T := S.map (DistribSMul.toAddMonoidHom (ι → k) z) with hT
  have hTS : T ≤ S := by
    rintro x ⟨y, hy, rfl⟩
    exact hz y hy
  have hL : L₀ = (AddSubgroup.toSubgroup S).map f := by
    ext g
    constructor
    · intro hg
      have hu := hL₀ hg
      refine ⟨φ ⟨g, hu⟩, (hS g hu).1 hg, ?_⟩
      simp [hfdef]
    · rintro ⟨x, hx, rfl⟩
      have hu : ((φ.symm x : U) : G) ∈ U := (φ.symm x).2
      refine (hS _ hu).2 ?_
      simpa using hx
  have hcf : (MulAut.conj a).toMonoidHom.comp f = f.comp m := by
    refine MonoidHom.ext fun y => ?_
    have h2 : φ ⟨a * (φ.symm y : G) * a⁻¹, haU _ (φ.symm y).2⟩ =
        Multiplicative.ofAdd (z • Multiplicative.toAdd y) := by
      rw [← ofAdd_toAdd (φ _), hφ _ (φ.symm y).2]
      simp
    have h3 := (MulEquiv.symm_apply_eq φ).2 h2.symm
    have h4 : m y = Multiplicative.ofAdd (z • Multiplicative.toAdd y) := rfl
    show a * (φ.symm y : G) * a⁻¹ = ((φ.symm (m y) : U) : G)
    rw [h4, h3]
  have hTm : AddSubgroup.toSubgroup T = (AddSubgroup.toSubgroup S).map m := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨Multiplicative.ofAdd y, hy, by simp [hmdef, hxy]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Multiplicative.toAdd y, hy, by simp [hmdef]⟩
  have hmap : L₀.map (MulAut.conj a).toMonoidHom = (AddSubgroup.toSubgroup T).map f := by
    rw [hL, Subgroup.map_map, hcf, ← Subgroup.map_map, ← hTm]
  refine ⟨?_, ?_⟩
  · rw [hmap, hL]
    exact Subgroup.map_mono (fun x hx => hTS hx)
  · rw [hmap, hL, Subgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_toSubgroup]
    exact relIndex_smul ι S hc ho z hz

end PositivityTheory.RgUd.CellB
end

section
open Matrix GlobalTheory.SmGL ValuativeRel
open scoped Pointwise

noncomputable section

namespace PositivityTheory.RgUd.CellB

variable {k : Type} [Field k]

variable {r m : ℕ}

def rowI (i : Fin m) : Fin (r + m) := ⟨i, by omega⟩

def colI (j : Fin r) : Fin (r + m) := ⟨m + j, by omega⟩

variable (r) in

def blockE (Y : Fin m × Fin r → k) : Matrix (Fin (r + m)) (Fin (r + m)) k := fun i j =>
  if h : (i : ℕ) < m ∧ m ≤ (j : ℕ) then Y (⟨i, h.1⟩, ⟨j - m, by omega⟩) else 0

theorem blockE_mul (Y Y' : Fin m × Fin r → k) : blockE r Y * blockE r Y' = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro l _
  unfold blockE
  by_cases hl : (l : ℕ) < m
  · have hl' : ¬ m ≤ (l : ℕ) := by omega
    simp [hl']
  · simp [hl]

theorem blockE_apply (Y : Fin m × Fin r → k) (i : Fin m) (j : Fin r) :
    blockE r Y (rowI i) (colI j) = Y (i, j) := by
  unfold blockE
  have hc : ((rowI (r := r) i : Fin (r + m)) : ℕ) < m ∧ m ≤ ((colI (m := m) j : Fin (r + m)) : ℕ) := by
    simp [rowI, colI]
  rw [dif_pos hc]
  congr 2
  all_goals
    apply Fin.ext
    simp [rowI, colI]

theorem one_rowI_colI (i : Fin m) (j : Fin r) : (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) (rowI i) (colI j) = 0 := by
  rw [Matrix.one_apply_ne]
  intro h
  have := congrArg Fin.val h
  simp [rowI, colI] at this
  omega

def blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k) : Fin m × Fin r → k := fun p => u (rowI p.1) (colI p.2)

def IsBlockShape (u : Matrix (Fin (r + m)) (Fin (r + m)) k) : Prop :=
  ∀ i j, u i j ≠ (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j → (i : ℕ) < m ∧ m ≤ (j : ℕ)

theorem eq_one_add_blockE {u : Matrix (Fin (r + m)) (Fin (r + m)) k} (hu : IsBlockShape u) :
    u = 1 + blockE r (blockY u) := by
  ext i j
  rw [Matrix.add_apply]
  unfold blockE
  by_cases hij : (i : ℕ) < m ∧ m ≤ (j : ℕ)
  · rw [dif_pos hij]
    have hne : i ≠ j := by
      intro h
      rw [h] at hij
      omega
    rw [Matrix.one_apply_ne hne, zero_add]
    show u i j = u (rowI _) (colI _)
    congr 1
    all_goals
      apply Fin.ext
      simp only [rowI, colI]
      try omega
  · rw [dif_neg hij, add_zero]
    by_contra h
    exact hij (hu i j h)

theorem isBlockShape_one_add (Y : Fin m × Fin r → k) : IsBlockShape (1 + blockE r Y) := by
  intro i j h
  rw [Matrix.add_apply] at h
  unfold blockE at h
  by_contra hc
  rw [dif_neg hc, add_zero] at h
  exact h rfl

def blockGL (Y : Fin m × Fin r → k) : GL (Fin (r + m)) k :=
  ⟨1 + blockE r Y, 1 - blockE r Y, by rw [add_mul, one_mul, mul_sub, mul_one, blockE_mul, sub_zero, sub_add_cancel],
    by rw [sub_mul, one_mul, mul_add, mul_one, blockE_mul, add_zero, add_sub_cancel_right]⟩

theorem blockGL_mem_unipB (Y : Fin m × Fin r → k) : blockGL Y ∈ unipB k (Fin (r + m)) := by
  rw [mem_unipB]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · show (1 + blockE r Y) i j = 0
    have hlt : (j : ℕ) < i := Fin.lt_iff_val_lt_val.mp hji
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hji).symm, zero_add]
    unfold blockE
    rw [dif_neg (by omega)]
  · show (1 + blockE r Y) i i = 1
    rw [Matrix.add_apply, Matrix.one_apply_eq]
    unfold blockE
    rw [dif_neg (by omega), add_zero]

def blockEquiv (U : Subgroup (GL (Fin (r + m)) k))
    (hU : ∀ u, u ∈ U ↔ u ∈ unipB k (Fin (r + m)) ∧ IsBlockShape (u : Matrix (Fin (r + m)) (Fin (r + m)) k)) :
    U ≃* Multiplicative (Fin m × Fin r → k) where
  toFun u := Multiplicative.ofAdd (blockY (u : GL (Fin (r + m)) k).1)
  invFun Y := ⟨blockGL (Multiplicative.toAdd Y), (hU _).2 ⟨blockGL_mem_unipB _, isBlockShape_one_add _⟩⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    show 1 + blockE r (blockY (u : GL (Fin (r + m)) k).1) = _
    exact (eq_one_add_blockE ((hU u.1).1 u.2).2).symm
  right_inv Y := by
    apply Multiplicative.toAdd.injective
    funext p
    show (1 + blockE r (Multiplicative.toAdd Y)) (rowI p.1) (colI p.2) = _
    rw [Matrix.add_apply, one_rowI_colI, zero_add, blockE_apply]
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    funext p
    show ((u : GL (Fin (r + m)) k).1 * (v : GL (Fin (r + m)) k).1) (rowI p.1) (colI p.2) =
      (u : GL (Fin (r + m)) k).1 (rowI p.1) (colI p.2) + (v : GL (Fin (r + m)) k).1 (rowI p.1) (colI p.2)
    have hu := eq_one_add_blockE ((hU u.1).1 u.2).2
    have hv := eq_one_add_blockE ((hU v.1).1 v.2).2
    rw [hu, hv, add_mul, one_mul, mul_add, mul_one, blockE_mul, add_zero]
    simp only [Matrix.add_apply, one_rowI_colI, blockE_apply, zero_add]
    ring

theorem blockEquiv_apply (U : Subgroup (GL (Fin (r + m)) k))
    (hU : ∀ u, u ∈ U ↔ u ∈ unipB k (Fin (r + m)) ∧ IsBlockShape (u : Matrix (Fin (r + m)) (Fin (r + m)) k))
    (u : U) (i : Fin m) (j : Fin r) :
    Multiplicative.toAdd (blockEquiv U hU u) (i, j) = (u : GL (Fin (r + m)) k).1 (rowI i) (colI j) := rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (ι : Type) (γ : ValueGroupWithZero k) : AddSubgroup (ι → k) where
  carrier := {Y | ∀ i, valuation k (Y i) ≤ γ}
  add_mem' {a b} ha hb i := ((valuation k).map_add (a i) (b i)).trans (max_le (ha i) (hb i))
  zero_mem' i := by simp
  neg_mem' {a} ha i := by simpa using ha i

theorem mem_box {ι : Type} {γ : ValueGroupWithZero k} {Y : ι → k} : Y ∈ box ι γ ↔ ∀ i, valuation k (Y i) ≤ γ := Iff.rfl

theorem ball_eq_smul (c : kˣ) : {x : k | valuation k x ≤ valuation k (c : k)} = c • (𝒪[k] : Set k) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have hc : 0 < valuation k (c : k) := by
    rw [zero_lt_iff]
    simp
  have key : valuation k (((c⁻¹ : kˣ) : k) * x) = (valuation k (c : k))⁻¹ * valuation k x := by
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  show valuation k x ≤ valuation k (c : k) ↔ valuation k (((c⁻¹ : kˣ) : k) * x) ≤ 1
  rw [key, inv_mul_le_iff₀ hc, mul_one]

theorem isCompact_box (ι : Type) [Fintype ι] (c : kˣ) : IsCompact (box ι (valuation k (c : k)) : Set (ι → k)) := by
  have hset : (box ι (valuation k (c : k)) : Set (ι → k)) =
      Set.univ.pi (fun _ => {x : k | valuation k x ≤ valuation k (c : k)}) := by
    ext Y
    simp [mem_box]
  rw [hset]
  exact isCompact_univ_pi (fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _)

theorem isOpen_box (ι : Type) [Fintype ι] (c : kˣ) : IsOpen (box ι (valuation k (c : k)) : Set (ι → k)) := by
  have hset : (box ι (valuation k (c : k)) : Set (ι → k)) =
      Set.univ.pi (fun _ => {x : k | valuation k x ≤ valuation k (c : k)}) := by
    ext Y
    simp [mem_box]
  have hball : IsOpen {x : k | valuation k x ≤ valuation k (c : k)} := by
    rw [ball_eq_smul]
    exact ((valuation k).isOpen_integer).smul c
  rw [hset]
  exact isOpen_set_pi Set.finite_univ (fun _ _ => hball)

theorem smul_mem_box {ι : Type} {γ : ValueGroupWithZero k} (z : kˣ) (hz : valuation k (z : k) ≤ 1) {Y : ι → k}
    (hY : Y ∈ box ι γ) : z • Y ∈ box ι γ := by
  rw [mem_box] at hY ⊢
  intro i
  rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, map_mul]
  calc valuation k (z : k) * valuation k (Y i) ≤ 1 * γ := mul_le_mul' hz (hY i)
    _ = γ := one_mul γ

end PositivityTheory.RgUd.CellB
end
end

section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier ValuativeRel GroundTheory.Automorphic.GLnLocal
open GlobalTheory.SplitWeil PositivityTheory.RgUd.CellA

noncomputable section

namespace PositivityTheory.RgUd.CellB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem valuation_blockE_le {r m : ℕ} {γ : ValueGroupWithZero k} {Y : Fin m × Fin r → k}
    (hY : Y ∈ box (Fin m × Fin r) γ) (i j : Fin (r + m)) : valuation k (blockE r Y i j) ≤ γ := by
  unfold blockE
  split_ifs
  · exact hY _
  · simp

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem valuation_one_apply_le {N : ℕ} (i j : Fin N) : valuation k ((1 : Matrix (Fin N) (Fin N) k) i j) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem mem_congr_iff_box {r m : ℕ} (n : ℕ) {u : GL (Fin (r + m)) k}
    (hu : IsBlockShape (u : Matrix (Fin (r + m)) (Fin (r + m)) k)) :
    u ∈ congruenceSubgroup k (r + m) n ↔
      blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k) ∈
        box (Fin m × Fin r) (valuation k (uniformizer k : k) ^ n) := by
  have hE := eq_one_add_blockE hu
  have hγ : valuation k (uniformizer k : k) ^ n ≤ 1 :=
    pow_le_one₀ zero_le' (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one k).le
  rw [GroundTheory.Automorphic.GLnLocal.mem_congruenceSubgroup_iff, mem_box]
  constructor
  · rintro ⟨-, h⟩ ⟨i, j⟩
    simpa only [blockY, one_rowI_colI, sub_zero] using h (rowI i) (colI j)
  · intro hY
    have hY' : blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k) ∈
        box (Fin m × Fin r) (valuation k (uniformizer k : k) ^ n) := mem_box.2 hY
    have hent : ∀ i j, valuation k ((u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j -
        (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j) ≤ valuation k (uniformizer k : k) ^ n := by
      intro i j
      rw [hE, Matrix.add_apply, add_sub_cancel_left]
      exact valuation_blockE_le hY' i j
    refine ⟨(GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff k _).2 ⟨fun i j => ?_, fun i j => ?_⟩, hent⟩
    · show valuation k _ ≤ 1
      have e : (u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j = (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j +
          ((u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j - (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j) := by
        ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le (valuation_one_apply_le i j) ((hent i j).trans hγ))
    · have hinv : ((u⁻¹ : GL (Fin (r + m)) k) : Matrix (Fin (r + m)) (Fin (r + m)) k) =
          1 - blockE r (blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k)) := by
        apply Units.inv_eq_of_mul_eq_one_right
        calc (u : Matrix (Fin (r + m)) (Fin (r + m)) k) *
              (1 - blockE r (blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k)))
            = (1 + blockE r (blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k))) *
              (1 - blockE r (blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k))) := by rw [← hE]
          _ = 1 := by
            simp only [add_mul, mul_sub, one_mul, mul_one, blockE_mul]
            abel
      show valuation k _ ≤ 1
      rw [hinv, Matrix.sub_apply]
      exact (Valuation.map_sub _ _ _).trans
        (max_le (valuation_one_apply_le i j) ((valuation_blockE_le hY' i j).trans hγ))

abbrev congrL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r m n : ℕ) :
    Subgroup (GL (Fin (r + m)) k) :=
  unipU k (dd r m) (hdd r m) ⊓ (congruenceSubgroup k (r + m) n).comap (MulAut.conj (pm k (wOpen (dd r m) (hdd r m)))).toMonoidHom

theorem mem_congrL {r m n : ℕ} {u : GL (Fin (r + m)) k} :
    u ∈ congrL k r m n ↔ u ∈ unipU k (dd r m) (hdd r m) ∧ u ∈ congruenceSubgroup k (r + m) n := by
  rw [congrL, Subgroup.mem_inf, Subgroup.mem_comap]
  refine and_congr_right fun _ => ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pm]
  constructor
  · intro h
    have := GroundTheory.Automorphic.Parabolic.permGL_conj_mem_congruenceSubgroup
      (w := (wOpen (dd r m) (hdd r m))⁻¹) h
    simpa [map_inv, mul_assoc] using this
  · exact GroundTheory.Automorphic.Parabolic.permGL_conj_mem_congruenceSubgroup

set_option maxHeartbeats 1000000 in

theorem vol_conj_aDiag (ψ : AddChar k Circle) {r m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (dd r m a)) W) (J : openFns (dd r m) (hdd r m) ρ →ₗ[ℂ] W)
    (vol : Subgroup (GL (Fin (r + m)) k) → ℝ)
    (hU : ∀ (u : GL (Fin (r + m)) k) (hu : u ∈ unipU k (dd r m) (hdd r m)) (hb : u ∈ unipB k (Fin (r + m)))
      (f f' : openFns (dd r m) (hdd r m) ρ), (f' : IndSp (stdBlocks (dd r m) (hdd r m)) ρ) = parInd (stdBlocks (dd r m) (hdd r m)) ρ u f →
        J f' = (whitChar ψ (r + m) ⟨u, hb⟩ : ℂ) • J f)
    (hV : ∀ L₀ : Subgroup (GL (Fin (r + m)) k), L₀ ≤ unipU k (dd r m) (hdd r m) → IsCompact (L₀ : Set (GL (Fin (r + m)) k)) →
      (∃ O : Set (GL (Fin (r + m)) k), IsOpen O ∧ O ∩ (unipU k (dd r m) (hdd r m) : Set (GL (Fin (r + m)) k)) = L₀) →
      0 < vol L₀ ∧ ∀ (f : openFns (dd r m) (hdd r m) ρ) (v : W),
        (∀ (u : GL (Fin (r + m)) k) (hb : u ∈ unipB k (Fin (r + m))), u ∈ L₀ →
          f.1.1.1 (pm k (wOpen (dd r m) (hdd r m)) * u) = (whitChar ψ (r + m) ⟨u, hb⟩ : ℂ) • v) →
        (∀ u ∈ unipU k (dd r m) (hdd r m), u ∉ L₀ → f.1.1.1 (pm k (wOpen (dd r m) (hdd r m)) * u) = 0) → J f = (vol L₀ : ℂ) • v)
    (hU2 : ∀ u : GL (Fin (r + m)) k, u ∈ unipU k (dd r m) (hdd r m) ↔
      u ∈ unipB k (Fin (r + m)) ∧ IsBlockShape (u : Matrix (Fin (r + m)) (Fin (r + m)) k))
    (n : ℕ) (z : kˣ) (hz : valuation k (z : k) ≤ 1)
    (hθ : ∀ (u : GL (Fin (r + m)) k) (hb : u ∈ unipB k (Fin (r + m))), u ∈ congrL k r m n →
      whitChar ψ (r + m) ⟨u, hb⟩ = 1)
    (g : openFns (dd r m) (hdd r m) ρ) (v : W) (hv : v ≠ 0)
    (hg1 : ∀ u ∈ (congrL k r m n).map (MulAut.conj (aDiag k (r + m) m z)).toMonoidHom,
      g.1.1.1 (pm k (wOpen (dd r m) (hdd r m)) * u) = v)
    (hg0 : ∀ u ∈ unipU k (dd r m) (hdd r m), u ∉ (congrL k r m n).map (MulAut.conj (aDiag k (r + m) m z)).toMonoidHom →
      g.1.1.1 (pm k (wOpen (dd r m) (hdd r m)) * u) = 0) :
    vol ((congrL k r m n).map (MulAut.conj (aDiag k (r + m) m z)).toMonoidHom) =
      nabs k z ^ (m * r) * vol (congrL k r m n) := by
  set U := unipU k (dd r m) (hdd r m) with hUdef
  set a := aDiag k (r + m) m z with hadef
  set L₀ := congrL k r m n with hL₀def
  set C := congruenceSubgroup k (r + m) n with hCdef
  have hL₀U : L₀ ≤ U := inf_le_left
  have hmemL₀ : ∀ u, u ∈ L₀ ↔ u ∈ U ∧ u ∈ C := fun u => mem_congrL
  have haU : ∀ u ∈ U, a * u * a⁻¹ ∈ U := fun u hu => aDiag_conj_mem_unipU k z hu
  have haU' : ∀ u ∈ U, a⁻¹ * u * a ∈ U := by
    intro u hu
    have := aDiag_conj_mem_unipU k z⁻¹ hu
    rwa [← aDiag_inv, inv_inv] at this
  have hφ : ∀ (u : GL (Fin (r + m)) k) (hu : u ∈ U),
      Multiplicative.toAdd (blockEquiv U hU2 ⟨u, hu⟩) = blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k) := by
    intro u hu
    funext p
    exact blockEquiv_apply U hU2 ⟨u, hu⟩ p.1 p.2
  have hc0 : (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ≠ 0 :=
    GroundTheory.Automorphic.GLnLocal.uniformizer_ne_zero k
  set c : kˣ := (Units.mk0 _ hc0) ^ n with hcdef
  have hvc : valuation k (c : k) = valuation k (uniformizer k : k) ^ n := by
    simp [c, map_pow]
  have hUclosed : IsClosed (U : Set (GL (Fin (r + m)) k)) := by
    have e : (U : Set (GL (Fin (r + m)) k)) = {u : GL (Fin (r + m)) k | ∀ i j : Fin (r + m),
        ¬ ((i : ℕ) < m ∧ m ≤ (j : ℕ)) →
        (u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j = (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j} := by
      ext u
      simp only [SetLike.mem_coe, Set.mem_setOf_eq]
      rw [hU2]
      constructor
      · rintro ⟨-, hs⟩ i j hij
        by_contra hne
        exact hij (hs i j hne)
      · intro H
        refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, fun i j hne => ?_⟩
        · rw [H i j (fun h => absurd (lt_of_lt_of_le h.1 h.2) (not_lt.mpr (Fin.le_def.mp hji.le)))]
          exact Matrix.one_apply_ne hji.ne'
        · rw [H i i (fun h => absurd (lt_of_lt_of_le h.1 h.2) (lt_irrefl _))]
          exact Matrix.one_apply_eq i
        · by_contra hc
          exact hne (H i j hc)
    rw [e]
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
  have hL₀set : (L₀ : Set (GL (Fin (r + m)) k)) = (C : Set (GL (Fin (r + m)) k)) ∩ U := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_inter_iff, hmemL₀]
    tauto
  have hcomp₀ : IsCompact (L₀ : Set (GL (Fin (r + m)) k)) := by
    rw [hL₀set]
    exact (GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k (r + m) n).inter_right hUclosed
  have hopen₀ : ∃ O : Set (GL (Fin (r + m)) k), IsOpen O ∧ O ∩ (U : Set (GL (Fin (r + m)) k)) = L₀ :=
    ⟨C, GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k (r + m) n, hL₀set.symm⟩
  have hcont : Continuous fun u : GL (Fin (r + m)) k => a * u * a⁻¹ := by fun_prop
  have hcomp : IsCompact ((L₀.map (MulAut.conj a).toMonoidHom : Subgroup _) : Set (GL (Fin (r + m)) k)) := by
    rw [Subgroup.coe_map]
    exact hcomp₀.image hcont
  have hopen : ∃ O : Set (GL (Fin (r + m)) k), IsOpen O ∧
      O ∩ (U : Set (GL (Fin (r + m)) k)) = (L₀.map (MulAut.conj a).toMonoidHom : Subgroup _) := by
    refine ⟨(fun u => a⁻¹ * u * a) ⁻¹' (C : Set (GL (Fin (r + m)) k)),
      (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k (r + m) n).preimage (by fun_prop), ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_map_equiv,
      MulAut.conj_symm_apply, hmemL₀]
    constructor
    · rintro ⟨hC, hU⟩
      exact ⟨haU' x hU, hC⟩
    · rintro ⟨hU, hC⟩
      refine ⟨hC, ?_⟩
      have := haU _ hU
      simpa [mul_assoc] using this
  have hS : ∀ (u : GL (Fin (r + m)) k) (hu : u ∈ U),
      u ∈ L₀ ↔ Multiplicative.toAdd (blockEquiv U hU2 ⟨u, hu⟩) ∈ box (Fin m × Fin r) (valuation k (c : k)) := by
    intro u hu
    rw [hφ, hvc, hmemL₀, ← mem_congr_iff_box n ((hU2 u).1 hu).2]
    simp [hu, C]
  have hscale : ∀ (u : GL (Fin (r + m)) k) (hu : u ∈ U),
      Multiplicative.toAdd (blockEquiv U hU2 ⟨a * u * a⁻¹, haU u hu⟩) =
        z • Multiplicative.toAdd (blockEquiv U hU2 ⟨u, hu⟩) := by
    intro u hu
    rw [hφ, hφ]
    funext p
    simp only [blockY, Pi.smul_apply, Units.smul_def, smul_eq_mul, a, aDiag_conj_apply]
    have h1 : ((rowI (r := r) p.1 : Fin (r + m)) : ℕ) < m := p.1.2
    have h2 : ¬ ((colI (m := m) p.2 : Fin (r + m)) : ℕ) < m := by simp [colI]
    rw [if_pos h1, if_neg h2, mul_one]
  obtain ⟨hLL₀, hidx⟩ := relIndex_conj (Fin m × Fin r) U (blockEquiv U hU2) a z haU hscale L₀ hL₀U
    (box (Fin m × Fin r) (valuation k (c : k))) hS (isCompact_box _ c) (isOpen_box _ c)
    (fun x hx => smul_mem_box z hz hx)
  have hvol := vol_relIndex ψ (dd r m) (hdd r m) ρ J vol (fun u hu hb f f' h => hU u hu hb f f' h) hV hLL₀ hL₀U
    hcomp₀ hopen₀ hcomp hopen hθ g v hv hg1 hg0
  rw [hidx] at hvol
  have hpos := GlobalTheory.SplitWeil.nabs_pos k z
  have hcard : Fintype.card (Fin m × Fin r) = m * r := by simp
  rw [hcard] at hvol
  rw [hvol, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hpos.ne', one_pow, one_mul]

end PositivityTheory.RgUd.CellB
end
end
