import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.CupDecompositionGlobal
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Splitting
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.CupLocal
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SymbolBridgeSum
import GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicCompositum
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in

theorem apply_eq_abs_embedding_of_isReal {v : InfinitePlace K} (hv : v.IsReal) (x : K) :
    v x = |embedding_of_isReal hv x| := by
  rw [← norm_embedding_of_isReal hv x, Real.norm_eq_abs]

theorem exists_units_neg_iff_mem (S : Set {v : InfinitePlace K // v.IsReal}) :
    ∃ a : Kˣ, ∀ v : {v : InfinitePlace K // v.IsReal},
      (embedding_of_isReal v.2 (a : K) < 0 ↔ v ∈ S) ∧ (0 < embedding_of_isReal v.2 (a : K) ↔ v ∉ S) := by
  classical

  set c : InfinitePlace K → K := fun v => if h : v.IsReal then
    (if (⟨v, h⟩ : {v : InfinitePlace K // v.IsReal}) ∈ S then -1 else 1) else 1 with hcdef
  let t : (v : InfinitePlace K) → WithAbs v.1 := fun v => WithAbs.toAbs v.1 (c v)
  let U : Set ((v : InfinitePlace K) → WithAbs v.1) := Set.pi Set.univ fun v => Metric.ball (t v) 1
  have hU : IsOpen U := isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  have htU : t ∈ U := fun v _ => Metric.mem_ball_self one_pos
  obtain ⟨x, hx⟩ := (InfinitePlace.denseRange_algebraMap_pi K).exists_mem_open hU ⟨t, htU⟩

  have hclose : ∀ v : InfinitePlace K, v (x - c v) < 1 := by
    intro v
    have h := hx v (Set.mem_univ v)
    rw [Metric.mem_ball, dist_eq_norm] at h
    exact h
  have hc : ∀ v : InfinitePlace K, v (c v) = 1 := by
    intro v
    rw [hcdef]
    show v.1 (if h : v.IsReal then (if (⟨v, h⟩ : {v : InfinitePlace K // v.IsReal}) ∈ S then -1 else 1)
      else 1) = 1
    split_ifs <;> simp only [AbsoluteValue.map_neg, AbsoluteValue.map_one]
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
    have := hclose v
    rw [zero_sub, show v (-c v) = v (c v) from v.1.map_neg _, hc] at this
    exact lt_irrefl _ this
  refine ⟨Units.mk0 x hx0, fun v => ?_⟩
  have h := hclose v.1
  rw [apply_eq_abs_embedding_of_isReal v.2, map_sub] at h
  have hcv : c v.1 = if v ∈ S then -1 else 1 := by rw [hcdef]; exact dif_pos v.2
  rw [hcv] at h
  rw [Units.val_mk0]
  by_cases hv : v ∈ S
  · rw [if_pos hv, map_neg, map_one, sub_neg_eq_add, abs_lt] at h
    exact ⟨⟨fun _ => hv, fun _ => by linarith [h.2]⟩, ⟨fun h' => by linarith [h.2], fun h' => absurd hv h'⟩⟩
  · rw [if_neg hv, map_one, abs_lt] at h
    exact ⟨⟨fun h' => by linarith [h.1], fun h' => absurd h' hv⟩, ⟨fun _ => hv, fun _ => by linarith [h.1]⟩⟩


omit [NumberField K] in

theorem extensionEmbeddingOfIsReal_algebraMap {v : InfinitePlace K} (hv : v.IsReal) (x : K) :
    Completion.extensionEmbeddingOfIsReal hv (algebraMap K v.Completion x) = embedding_of_isReal hv x :=
  Completion.extensionEmbeddingOfIsReal_coe hv (WithAbs.toAbs v.1 x)


end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField NumberField.InfinitePlace GroundTheory.Global FiniteSubfield

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Norms

variable (v : InfinitePlace K.1)

theorem range_norm_infAlgClosure_eq {F : FiniteSubfield} [Fact (K ≤ F)] (w : v.placesOver F.1)
    [(w : InfinitePlace F.1).LiesOver v]
    (e : (w : InfinitePlace F.1).Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion) :
    Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) =
      Set.range (Algebra.norm v.Completion : (w : InfinitePlace F.1).Completion → v.Completion) := by
  ext c
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.symm y, Algebra.norm_eq_of_algEquiv e.symm y⟩
  · rintro ⟨y, rfl⟩
    exact ⟨e y, Algebra.norm_eq_of_algEquiv e y⟩

theorem mem_range_norm_iff_mem_normSubgroup {F : FiniteSubfield} [Fact (K ≤ F)] (w : v.placesOver F.1)
    [(w : InfinitePlace F.1).LiesOver v] (c : v.Completionˣ) :
    (c : v.Completion) ∈ Set.range (Algebra.norm v.Completion : (w : InfinitePlace F.1).Completion → v.Completion) ↔
      c ∈ InfinitePlace.normSubgroup v (w : InfinitePlace F.1) := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hy
      exact c.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Units.val hy⟩

theorem not_isAlgClosed_of_ringHom_real {L : Type*} [Field L] (f : L →+* ℝ) : ¬ IsAlgClosed L := by
  intro hL
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (-1 : L)
  have h := congrArg f hz
  rw [map_neg, map_one, map_mul] at h
  nlinarith [mul_self_nonneg (f z)]

theorem infAlgClosure_mem_range_norm_iff_of_isReal (hv : v.IsReal) (c : v.Completionˣ) :
    (c : v.Completion) ∈ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) ↔
      0 < Completion.extensionEmbeddingOfIsReal hv (c : v.Completion) := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  have hw : (w : InfinitePlace F.1).IsComplex := by
    rw [← not_isReal_iff_isComplex]
    intro hwr
    have hc : IsAlgClosed (w : InfinitePlace F.1).Completion :=
      IsAlgClosed.of_ringEquiv (AlgebraicClosure v.Completion) _ e.toRingEquiv.symm
    exact not_isAlgClosed_of_ringHom_real (Completion.extensionEmbeddingOfIsReal hwr) hc
  rw [range_norm_infAlgClosure_eq v w e, mem_range_norm_iff_mem_normSubgroup v w,
    InfinitePlace.mem_normSubgroup_iff hv hw]

theorem infAlgClosure_mem_range_norm_of_isComplex (hv : v.IsComplex) (c : v.Completionˣ) :
    (c : v.Completion) ∈ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  have h : ¬ (v.IsReal ∧ (w : InfinitePlace F.1).IsComplex) := fun h =>
    (not_isReal_iff_isComplex.2 hv) h.1
  rw [range_norm_infAlgClosure_eq v w e, mem_range_norm_iff_mem_normSubgroup v w,
    InfinitePlace.normSubgroup_eq_top (w : InfinitePlace F.1) h]
  exact Subgroup.mem_top c

theorem exists_gal_ne_of_sq_eq_neg_one (hv : v.IsReal) {s : AlgebraicClosure v.Completion}
    (hs : s ^ 2 = -1) : ∃ σ : Gal(AlgebraicClosure v.Completion/v.Completion), σ s ≠ s := by
  by_contra h
  push Not at h
  obtain ⟨z, hz⟩ := (IsGalois.mem_range_algebraMap_iff_fixed s).2 h
  have hz2 : z ^ 2 = -1 := by
    apply (algebraMap v.Completion (AlgebraicClosure v.Completion)).injective
    rw [map_pow, hz, hs, map_neg, map_one]
  have h2 := congrArg (Completion.extensionEmbeddingOfIsReal hv) hz2
  rw [map_pow, map_neg, map_one] at h2
  nlinarith [sq_nonneg (Completion.extensionEmbeddingOfIsReal hv z)]

end Norms

section IChar

def sqrtNegOne : ℚ̄ := (IsAlgClosed.exists_eq_mul_self (-1 : ℚ̄)).choose

theorem sqrtNegOne_mul_self : sqrtNegOne * sqrtNegOne = -1 :=
  (IsAlgClosed.exists_eq_mul_self (-1 : ℚ̄)).choose_spec.symm

theorem sqrtNegOne_sq : sqrtNegOne ^ 2 = -1 := by
  rw [sq, sqrtNegOne_mul_self]

theorem sqrtNegOne_ne_neg : sqrtNegOne ≠ -sqrtNegOne := by
  intro h
  have h2 : (2 : ℚ̄) * sqrtNegOne = 0 := by rw [two_mul]; nth_rw 2 [h]; exact add_neg_cancel _
  rcases mul_eq_zero.1 h2 with h2 | h2
  · exact two_ne_zero h2
  · have := sqrtNegOne_mul_self
    rw [h2, zero_mul, eq_comm, neg_eq_zero] at this
    exact one_ne_zero this

theorem apply_sqrtNegOne_eq_or (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) : σ sqrtNegOne = sqrtNegOne ∨ σ sqrtNegOne = -sqrtNegOne := by
  have h : (σ sqrtNegOne - sqrtNegOne) * (σ sqrtNegOne + sqrtNegOne) = 0 := by
    have h1 : σ sqrtNegOne * σ sqrtNegOne = -1 := by rw [← map_mul, sqrtNegOne_mul_self, map_neg, map_one]
    linear_combination h1 - sqrtNegOne_mul_self
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

variable (K) in
open Classical in

def iCharFun (g : Additive K.1.fixingSubgroup) : QZ :=
  if ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne = sqrtNegOne then 0 else QZ.mk (1 / 2)

theorem iCharFun_of_fix {g : Additive K.1.fixingSubgroup}
    (h : ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne = sqrtNegOne) : iCharFun K g = 0 := by
  simp [iCharFun, h]

theorem iCharFun_of_not_fix {g : Additive K.1.fixingSubgroup}
    (h : ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne ≠ sqrtNegOne) :
    iCharFun K g = QZ.mk (1 / 2) := by
  simp [iCharFun, h]

theorem iCharFun_congr {g h : Additive K.1.fixingSubgroup}
    (hgh : ((Additive.toMul h : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne =
      ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne) : iCharFun K h = iCharFun K g := by
  unfold iCharFun
  rw [hgh]

theorem continuous_iCharFun : Continuous (iCharFun K) := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  let G := K.1.fixingSubgroup
  let g' : G := Additive.toMul g
  have hstab : IsOpen (MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
    stabilizer_isOpen_of_isIntegral sqrtNegOne
  have hopen : IsOpen ((fun h : G => g'⁻¹ * h) ⁻¹' ((G.subtype : G → ℚ̄ ≃ₐ[ℚ] ℚ̄) ⁻¹'
      (MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)))) :=
    (hstab.preimage continuous_subtype_val).preimage (continuous_const_mul _)
  refine ⟨(fun h : G => g'⁻¹ * h) ⁻¹' ((G.subtype : G → ℚ̄ ≃ₐ[ℚ] ℚ̄) ⁻¹'
      (MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄))), hopen, ?_, ?_⟩
  · change (g'⁻¹ * g' : G).1 • sqrtNegOne = sqrtNegOne
    rw [inv_mul_cancel]
    exact one_smul _ _
  · intro h hh
    change (g'⁻¹ * Additive.toMul h : G).1 • sqrtNegOne = sqrtNegOne at hh
    apply iCharFun_congr
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_eq_iff] at hh
    exact hh

variable (K) in

def iChar : Additive K.1.fixingSubgroup →ₜ+ QZ where
  toFun := iCharFun K
  map_zero' := iCharFun_of_fix rfl
  map_add' g h := by
    have hmul : ((Additive.toMul (g + h) : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne =
        ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄)
          (((Additive.toMul h : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne) := rfl
    rcases apply_sqrtNegOne_eq_or ((Additive.toMul h : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) with hh | hh
    · rw [hh] at hmul
      rw [iCharFun_of_fix hh, add_zero]
      exact iCharFun_congr hmul
    · rw [hh, map_neg] at hmul
      have hh' : iCharFun K h = QZ.mk (1 / 2) :=
        iCharFun_of_not_fix (by rw [hh]; exact sqrtNegOne_ne_neg.symm)
      rcases apply_sqrtNegOne_eq_or ((Additive.toMul g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) with hg | hg
      · rw [hg] at hmul
        have hgh : iCharFun K (g + h) = QZ.mk (1 / 2) :=
          iCharFun_of_not_fix (by rw [hmul]; exact sqrtNegOne_ne_neg.symm)
        rw [hgh, hh', iCharFun_of_fix hg, zero_add]
      · rw [hg, neg_neg] at hmul
        have hg' : iCharFun K g = QZ.mk (1 / 2) :=
          iCharFun_of_not_fix (by rw [hg]; exact sqrtNegOne_ne_neg.symm)
        rw [iCharFun_of_fix hmul, hg', hh', QZ.mk_half_add_mk_half]
  continuous_toFun := continuous_iCharFun

theorem iChar_apply_of_fix (τ : K.1.fixingSubgroup) (h : (τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne = sqrtNegOne) :
    iChar K (Additive.ofMul τ) = 0 :=
  iCharFun_of_fix h

theorem iChar_apply_of_not_fix (τ : K.1.fixingSubgroup) (h : (τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) sqrtNegOne ≠ sqrtNegOne) :
    iChar K (Additive.ofMul τ) = QZ.mk (1 / 2) :=
  iCharFun_of_not_fix h

end IChar

section Invariants

variable (ι : LocalEmbeddings K) (a : K.1ˣ)

theorem placeInv_brauerLocal_globalCupClass_iChar_of_mem_range_norm (v : InfinitePlace K.1)
    (ha : algebraMap K.1 v.Completion (a : K.1) ∈
      Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion)) :
    placeInv (.inl v) (brauerLocal ι (globalCupClass (iChar K) a) (.inl v)) = 0 := by
  rw [placeInv_brauerLocal_globalCupClass_inl ι v (iChar K) a 1 (iff_of_true rfl ha), map_one, ofMul_one,
    map_zero]

theorem placeInv_brauerLocal_globalCupClass_iChar_of_neg (v : InfinitePlace K.1) (hv : v.IsReal)
    (ha : embedding_of_isReal hv (a : K.1) < 0) :
    placeInv (.inl v) (brauerLocal ι (globalCupClass (iChar K) a) (.inl v)) = QZ.mk (1 / 2) := by
  have hs : (ι.inf v) sqrtNegOne ^ 2 = -1 := by rw [← map_pow, sqrtNegOne_sq, map_neg, map_one]
  obtain ⟨σ, hσ⟩ := exists_gal_ne_of_sq_eq_neg_one v hv hs
  have hnorm : algebraMap K.1 v.Completion (a : K.1) ∉
      Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) := by
    intro hmem
    have hu := (infAlgClosure_mem_range_norm_iff_of_isReal v hv
      (Units.map (algebraMap K.1 v.Completion : K.1 →* v.Completion) a)).1 hmem
    rw [Units.coe_map, MonoidHom.coe_coe, extensionEmbeddingOfIsReal_algebraMap] at hu
    exact lt_asymm ha hu
  have hσ1 : σ ≠ 1 := fun h => hσ (by rw [h]; rfl)
  rw [placeInv_brauerLocal_globalCupClass_inl ι v (iChar K) a σ (iff_of_false hσ1 hnorm)]
  apply iChar_apply_of_not_fix
  intro hfix
  apply hσ
  rw [← globalDecomp_apply, hfix]

theorem placeInv_brauerLocal_globalCupClass_iChar_of_pos (v : InfinitePlace K.1) (hv : v.IsReal)
    (ha : 0 < embedding_of_isReal hv (a : K.1)) :
    placeInv (.inl v) (brauerLocal ι (globalCupClass (iChar K) a) (.inl v)) = 0 := by
  refine placeInv_brauerLocal_globalCupClass_iChar_of_mem_range_norm ι a v ?_
  have h := (infAlgClosure_mem_range_norm_iff_of_isReal v hv
    (Units.map (algebraMap K.1 v.Completion : K.1 →* v.Completion) a)).2
    (by rw [Units.coe_map, MonoidHom.coe_coe, extensionEmbeddingOfIsReal_algebraMap]; exact ha)
  rwa [Units.coe_map, MonoidHom.coe_coe] at h

theorem placeInv_brauerLocal_globalCupClass_iChar_of_isComplex (v : InfinitePlace K.1) (hv : v.IsComplex) :
    placeInv (.inl v) (brauerLocal ι (globalCupClass (iChar K) a) (.inl v)) = 0 := by
  refine placeInv_brauerLocal_globalCupClass_iChar_of_mem_range_norm ι a v ?_
  have h := infAlgClosure_mem_range_norm_of_isComplex v hv
    (Units.map (algebraMap K.1 v.Completion : K.1 →* v.Completion) a)
  rwa [Units.coe_map, MonoidHom.coe_coe] at h

open Classical in

theorem placeInv_brauerLocal_globalCupClass_iChar (v : InfinitePlace K.1) :
    placeInv (.inl v) (brauerLocal ι (globalCupClass (iChar K) a) (.inl v)) =
      if h : v.IsReal then (if v.embedding_of_isReal h (a : K.1) < 0 then QZ.mk (1 / 2) else 0) else 0 := by
  by_cases hv : v.IsReal
  · rw [dif_pos hv]
    by_cases ha : embedding_of_isReal hv (a : K.1) < 0
    · rw [if_pos ha]
      exact placeInv_brauerLocal_globalCupClass_iChar_of_neg ι a v hv ha
    · rw [if_neg ha]
      have hpos : 0 < embedding_of_isReal hv (a : K.1) :=
        lt_of_le_of_ne (not_lt.1 ha) (fun h => a.ne_zero ((map_eq_zero _).1 h.symm))
      exact placeInv_brauerLocal_globalCupClass_iChar_of_pos ι a v hv hpos
  · rw [dif_neg hv]
    exact placeInv_brauerLocal_globalCupClass_iChar_of_isComplex ι a v (not_isReal_iff_isComplex.1 hv)

end Invariants

section Bool

theorem exists_units_neg_iff {L : Type*} [Field L] [NumberField L] (s : {v : InfinitePlace L // v.IsReal} → Bool) :
    ∃ a : Lˣ, ∀ v : {v : InfinitePlace L // v.IsReal}, (v.1.embedding_of_isReal v.2 (a : L) < 0 ↔ s v = true) := by
  obtain ⟨a, ha⟩ := exists_units_neg_iff_mem {v | s v = true}
  exact ⟨a, fun v => (ha v).1⟩

example (s : {v : InfinitePlace K.1 // v.IsReal} → Bool) :
    ∃ a : K.1ˣ, ∀ v : {v : InfinitePlace K.1 // v.IsReal}, (v.1.embedding_of_isReal v.2 (a : K.1) < 0 ↔ s v = true) :=
  exists_units_neg_iff s

end Bool

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance] FiniteSubfield.isGalois_of_normal

theorem sup_rootsOfUnityField_mono (F : IntermediateField ℚ ℚ̄) {m n : ℕ} (h : m ∣ n) :
    F ⊔ Cyclotomic.rootsOfUnityField m ≤ F ⊔ Cyclotomic.rootsOfUnityField n := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono ℚ _ _ fun x hx ↦ ?_) F
  obtain ⟨c, rfl⟩ := h
  change x ^ (m * c) = 1
  rw [pow_mul, show x ^ m = 1 from hx, one_pow]

theorem exists_le_sup_rootsOfUnityField (F E : IntermediateField ℚ ℚ̄) [FiniteDimensional ℚ E]
    (hE : E ≤ F ⊔ Cyclotomic.maxCyclotomic) :
    ∃ n : ℕ+, E ≤ F ⊔ Cyclotomic.rootsOfUnityField n := by
  set T : ℕ+ → IntermediateField ℚ ℚ̄ := fun n ↦ F ⊔ Cyclotomic.rootsOfUnityField n with hT
  have hdir : Directed (· ≤ ·) T := fun m n ↦
    ⟨m * n, sup_rootsOfUnityField_mono F (by simp), sup_rootsOfUnityField_mono F (by simp)⟩
  have hsup : F ⊔ Cyclotomic.maxCyclotomic = ⨆ n, T n := by
    rw [Cyclotomic.maxCyclotomic_eq_iSup, sup_iSup]
  set b := Module.finBasis ℚ E with hb
  have hmem : ∀ i, ∃ n, ((b i : E) : ℚ̄) ∈ T n := fun i ↦ by
    have h := hE (b i).2
    rw [hsup, ← SetLike.mem_coe, coe_iSup_of_directed hdir, Set.mem_iUnion] at h
    exact h
  choose n hn using hmem
  obtain ⟨z, hz⟩ := hdir.finset_le (Finset.univ.image n)
  refine ⟨z, fun x hx ↦ ?_⟩
  have hbT : ∀ i, ((b i : E) : ℚ̄) ∈ T z := fun i ↦
    hz (n i) (Finset.mem_image_of_mem n (Finset.mem_univ i)) (hn i)
  have hx' : (⟨x, hx⟩ : E) ∈ Submodule.span ℚ (Set.range b) := b.mem_span _
  have hmap := Submodule.mem_map_of_mem (f := E.val.toLinearMap) hx'
  rw [Submodule.map_span, ← Set.range_comp] at hmap
  exact (Submodule.span_le (p := (T z).toSubalgebra.toSubmodule)).2
    (by rintro _ ⟨i, rfl⟩; exact hbT i) hmap

variable {K : FiniteSubfield} (E : FiniteSubfield) [Fact (K ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

theorem ideleSymbol_diagonal_eq_one_of_le_sup_maxCyclotomic (hE : E.1 ≤ K.1 ⊔ Cyclotomic.maxCyclotomic)
    (a : K.1ˣ) : ideleSymbol K.1 E.1 (diagonal K.1 a) = 1 := by
  obtain ⟨n, hn⟩ := exists_le_sup_rootsOfUnityField K.1 E.1 hE
  have : FiniteDimensional ℚ (Cyclotomic.rootsOfUnityField n) :=
    IsCyclotomicExtension.finiteDimensional {(n : ℕ)} ℚ _
  set F : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField n, inferInstance⟩ with hF
  have : IsCyclotomicExtension {(n : ℕ)} ℚ F.1 :=
    (inferInstance : IsCyclotomicExtension {(n : ℕ)} ℚ (Cyclotomic.rootsOfUnityField n))
  have : IsGalois ℚ F.1 := IsCyclotomicExtension.isGalois {(n : ℕ)} ℚ F.1
  have : IsMulCommutative (F.1 ≃ₐ[ℚ] F.1) := IsCyclotomicExtension.isMulCommutative {(n : ℕ)} ℚ F.1
  set M := CyclotomicSymbol.compositum K F with hM
  have : Fact (E ≤ M) := ⟨hn⟩
  have : IsScalarTower K.1 E.1 M.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hMone : ideleSymbol K.1 M.1 (diagonal K.1 a) = 1 := by
    have h := CyclotomicSymbol.restrictHom_eq_ideleSymbol K F 1 (diagonal K.1 a) (by
      rw [ideleNorm_diagonal, RationalSymbol.ideleSymbol_diagonal_eq_one F.1 {(n : ℕ)}]
      exact map_one (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1))
    rw [← h, map_one]
  rw [← restrictNormal_ideleSymbol E.1 M.1, hMone]
  exact map_one (AlgEquiv.restrictNormalHom (F := K.1) (K₁ := M.1) E.1)

variable (ι : LocalEmbeddings K)

theorem finsum_char_localSymbolAt_eq_zero (hE : E.1 ≤ K.1 ⊔ Cyclotomic.maxCyclotomic)
    (χ : Additive K.1.fixingSubgroup →ₜ+ QZ)
    (hχ : ∀ h : K.1.fixingSubgroup, (h : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ E.1.fixingSubgroup → χ (Additive.ofMul h) = 0)
    (a : K.1ˣ) :
    ∑ᶠ v : Place K.1, χ (Additive.ofMul (localSymbolAt ι v a)) = 0 := by
  rw [finsum_char_localSymbolAt_eq ι E χ hχ a 1
    (by rw [map_one, ideleSymbol_diagonal_eq_one_of_le_sup_maxCyclotomic E hE a]), ofMul_one, map_zero]

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

theorem subsingleton_cohomology_two_of_isComplex (v : InfinitePlace K.1) (hv : v.IsComplex) :
    Subsingleton (cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  have h1 : Module.finrank v.Completion (AlgebraicClosure v.Completion) = 1 := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact (InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace F.1)).2
      fun h => (InfinitePlace.not_isReal_iff_isComplex.2 hv) h.1
  have hcard : Nat.card Gal(AlgebraicClosure v.Completion/v.Completion) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, h1]
  have : Subsingleton Gal(AlgebraicClosure v.Completion/v.Completion) :=
    (Nat.card_eq_one_iff_unique.1 hcard).1
  have : DiscreteTopology Gal(AlgebraicClosure v.Completion/v.Completion) := inferInstance
  exact ModuleCat.isZero_iff_subsingleton.1
    ((isZero_groupCohomology_succ_of_subsingleton _ 1).of_iso (cohomologyIsoGroupCohomology _ 2))

theorem placeInv_inl_eq_zero_or_eq_half (v : InfinitePlace K.1) (t : localGaloisCohomology K 2 (.inl v)) :
    placeInv (.inl v) t = 0 ∨ placeInv (.inl v) t = QZ.mk (1 / 2) := by
  by_cases ht : t = 0
  · left
    rw [ht, map_zero]
  · right
    exact quadraticInvFun_of_ne_zero _ _ ht

def gaussField : FiniteSubfield :=
  ⟨Cyclotomic.rootsOfUnityField 4, IsCyclotomicExtension.finiteDimensional {4} ℚ _⟩

theorem sqrtNegOne_mem_gaussField : sqrtNegOne ∈ gaussField.1 :=
  IntermediateField.subset_adjoin ℚ _ (show sqrtNegOne ^ 4 = 1 by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sqrtNegOne_sq]; norm_num)

variable (ι : LocalEmbeddings K)

theorem brauerSumInv_globalCupClass_iChar (a : K.1ˣ) : brauerSumInv ι (globalCupClass (iChar K) a) = 0 := by
  have : IsCyclotomicExtension {4} ℚ gaussField.1 :=
    (inferInstance : IsCyclotomicExtension {4} ℚ (Cyclotomic.rootsOfUnityField 4))
  have : IsGalois ℚ gaussField.1 := IsCyclotomicExtension.isGalois {4} ℚ gaussField.1
  have : IsMulCommutative (gaussField.1 ≃ₐ[ℚ] gaussField.1) :=
    IsCyclotomicExtension.isMulCommutative {4} ℚ gaussField.1
  rw [brauerSumInv_globalCupClass]
  refine finsum_char_localSymbolAt_eq_zero (CyclotomicSymbol.compositum K gaussField) ι
    (sup_le_sup_left (RationalSymbol.rootsOfUnityField_le_maxCyclotomic 4) K.1) (iChar K) (fun h hh => ?_) a
  apply iChar_apply_of_fix
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh _
    ((show gaussField.1 ≤ (CyclotomicSymbol.compositum K gaussField).1 from le_sup_right)
      sqrtNegOne_mem_gaussField)

theorem exists_brauerLocal_sub_globalCupClass_iChar_inl_eq_zero (x : cohomology (unitsLimitRep K) 2) :
    ∃ a : K.1ˣ, ∀ v : InfinitePlace K.1,
      brauerLocal ι (x - globalCupClass (iChar K) a) (.inl v) = 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_units_neg_iff (L := K.1)
    fun v => decide (placeInv (K := K) (.inl v.1) (brauerLocal ι x (.inl v.1)) ≠ 0)
  refine ⟨a, fun v => ?_⟩
  rw [map_sub, DFinsupp.sub_apply]
  by_cases hv : v.IsReal
  · apply placeInv_injective (.inl v)
    rw [map_sub, map_zero, sub_eq_zero, placeInv_brauerLocal_globalCupClass_iChar, dif_pos hv]
    have hs := ha ⟨v, hv⟩
    simp only [decide_eq_true_eq] at hs
    rcases placeInv_inl_eq_zero_or_eq_half v (brauerLocal ι x (.inl v)) with h | h
    · rw [if_neg (fun hneg => (hs.1 hneg) h), h]
    · rw [if_pos (hs.2 (by rw [h]; exact QZ.mk_half_ne_zero)), h]
  · have := subsingleton_cohomology_two_of_isComplex v (InfinitePlace.not_isReal_iff_isComplex.1 hv)
    exact Subsingleton.elim (α := cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) _ _

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum GroundTheory.Global.SemiLocal

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (ι : LocalEmbeddings K)

theorem exists_nsmul_eq_zero_unitsLimitRep (x : cohomology (unitsLimitRep K) 2) : ∃ m : ℕ, m ≠ 0 ∧ m • x = 0 := by
  obtain ⟨p, y, rfl⟩ := exists_unitsLevelInfl_eq 2 x
  refine ⟨Fintype.card (p.1.1 ≃ₐ[K.1] p.1.1), Fintype.card_ne_zero, ?_⟩
  rw [← map_nsmul]
  have h := card_smul_groupCohomology (galUnitsZ K.1 p.1.1) two_ne_zero
    ((cohomologyIsoGroupCohomology _ 2).hom.hom y)
  have hy : Fintype.card (p.1.1 ≃ₐ[K.1] p.1.1) • y = 0 := by
    apply (ModuleCat.mono_iff_injective (cohomologyIsoGroupCohomology (galUnitsZ K.1 p.1.1) 2).hom).1
      inferInstance
    rw [map_nsmul, h, map_zero]
  rw [hy, map_zero]

theorem brauerSumInv_eq_zero (x : cohomology (unitsLimitRep K) 2) : brauerSumInv ι x = 0 := by
  classical
  obtain ⟨a₀, ha₀⟩ := exists_brauerLocal_sub_globalCupClass_iChar_inl_eq_zero ι x
  set x' := x - globalCupClass (iChar K) a₀ with hx'
  obtain ⟨m, hm0, hm⟩ := exists_nsmul_eq_zero_unitsLimitRep x'
  let S : Finset (HeightOneSpectrum (𝓞 K.1)) :=
    (brauerLocal ι x').support.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨E, _, hgal, hcyc, hEle, hdeg⟩ := CyclotomicLayer.exists_cyclic_layer_dvd_localDegree K S hm0
  have hsplit : (unitsResField K E 2).hom x' = 0 :=
    unitsResField_eq_zero_of_dvd_finrank ι x' m hm ha₀ fun v hv w => hdeg v (by
      rw [Finset.mem_preimage, DFinsupp.mem_support_iff]
      exact hv) w
  obtain ⟨χ, b, hχ, hb⟩ := exists_globalCupClass_eq_of_unitsResField_eq_zero x' hsplit
  have : (E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal := normal_subgroupOf_of_isGalois (K := K) (E := E)
  have : IsMulCommutative (E.1 ≃ₐ[K.1] E.1) := by
    let := IsCyclic.commGroup (α := E.1 ≃ₐ[K.1] E.1)
    exact ⟨⟨fun a c => mul_comm a c⟩⟩
  have h' : brauerSumInv ι x' = 0 := by
    rw [← hb, brauerSumInv_globalCupClass]
    exact finsum_char_localSymbolAt_eq_zero E ι (hEle.trans (sup_le_sup_left Cyclotomic.zhatField_le_maxCyclotomic _))
      χ hχ b
  have hx : x = x' + globalCupClass (iChar K) a₀ := by rw [hx', sub_add_cancel]
  rw [hx, map_add, h', brauerSumInv_globalCupClass_iChar, add_zero]

end

end GroundTheory.ProfCoh
end
