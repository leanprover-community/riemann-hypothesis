import Mathlib
import GroundTheory.PAdicHodge.FieldOfNormsTower
import GroundTheory.LocalFields.DifferentGalois
import GroundTheory.LocalFields.RamificationStructure
import GroundTheory.LocalFields.ConductorTransport

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel IntermediateField

section AbsUpper

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

def absUpper (u : ℝ) : Subgroup Gal(Ω/K) where
  carrier := {σ | ∀ M : FiniteGaloisIntermediateField K Ω,
    AlgEquiv.restrictNormalHom (M : IntermediateField K Ω) σ ∈
      upperRamificationGroup K (M : IntermediateField K Ω) u}
  one_mem' M := by rw [map_one]; exact one_mem _
  mul_mem' hσ hτ M := by rw [map_mul]; exact mul_mem (hσ M) (hτ M)
  inv_mem' hσ M := by rw [map_inv]; exact inv_mem (hσ M)

variable {K Ω}

variable (K Ω) in

theorem absUpper_antitone : Antitone (absUpper K Ω) :=
  fun _ _ h _ hσ M ↦ upperRamificationGroup_antitone K _ h (hσ M)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

theorem restrictAut_restrictNormalHom {M M' : IntermediateField K Ω} [Normal K M] [Normal K M']
    (h : M ≤ M') (σ : Gal(Ω/K)) :
    restrictAut h (AlgEquiv.restrictNormalHom M' σ) = AlgEquiv.restrictNormalHom M σ := by
  ext x
  rw [restrictAut_apply, AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]

theorem restrictNormalHom_mem_of_le {M M' : FiniteGaloisIntermediateField K Ω}
    (h : (M : IntermediateField K Ω) ≤ M') {u : ℝ} {σ : Gal(Ω/K)}
    (hσ : AlgEquiv.restrictNormalHom (M' : IntermediateField K Ω) σ ∈
      upperRamificationGroup K (M' : IntermediateField K Ω) u) :
    AlgEquiv.restrictNormalHom (M : IntermediateField K Ω) σ ∈
      upperRamificationGroup K (M : IntermediateField K Ω) u := by
  rw [← map_upperRamificationGroup_restrictAut h u, ← restrictAut_restrictNormalHom h]
  exact Subgroup.mem_map_of_mem _ hσ

variable [IsGalois K Ω]

theorem map_absUpper (M : FiniteGaloisIntermediateField K Ω) (u : ℝ) :
    (absUpper K Ω u).map (AlgEquiv.restrictNormalHom (M : IntermediateField K Ω)) =
      upperRamificationGroup K (M : IntermediateField K Ω) u := by
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact hσ M
  intro τ hτ

  let t : FiniteGaloisIntermediateField K Ω → Set Gal(Ω/K) := fun M' ↦
    {σ | AlgEquiv.restrictNormalHom (M : IntermediateField K Ω) σ = τ ∧
      AlgEquiv.restrictNormalHom (M' : IntermediateField K Ω) σ ∈
        upperRamificationGroup K (M' : IntermediateField K Ω) u}
  have hmono : ∀ {M₁ M₂ : FiniteGaloisIntermediateField K Ω}, M₁ ≤ M₂ → t M₂ ⊆ t M₁ :=
    fun h σ hσ ↦ ⟨hσ.1, restrictNormalHom_mem_of_le h hσ.2⟩
  have hdir : Directed (· ⊇ ·) t := fun M₁ M₂ ↦
    ⟨M₁ ⊔ M₂, hmono le_sup_left, hmono le_sup_right⟩
  have hne : ∀ M', (t M').Nonempty := by
    intro M'
    let M'' := M ⊔ M'
    have hMM : (M : IntermediateField K Ω) ≤ M'' := (le_sup_left : M ≤ M'')
    rw [← map_upperRamificationGroup_restrictAut hMM u] at hτ
    obtain ⟨ρ, hρ, rfl⟩ := hτ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
      (K₁ := (M'' : IntermediateField K Ω)) Ω ρ
    refine ⟨σ, (restrictAut_restrictNormalHom hMM σ).symm, ?_⟩
    exact restrictNormalHom_mem_of_le (le_sup_right : M' ≤ M'') hρ
  have hcl : ∀ M', IsClosed (t M') := by
    intro M'
    have h1 : IsClosed {σ : Gal(Ω/K) | AlgEquiv.restrictNormalHom (M : IntermediateField K Ω) σ = τ} :=
      isClosed_eq (InfiniteGalois.restrictNormalHom_continuous _) continuous_const
    have h2 : IsClosed {σ : Gal(Ω/K) | AlgEquiv.restrictNormalHom (M' : IntermediateField K Ω) σ ∈
        upperRamificationGroup K (M' : IntermediateField K Ω) u} :=
      (Set.toFinite _).isClosed.preimage (InfiniteGalois.restrictNormalHom_continuous _)
    exact h1.inter h2
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
    (fun M' ↦ (hcl M').isCompact) hcl
  rw [Set.mem_iInter] at hσ
  exact ⟨σ, fun M' ↦ (hσ M').2, (hσ M).1⟩

instance absUpper_normal (u : ℝ) : (absUpper K Ω u).Normal where
  conj_mem n hn g M := by
    have : (upperRamificationGroup K (M : IntermediateField K Ω) u).Normal := by
      unfold upperRamificationGroup lowerRamificationGroupReal; infer_instance
    rw [map_mul, map_mul, map_inv]
    exact this.conj_mem _ (hn M) _

end AbsUpper

section APF

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  (L : IntermediateField K Ω)

def upperSupFixing (u : ℝ) : Subgroup Gal(Ω/K) :=
  absUpper K Ω u ⊔ L.fixingSubgroup

def IsAPF : Prop :=
  ∀ u : ℝ, IsOpen (upperSupFixing K Ω L u : Set Gal(Ω/K))

def apfIndex (u : ℝ) : ℕ :=
  (upperSupFixing K Ω L u).relIndex (absUpper K Ω 0)

def apfPsi (u : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..u, (apfIndex K Ω L w : ℝ)

def IsStrictlyAPF : Prop :=
  IsAPF K Ω L ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ u in Filter.atTop, c * apfIndex K Ω L u ≤ apfPsi K Ω L u

def upperField (u : ℝ) : IntermediateField K Ω :=
  fixedField (upperSupFixing K Ω L u)

variable {K Ω L}

theorem fixingSubgroup_le_upperSupFixing (u : ℝ) : L.fixingSubgroup ≤ upperSupFixing K Ω L u :=
  le_sup_right

theorem absUpper_le_upperSupFixing (u : ℝ) : absUpper K Ω u ≤ upperSupFixing K Ω L u :=
  le_sup_left

theorem upperSupFixing_antitone : Antitone (upperSupFixing K Ω L) :=
  fun _ _ h ↦ sup_le_sup_right (absUpper_antitone K Ω h) _

variable [IsGalois K Ω]

theorem finiteIndex_of_isOpen (H : Subgroup Gal(Ω/K)) (h : IsOpen (H : Set Gal(Ω/K))) :
    H.FiniteIndex := by
  have := Subgroup.quotient_finite_of_isOpen H h
  exact Subgroup.finiteIndex_of_finite_quotient

theorem relIndex_ne_zero_of_isOpen {H : Subgroup Gal(Ω/K)} (h : IsOpen (H : Set Gal(Ω/K)))
    (H' : Subgroup Gal(Ω/K)) : H.relIndex H' ≠ 0 := by
  have := finiteIndex_of_isOpen H h
  have : H.IsFiniteRelIndex ⊤ := Subgroup.isFiniteRelIndex_top_iff.mpr this
  exact mt (Subgroup.relIndex_eq_zero_of_le_right le_top) (Subgroup.relIndex_ne_zero (K := ⊤))

theorem upperField_le (u : ℝ) : upperField K Ω L u ≤ L := by
  conv_rhs => rw [← InfiniteGalois.fixedField_fixingSubgroup L]
  exact (IntermediateField.fixedField_antitone (fixingSubgroup_le_upperSupFixing u))

theorem upperField_mono : Monotone (upperField K Ω L) :=
  fun _ _ h ↦ IntermediateField.fixedField_antitone (upperSupFixing_antitone h)

theorem isClosed_upperSupFixing (hL : IsAPF K Ω L) (u : ℝ) :
    IsClosed (upperSupFixing K Ω L u : Set Gal(Ω/K)) :=
  Subgroup.isClosed_of_isOpen _ (hL u)

theorem fixingSubgroup_upperField (hL : IsAPF K Ω L) (u : ℝ) :
    (upperField K Ω L u).fixingSubgroup = upperSupFixing K Ω L u :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨upperSupFixing K Ω L u, isClosed_upperSupFixing hL u⟩

theorem finiteDimensional_upperField (hL : IsAPF K Ω L) (u : ℝ) :
    FiniteDimensional K (upperField K Ω L u) := by
  rw [← InfiniteGalois.isOpen_iff_finite]
  have := fixingSubgroup_upperField hL u
  exact this ▸ hL u

theorem apfIndex_mono (hL : IsAPF K Ω L) : Monotone (apfIndex K Ω L) := by
  intro u u' h
  exact Subgroup.relIndex_le_of_le_left (upperSupFixing_antitone h)
    (relIndex_ne_zero_of_isOpen (hL u') _)

theorem apfIndex_pos (hL : IsAPF K Ω L) (u : ℝ) : 0 < apfIndex K Ω L u := by
  exact Nat.pos_of_ne_zero (relIndex_ne_zero_of_isOpen (hL u) _)

theorem intervalIntegrable_apfIndex (hL : IsAPF K Ω L) (a b : ℝ) :
    IntervalIntegrable (fun w ↦ (apfIndex K Ω L w : ℝ)) MeasureTheory.volume a b :=
  (Monotone.intervalIntegrable (fun _ _ h ↦ by exact_mod_cast apfIndex_mono hL h))

end APF

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology

section LocalNrm

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem nrm_zpow (x : Ω) (k : ℤ) : nrm K (x ^ k) = nrm K x ^ k := by
  letI := algebraicNormedField K Ω
  change ‖x ^ k‖ = ‖x‖ ^ k
  exact norm_zpow x k

variable (F : IntermediateField K Ω) [FiniteDimensional K F]

theorem coe_zpow' (a : F) (k : ℤ) : ((a ^ k : F) : Ω) = (a : Ω) ^ k :=
  map_zpow₀ F.val a k

theorem valuation_le_iff_nrm_le (y z : F) :
    valuation F y ≤ valuation F z ↔ nrm K (y : Ω) ≤ nrm K (z : Ω) := by
  rw [← (valuation F).vle_iff_le, ← IntermediateField.coe_vle_coe_iff, nrm_le_nrm_iff]

theorem mem_integer_iff_nrm_le_one (y : F) : y ∈ 𝒪[F] ↔ nrm K (y : Ω) ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation F), valuation_le_iff_nrm_le]
  simp

def unif : 𝒪[F] := (IsDiscreteValuationRing.exists_irreducible 𝒪[F]).choose

theorem irreducible_unif : Irreducible (unif F) :=
  (IsDiscreteValuationRing.exists_irreducible 𝒪[F]).choose_spec

def unifNrm : ℝ := nrm K (((unif F : F) : Ω))

theorem unif_ne_zero : ((unif F : F) : Ω) ≠ 0 := by
  have := (irreducible_unif F).ne_zero
  intro h
  apply this
  exact Subtype.ext (Subtype.ext h)

theorem unifNrm_pos : 0 < unifNrm F := nrm_pos.mpr (unif_ne_zero F)

theorem unifNrm_lt_one : unifNrm F < 1 := by
  have h := valuation_lt_one_of_mem_maximalIdeal (K := F)
    ((IsLocalRing.mem_maximalIdeal _).mpr (irreducible_unif F).not_isUnit)
  rw [unifNrm, ← nrm_one (K := K) (Ω := Ω)]
  have h' : ¬ valuation F (1 : F) ≤ valuation F ((unif F : F)) := by rw [map_one]; exact not_le.mpr h
  rw [valuation_le_iff_nrm_le] at h'
  simpa using not_le.mp h'

theorem nrm_eq_unifNrm_zpow {y : F} (hy : y ≠ 0) : nrm K (y : Ω) = unifNrm F ^ ord y := by
  have hϖ : ((unif F : F)) ≠ 0 := fun h ↦ unif_ne_zero F (by rw [h]; rfl)
  have hpow : ((unif F : F)) ^ ord y ≠ 0 := zpow_ne_zero _ hϖ
  have hord : ord (((unif F : F)) ^ ord y) = ord y := by
    rw [ord_zpow hϖ, ord_uniformizer (irreducible_unif F), mul_one]
  have hv : valuation F y = valuation F (((unif F : F)) ^ ord y) := by
    rw [← normalizedValuation_eq_iff, normalizedValuation_eq_exp_ord hy,
      normalizedValuation_eq_exp_ord hpow, hord]
  have h1 := (valuation_le_iff_nrm_le F _ _).mp hv.le
  have h2 := (valuation_le_iff_nrm_le F _ _).mp hv.ge
  have e : ((((unif F : F)) ^ ord y : F) : Ω) = ((unif F : F) : Ω) ^ ord y :=
    coe_zpow' F _ _
  rw [e, nrm_zpow] at h1 h2
  exact le_antisymm h1 h2

theorem normalizedValuation_le_exp_iff (y : F) (m : ℤ) :
    normalizedValuation F y ≤ WithZero.exp (-m) ↔ nrm K (y : Ω) ≤ unifNrm F ^ m := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [map_zero, zero_le, true_iff]
    simp only [IntermediateField.coe_zero, nrm_zero]
    exact (zpow_pos (unifNrm_pos F) m).le
  rw [normalizedValuation_eq_exp_ord hy, WithZero.exp_le_exp, neg_le_neg_iff,
    nrm_eq_unifNrm_zpow F hy]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ (unifNrm_pos F) (unifNrm_lt_one F)).symm

variable (K) in

def baseUnif : 𝒪[K] := (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose

variable (K Ω) in

def baseUnifNrm : ℝ := nrm K (algebraMap K Ω (baseUnif K : K))

theorem unifNrm_pow_ramificationIndex :
    unifNrm F ^ ramificationIndex K F = baseUnifNrm K Ω := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose_spec
  have hK0 : (baseUnif K : K) ≠ 0 := by
    intro h; exact hirr.ne_zero (Subtype.ext h)
  have hF0 : algebraMap K F (baseUnif K : K) ≠ 0 := (_root_.map_ne_zero _).mpr hK0
  have h := nrm_eq_unifNrm_zpow F hF0
  have hord : ord (baseUnif K : K) = 1 := ord_uniformizer hirr
  rw [ord_algebraMap, hord, mul_one, zpow_natCast] at h
  rw [baseUnifNrm, ← h]
  rfl

theorem baseUnifNrm_pos : 0 < baseUnifNrm K Ω := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose_spec
  refine nrm_pos.mpr ((_root_.map_ne_zero _).mpr ?_)
  intro h; exact hirr.ne_zero (Subtype.ext h)

section Relative

variable {F} (σ : Gal(Ω/K)) (r : ℝ)

def Moves (a : Ω) : Prop := nrm K (σ a - a) ≤ r * nrm K a

variable {σ r}

theorem Moves.mul (_hr : 0 ≤ r) {a b : Ω} (ha : Moves σ r a) (hb : Moves σ r b) :
    Moves σ r (a * b) := by
  unfold Moves at *
  have e : σ (a * b) - a * b = σ a * (σ b - b) + (σ a - a) * b := by rw [map_mul]; ring
  rw [e, nrm_mul a b]
  refine nrm_add_le_of_le ?_ ?_
  · rw [nrm_mul, nrm_algEquiv]
    calc nrm K a * nrm K (σ b - b) ≤ nrm K a * (r * nrm K b) :=
          mul_le_mul_of_nonneg_left hb (nrm_nonneg _)
      _ = r * (nrm K a * nrm K b) := by ring
  · rw [nrm_mul]
    calc nrm K (σ a - a) * nrm K b ≤ r * nrm K a * nrm K b :=
          mul_le_mul_of_nonneg_right ha (nrm_nonneg _)
      _ = r * (nrm K a * nrm K b) := by ring

theorem Moves.inv {a : Ω} (ha : Moves σ r a) : Moves σ r a⁻¹ := by
  unfold Moves at *
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  have hσa : σ a ≠ 0 := (_root_.map_ne_zero σ).mpr ha0
  have e : σ a⁻¹ - a⁻¹ = -(σ a - a) / (σ a * a) := by
    rw [map_inv₀]; field_simp; ring
  rw [e, nrm_div, nrm_neg, nrm_mul, nrm_algEquiv, nrm_inv]
  have hn : 0 < nrm K a := nrm_pos.mpr ha0
  rw [div_le_iff₀ (mul_pos hn hn)]
  calc nrm K (σ a - a) ≤ r * nrm K a := ha
    _ = r * (nrm K a)⁻¹ * (nrm K a * nrm K a) := by field_simp

theorem Moves.pow (hr : 0 ≤ r) {a : Ω} (ha : Moves σ r a) (n : ℕ) : Moves σ r (a ^ n) := by
  induction n with
  | zero => simpa [Moves] using hr
  | succ n ih => rw [pow_succ]; exact ih.mul hr ha

theorem Moves.zpow (hr : 0 ≤ r) {a : Ω} (ha : Moves σ r a) (n : ℤ) : Moves σ r (a ^ n) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact ha.pow hr m
  · rw [zpow_neg, zpow_natCast]; exact (ha.pow hr m).inv

variable (F) in

theorem nrm_sub_le_of_forall_integer (i : ℕ)
    (h : ∀ y : F, nrm K (y : Ω) ≤ 1 → nrm K (σ y - y) ≤ unifNrm F ^ (i + 1)) (x : F) :
    nrm K (σ x - x) ≤ unifNrm F ^ i * nrm K (x : Ω) := by
  set ρF := unifNrm F
  have hρ0 : 0 ≤ ρF ^ i := pow_nonneg (unifNrm_pos F).le _
  rcases eq_or_ne x 0 with rfl | hx
  · simp

  have hϖ : Moves σ (ρF ^ i) ((unif F : F) : Ω) := by
    have h1 := h (unif F : F) (by
      rw [← mem_integer_iff_nrm_le_one]; exact (unif F).2)
    unfold Moves
    calc nrm K (σ ((unif F : F) : Ω) - ((unif F : F) : Ω)) ≤ ρF ^ (i + 1) := h1
      _ = ρF ^ i * ρF := pow_succ _ _

  set u : F := x / ((unif F : F)) ^ ord x
  have hϖ0 : ((unif F : F)) ≠ 0 := fun h' ↦ unif_ne_zero F (by rw [h']; rfl)
  have hu1 : nrm K (u : Ω) = 1 := by
    have e : (u : Ω) = (x : Ω) / ((unif F : F) : Ω) ^ ord x := by
      simp only [u, IntermediateField.coe_div]
      rw [coe_zpow']
    rw [e, nrm_div, nrm_zpow, nrm_eq_unifNrm_zpow F hx]
    exact div_self (zpow_pos (unifNrm_pos F) _).ne'
  have hu : Moves σ (ρF ^ i) (u : Ω) := by
    unfold Moves
    rw [hu1, mul_one]
    refine (h u hu1.le).trans ?_
    exact pow_le_pow_of_le_one (unifNrm_pos F).le (unifNrm_lt_one F).le (Nat.le_succ i)
  have hx' : (x : Ω) = ((unif F : F) : Ω) ^ ord x * (u : Ω) := by
    have : x = ((unif F : F)) ^ ord x * u := by
      simp only [u]; field_simp
    conv_lhs => rw [this]
    rw [IntermediateField.coe_mul, coe_zpow']
  have := (hϖ.zpow hρ0 (ord x)).mul hρ0 hu
  rw [← hx'] at this
  exact this

end Relative

theorem nrm_sub_le_of_mem_lowerRamificationGroup (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] {σ : Gal(Ω/K)} {i : ℕ}
    (hσ : AlgEquiv.restrictNormalHom M σ ∈ lowerRamificationGroup K M i) (x : M) :
    nrm K (σ x - x) ≤ unifNrm M ^ i * nrm K (x : Ω) := by
  refine nrm_sub_le_of_forall_integer M i (fun y hy ↦ ?_) x
  rw [mem_lowerRamificationGroup_iff_valuation] at hσ
  have h := hσ y ((mem_integer_iff_nrm_le_one M y).mpr hy)
  have h' := (normalizedValuation_le_exp_iff M _ ((i : ℤ) + 1)).mp (by exact_mod_cast h)
  have e : ((AlgEquiv.restrictNormalHom M σ y - y : M) : Ω) = σ y - y := by
    rw [AddSubgroupClass.coe_sub, AlgEquiv.restrictNormalHom_apply]
  rw [e] at h'
  exact_mod_cast h'

end LocalNrm

section Psi

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

variable (K L) in

def upperIndex (w : ℝ) : ℕ :=
  (upperRamificationGroup K L w).relIndex (lowerRamificationGroup K L 0)

theorem upperIndex_mono : Monotone (upperIndex K L) := fun _ b h ↦
  Subgroup.relIndex_le_of_le_left (upperRamificationGroup_antitone K L h) (by
    have := relIndex_pos_of_finite (upperRamificationGroup K L b) (lowerRamificationGroup K L 0)
    exact_mod_cast this.ne')

theorem intervalIntegrable_upperIndex (a b : ℝ) :
    IntervalIntegrable (fun w ↦ (upperIndex K L w : ℝ)) MeasureTheory.volume a b :=
  Monotone.intervalIntegrable fun _ _ h ↦ by exact_mod_cast upperIndex_mono h

theorem upperRamificationGroup_eq_of_mem_Ioc (n : ℕ) {w : ℝ}
    (hw : w ∈ Set.Ioc (herbrandPhi K L n) (herbrandPhi K L (n + 1))) :
    upperRamificationGroup K L w = lowerRamificationGroup K L ((n : ℤ) + 1) := by
  rw [upperRamificationGroup, lowerRamificationGroupReal]
  congr 1
  have h1 : (n : ℝ) < herbrandPsi K L w := by
    rw [← herbrandPsi_herbrandPhi (K := K) (L := L) n]
    exact herbrandPsi_strictMono hw.1
  have h2 : herbrandPsi K L w ≤ (n : ℝ) + 1 := by
    rw [← herbrandPsi_herbrandPhi (K := K) (L := L) ((n : ℝ) + 1)]
    exact herbrandPsi_strictMono.monotone hw.2
  rw [Int.ceil_eq_iff]
  push_cast
  constructor <;> linarith

theorem integral_upperIndex_Ioc (n : ℕ) :
    ∫ w in herbrandPhi K L n..herbrandPhi K L (n + 1), (upperIndex K L w : ℝ) =
      (herbrandPhi K L (n + 1) - herbrandPhi K L n) *
        ((lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex (lowerRamificationGroup K L 0) : ℝ) := by
  have hle : herbrandPhi K L n ≤ herbrandPhi K L (n + 1) :=
    herbrandPhi_strictMono.monotone (by linarith)
  rw [intervalIntegral.integral_congr_ae (g := fun _ ↦
    ((lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex (lowerRamificationGroup K L 0) : ℝ))]
  · simp
  · refine Filter.Eventually.of_forall fun w hw ↦ ?_
    rw [Set.uIoc_of_le hle] at hw
    simp only [upperIndex, upperRamificationGroup_eq_of_mem_Ioc n hw]

theorem integral_upperIndex_herbrandPhi (n : ℕ) :
    ∫ w in (0 : ℝ)..herbrandPhi K L n, (upperIndex K L w : ℝ) = n := by
  induction n with
  | zero => simp [herbrandPhi_zero]
  | succ n ih =>
    rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_upperIndex _ _)
      (intervalIntegrable_upperIndex _ _), ih]
    push_cast
    rw [integral_upperIndex_Ioc]
    have hv : herbrandPhi K L ((n : ℝ) + 1) ∈
        Set.Icc (herbrandPhi K L n) (herbrandPhi K L ((n : ℝ) + 1)) :=
      ⟨herbrandPhi_strictMono.monotone (by linarith), le_rfl⟩
    have h := herbrandPsi_of_mem_Icc (K := K) (L := L) n hv
    rw [herbrandPsi_herbrandPhi] at h
    linarith

theorem herbrandPsi_eq_integral {v : ℝ} (hv : 0 ≤ v) :
    herbrandPsi K L v = ∫ w in (0 : ℝ)..v, (upperIndex K L w : ℝ) := by
  have hψ0 : 0 ≤ herbrandPsi K L v := by
    rw [← herbrandPsi_zero (K := K) (L := L)]; exact herbrandPsi_strictMono.monotone hv
  set n := ⌊herbrandPsi K L v⌋₊
  have hn1 : (n : ℝ) ≤ herbrandPsi K L v := Nat.floor_le hψ0
  have hn2 : herbrandPsi K L v < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hφn : herbrandPhi K L n ≤ v := by
    rw [← herbrandPhi_herbrandPsi (K := K) (L := L) v]
    exact herbrandPhi_strictMono.monotone hn1
  have hφn1 : v ≤ herbrandPhi K L ((n : ℝ) + 1) := by
    rw [← herbrandPhi_herbrandPsi (K := K) (L := L) v]
    exact herbrandPhi_strictMono.monotone hn2.le
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := herbrandPhi K L n)
    (intervalIntegrable_upperIndex _ _) (intervalIntegrable_upperIndex _ _),
    integral_upperIndex_herbrandPhi, herbrandPsi_of_mem_Icc n ⟨hφn, hφn1⟩]
  congr 1
  rw [intervalIntegral.integral_congr_ae (g := fun _ ↦
    ((lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex (lowerRamificationGroup K L 0) : ℝ))]
  · simp
  · refine Filter.Eventually.of_forall fun w hw ↦ ?_
    rw [Set.uIoc_of_le hφn] at hw
    simp only [upperIndex, upperRamificationGroup_eq_of_mem_Ioc n ⟨hw.1, hw.2.trans hφn1⟩]

end Psi

end GroundTheory.PAdicHodge
end
end
