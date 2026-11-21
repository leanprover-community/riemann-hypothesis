import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqOfSetLIntegralEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarMapMulFiniteIdeleOfUniformizerPowers
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure

section
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellCompare

theorem isFundamentalDomain_of_map {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G)
    (H : Subgroup G) (Γ : Subgroup H) (𝓕 : Set G)
    (h : IsFundamentalDomain (Γ.map H.subtype) 𝓕 μ) : IsFundamentalDomain Γ 𝓕 μ := by
  let E := Subgroup.equivMapOfInjective Γ H.subtype H.subtype_injective
  refine h.preimage_of_equiv (f := id) (e := E.symm) (Measure.QuasiMeasurePreserving.id μ)
    E.symm.bijective (fun g x => ?_)
  show (((E.symm g : Γ) : H) : G) * x = (g : G) * x
  congr 1
  have h1 : ((E (E.symm g) : Γ.map H.subtype) : G) = (g : G) := by rw [E.apply_symm_apply]
  rw [← h1, Subgroup.coe_equivMapOfInjective_apply]
  rfl

end GlobalTheory.CellCompare

theorem GlobalTheory.CellCompare.lintegral_comparison : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant]
    (Γ Γ' : Subgroup H) [Countable Γ] [Countable Γ'] (D D' : Set H), IsFundamentalDomain Γ D ν →
    IsFundamentalDomain Γ' D' ν → ∀ (𝓕 𝓕' : Set G), IsFundamentalDomain (Γ.map H.subtype) 𝓕 μ →
    IsFundamentalDomain (Γ'.map H.subtype) 𝓕' μ → ∀ f : G → ℝ≥0∞, Measurable f → (∀ h : H, ∀ g, f (h * g) = f g) →
    ν D' * ∫⁻ g in 𝓕, f g ∂μ = ν D * ∫⁻ g in 𝓕', f g ∂μ := by
  intro G _ _ _ _ μ _ _ H ν _ _ _ Γ Γ' _ _ D D' hD hD' 𝓕 𝓕' h𝓕 h𝓕' f hf hinv
  haveI : MeasurableSMul₂ H G := ⟨(measurable_subtype_coe.comp measurable_fst).mul measurable_snd⟩
  haveI : SMulInvariantMeasure H G μ := inferInstance
  haveI : MeasurableInv H := ⟨by
    have : Measurable fun x : H => (((x : G)⁻¹ : G)) := measurable_subtype_coe.inv
    exact Measurable.subtype_mk (f := fun x : H => ((x : G))⁻¹) (h := fun x => H.inv_mem x.2) this⟩
  haveI : MeasurableMul₂ H := ⟨by
    have : Measurable fun p : H × H => ((p.1 : G) * (p.2 : G)) :=
      (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
    exact Measurable.subtype_mk (f := fun p : H × H => ((p.1 : G) * (p.2 : G)))
      (h := fun p => H.mul_mem p.1.2 p.2.2) this⟩
  exact GlobalTheory.CovolIndep.lintegral_mul_eq ν μ Γ Γ' 𝓕 𝓕' D D'
    (GlobalTheory.CellCompare.isFundamentalDomain_of_map μ H Γ 𝓕 h𝓕)
    (GlobalTheory.CellCompare.isFundamentalDomain_of_map μ H Γ' 𝓕' h𝓕') hD hD' f hf (fun s x => hinv s x)
end

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_quotient_comparison_fundamentalDomains : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant]
    (Γ Γ' : Subgroup H) [Countable Γ] [Countable Γ'] (D D' : Set H), IsFundamentalDomain Γ D ν →
    IsFundamentalDomain Γ' D' ν → ∀ (𝓕 𝓕' : Set G), IsFundamentalDomain (Γ.map H.subtype) 𝓕 μ →
    IsFundamentalDomain (Γ'.map H.subtype) 𝓕' μ → ∀ f : G → ℝ≥0∞, Measurable f → (∀ h : H, ∀ g, f (h * g) = f g) →
    ν D' * ∫⁻ g in 𝓕, f g ∂μ = ν D * ∫⁻ g in 𝓕', f g ∂μ := by
  atlas_forward_decl GlobalTheory.CellCompare.lintegral_comparison
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CellDec.Unimod

variable {R : Type} [CommRing R] {n : ℕ}

def Fil (k : ℕ) (X : Matrix (Fin n) (Fin n) R) : Prop := ∀ i j : Fin n, (j : ℕ) < i + k → X i j = 0

theorem fil_add {k : ℕ} {X Y : Matrix (Fin n) (Fin n) R} (hX : Fil k X) (hY : Fil k Y) : Fil k (X + Y) :=
  fun i j h => by rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

theorem fil_sub {k : ℕ} {X Y : Matrix (Fin n) (Fin n) R} (hX : Fil k X) (hY : Fil k Y) : Fil k (X - Y) :=
  fun i j h => by rw [Matrix.sub_apply, hX i j h, hY i j h, sub_zero]

theorem fil_nsmul {k : ℕ} {X : Matrix (Fin n) (Fin n) R} (hX : Fil k X) (m : ℕ) : Fil k (m • X) :=
  fun i j h => by rw [Matrix.smul_apply, hX i j h, smul_zero]

theorem fil_mono {a b : ℕ} {X : Matrix (Fin n) (Fin n) R} (hX : Fil b X) (hab : a ≤ b) : Fil a X :=
  fun i j h => hX i j (by omega)

theorem fil_mul {a b : ℕ} {X Y : Matrix (Fin n) (Fin n) R} (hX : Fil a X) (hY : Fil b Y) :
    Fil (a + b) (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : (l : ℕ) < i + a
  · rw [hX i l h, zero_mul]
  · rw [hY l j (by omega), mul_zero]

theorem fil_pow {k : ℕ} (hk : 1 ≤ k) {X : Matrix (Fin n) (Fin n) R} (hX : Fil k X) (m : ℕ) :
    Fil (k + 1) ((1 + X) ^ m - 1 - m • X) := by
  induction m with
  | zero => intro i j _; simp
  | succ m ih =>
    have e : (1 + X) ^ (m + 1) - 1 - (m + 1) • X =
        ((1 + X) ^ m - 1 - m • X) + ((1 + X) ^ m - 1 - m • X) * X + m • (X * X) := by
      rw [pow_succ, add_smul, one_smul, mul_add, mul_one, sub_mul, sub_mul, one_mul, smul_mul_assoc]; abel
    rw [e]
    refine fil_add (fil_add ih (fil_mono (fil_mul ih hX) (by omega))) (fil_nsmul (fil_mono (fil_mul hX hX) (by omega)) m)

end GlobalTheory.CellDec.Unimod

namespace GlobalTheory.CellDec.Unimod

variable {R : Type} [CommRing R] {n : ℕ}

def wt (c : Rˣ) (i : Fin n) : Rˣ := c⁻¹ ^ (i : ℕ)

theorem wt_mul_inv (c : Rˣ) {i j : Fin n} {k : ℕ} (h : (j : ℕ) = i + k) :
    (wt c i * (wt c j)⁻¹ : Rˣ) = c ^ k := by
  simp only [wt, h, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel, inv_mul_cancel, one_mul, inv_pow, inv_inv]

theorem fil_conj (c : Rˣ) {k : ℕ} {X : Matrix (Fin n) (Fin n) R} (hX : Fil k X) :
    Fil (k + 1) (diagonal (fun i => (wt c i : R)) * X * diagonal (fun i => (((wt c i)⁻¹ : Rˣ) : R))
      - ((c : R) ^ k) • X) := by
  intro i j h
  rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  by_cases h' : (j : ℕ) < i + k
  · rw [hX i j h']; ring
  · have hj : (j : ℕ) = i + k := by omega
    have := congrArg (fun x : Rˣ => (x : R)) (wt_mul_inv c hj)
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this
    rw [mul_right_comm, this, sub_self]

theorem hom_trivial (c : Rˣ) (hc : (c : R) = 2) (Δ : GlobalTheory.SmGL.unipB R (Fin n) →* ℝ≥0)
    (hΔ : ∀ u : GlobalTheory.SmGL.unipB R (Fin n),
      Δ ⟨GlobalTheory.SmGL.diagT R (Fin n) (wt c) * u * (GlobalTheory.SmGL.diagT R (Fin n) (wt c))⁻¹,
        GlobalTheory.CellDec.diagT_conj_mem (wt c) u.2⟩ = Δ u)
    (u : GlobalTheory.SmGL.unipB R (Fin n)) : Δ u = 1 := by
  let M : (GlobalTheory.SmGL.unipB R (Fin n)) → Matrix (Fin n) (Fin n) R := fun u => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  have hne : ∀ u : (GlobalTheory.SmGL.unipB R (Fin n)), Δ u ≠ 0 := fun u h => by
    have := map_mul Δ u u⁻¹
    rw [mul_inv_cancel, map_one, h, zero_mul] at this
    exact one_ne_zero this
  have key : ∀ d k : ℕ, n ≤ k + d → 1 ≤ k → ∀ u : (GlobalTheory.SmGL.unipB R (Fin n)), Fil k (M u - 1) → Δ u = 1 := by
    intro d
    induction d with
    | zero =>
      intro k hk _ u hu
      have : u = 1 := by
        apply Subtype.ext; apply Units.ext; ext i j
        have := hu i j (by omega)
        rw [Matrix.sub_apply, sub_eq_zero] at this
        exact this
      rw [this, map_one]
    | succ d ih =>
      intro k hk hk1 u hu
      have P := ih (k + 1) (by omega) (by omega)
      set X := M u - 1 with hXdef
      set t := GlobalTheory.SmGL.diagT R (Fin n) (wt c)
      set a : (GlobalTheory.SmGL.unipB R (Fin n)) := u ^ (2 ^ k)
      set b : (GlobalTheory.SmGL.unipB R (Fin n)) := ⟨t * u * t⁻¹, GlobalTheory.CellDec.diagT_conj_mem (wt c) u.2⟩
      have hMa : M a = (1 + X) ^ (2 ^ k) := by
        rw [hXdef, add_sub_cancel]
        simp only [M, a, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      have hMb : M b - 1 = diagonal (fun i => (wt c i : R)) * X * diagonal (fun i => (((wt c i)⁻¹ : Rˣ) : R)) := by
        have e1 : M b = diagonal (fun i => (wt c i : R)) * M u * diagonal (fun i => (((wt c i)⁻¹ : Rˣ) : R)) := by
          simp only [M, b, t, Units.val_mul, ← map_inv, GlobalTheory.SmGL.val_diagT, Pi.inv_apply]
        have e2 : diagonal (fun i : Fin n => (wt c i : R)) * diagonal (fun i : Fin n => (((wt c i)⁻¹ : Rˣ) : R)) = 1 := by
          rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
          congr 1; funext i; simp
        rw [e1, hXdef, mul_sub, sub_mul, mul_one, e2]
      have hba : Fil (k + 1) (M b - M a) := by
        have e : M b - M a = (M b - 1 - ((c : R) ^ k) • X) - (M a - 1 - (2 ^ k : ℕ) • X) := by
          have : ((c : R) ^ k) • X = (2 ^ k : ℕ) • X := by
            rw [hc, ← Nat.cast_smul_eq_nsmul R]; push_cast; rfl
          rw [this]; abel
        rw [e, hMb, hMa]
        exact fil_sub (fil_conj c hu) (fil_pow hk1 hu _)
      have hinv : Fil 0 (M a⁻¹) := fun i j h =>
        ((GlobalTheory.SmGL.mem_unipB R).1 (a⁻¹).2).1 i j (by simpa using h)
      have hab : Fil (k + 1) (M (a⁻¹ * b) - 1) := by
        have e : M (a⁻¹ * b) - 1 = M a⁻¹ * (M b - M a) := by
          have h1 : M a⁻¹ * M a = 1 := by
            simp only [M, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
          simp only [M, Subgroup.coe_mul, Units.val_mul] at h1 ⊢
          rw [mul_sub, h1]
        rw [e]; simpa using fil_mul hinv hba
      have h1 : Δ b = Δ a := by
        have : b = a * (a⁻¹ * b) := by group
        rw [this, map_mul, P _ hab, mul_one]
      have hb : Δ b = Δ u := hΔ u
      rw [hb, map_pow] at h1

      have h2 : Δ u ^ (2 ^ k - 1) = 1 := by
        have h3 : Δ u ^ (2 ^ k - 1) * Δ u = 1 * Δ u := by
          rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, one_mul, ← h1]
        exact mul_right_cancel₀ (hne u) h3
      have h4 : 2 ^ k - 1 ≠ 0 := by
        have : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
        omega
      exact (pow_eq_one_iff_of_nonneg zero_le h4).1 h2
  refine key n 1 (by omega) le_rfl u fun i j h => ?_
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 u.2
  rw [Matrix.sub_apply]
  show ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j = 0
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 h) with h' | h'
  · rw [h1 i j h', Matrix.one_apply_ne (fun e => by rw [e] at h'; exact lt_irrefl _ h'), sub_zero]
  · have : j = i := Fin.ext h'
    subst this
    rw [h2, Matrix.one_apply_eq, sub_self]

end GlobalTheory.CellDec.Unimod

namespace GlobalTheory.CellDec.Unimod

theorem modularCharacter_map_equiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (φ : G ≃ₜ* G) (g : G) : Measure.modularCharacter (φ g) = Measure.modularCharacter g := by
  have R : ∀ (ρ : Measure G) [ρ.IsHaarMeasure] (h : G),
      ρ.map (· * h) = (Measure.modularCharacterFun h) • ρ := by
    intro ρ _ h
    rw [Measure.modularCharacterFun_eq_haarScalarFactor ρ h]
    exact Measure.isMulLeftInvariant_eq_smul _ ρ
  let μ : Measure G := Measure.haar
  let ν : Measure G := μ.map φ
  haveI : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ φ
  have h1 : ν.map (· * φ g) = Measure.modularCharacterFun g • ν := by
    have e : (· * φ g) ∘ φ = φ ∘ (· * g) := funext fun x => (map_mul φ x g).symm
    simp only [ν]
    have hφ : Measurable (φ : G → G) := (map_continuous φ).measurable
    rw [Measure.map_map (measurable_mul_const _) hφ, e,
      ← Measure.map_map hφ (measurable_mul_const g), R μ g, Measure.map_smul]
  have h2 := R ν (φ g)
  rw [h1] at h2
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have h3 := congrArg (fun m : Measure G => m K) h2
  simp only [Measure.coe_nnreal_smul_apply] at h3
  have hne : ν K ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hnt : ν K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h4 := (ENNReal.mul_left_inj hne hnt).1 h3
  exact (ENNReal.coe_injective h4).symm

def conjEquiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (t : G)
    (h1 : ∀ u ∈ H, t * u * t⁻¹ ∈ H) (h2 : ∀ u ∈ H, t⁻¹ * u * t ∈ H) : H ≃ₜ* H where
  toFun u := ⟨t * u * t⁻¹, h1 u u.2⟩
  invFun u := ⟨t⁻¹ * u * t, h2 u u.2⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

end GlobalTheory.CellDec.Unimod

namespace GlobalTheory.CellDec

open GlobalTheory.CellDec.Unimod in

theorem NA_isInvInvariant : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)]
    [BorelSpace (GA E n)] (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure], ν.IsInvInvariant := by
  intro E _ _ n _ _ ν _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : LocallyCompactSpace (GA E n) := by
    haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E)) :=
      inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Ad E))
    haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
    exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GA E n) := by
    haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E))
    haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
    exact Units.isEmbedding_embedProduct.secondCountableTopology
  have hcl : IsClosed ((NA E n : Subgroup (GA E n)) : Set (GA E n)) := by
    have hc : ∀ i j : Fin n, Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E)) i j :=
      fun i j => (continuous_id.matrix_elem i j).comp Units.continuous_val
    have e : ((NA E n : Subgroup (GA E n)) : Set (GA E n)) =
        (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i), {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i j = 0}) ∩
          ⋂ i : Fin n, {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i i = 1} := by
      ext g
      simp only [SetLike.mem_coe, NA, GlobalTheory.SmGL.mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [e]
    exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (hc i j) continuous_const).inter
      (isClosed_iInter fun i => isClosed_eq (hc i i) continuous_const)
  haveI : LocallyCompactSpace (NA E n) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (NA E n) := TopologicalSpace.Subtype.secondCountableTopology _

  let c : (Ad E)ˣ := Units.map (algebraMap E (Ad E)).toMonoidHom (Units.mk0 2 two_ne_zero)
  have hc : (c : Ad E) = 2 := by
    show algebraMap E (Ad E) 2 = 2
    exact map_ofNat _ 2
  let t : GA E n := GlobalTheory.SmGL.diagT (Ad E) (Fin n) (wt c)
  have h1 : ∀ u ∈ NA E n, t * u * t⁻¹ ∈ NA E n := fun u hu => diagT_conj_mem (wt c) hu
  have h2 : ∀ u ∈ NA E n, t⁻¹ * u * t ∈ NA E n := fun u hu => by
    have := diagT_conj_mem (wt c)⁻¹ hu
    rwa [map_inv, inv_inv] at this
  have hΔ : ∀ g : NA E n, Measure.modularCharacter g = 1 :=
    hom_trivial c hc Measure.modularCharacter fun u =>
      modularCharacter_map_equiv (conjEquiv (NA E n) t h1 h2) u
  haveI : ν.IsMulRightInvariant := ⟨fun g => by
    have := Measure.isMulLeftInvariant_eq_smul (ν.map (· * g)) ν
    rw [← Measure.modularCharacterFun_eq_haarScalarFactor ν g] at this
    rw [this, show Measure.modularCharacterFun g = 1 from hΔ g, one_smul]⟩
  constructor
  let s : ENNReal := Measure.haarScalarFactor ν.inv ν
  have hs : ν.inv = s • ν := Measure.isMulLeftInvariant_eq_smul ν.inv ν
  have e1 : Measure.map Inv.inv (Measure.map Inv.inv ν) = s ^ 2 • ν := by
    rw [← Measure.inv_def ν, hs, Measure.map_smul, ← Measure.inv_def ν, hs, smul_smul, pow_two]
  have e2 : ν = s ^ 2 • ν := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at e1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using e1
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (NA E n)) := inferInstance
  have e3 : s ^ 2 * ν K = 1 ^ 2 * ν K := by
    conv_rhs => rw [e2]
    simp
  have e4 : s ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1 e3
  have e5 : s = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective e4
  rw [hs, e5, one_smul]

end GlobalTheory.CellDec
end
end

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_inverse_invariant : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure], ν.IsInvInvariant := by
  atlas_forward_decl GlobalTheory.CellDec.NA_isInvInvariant
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.UnipCoords

variable (R : Type) [CommRing R] (n : ℕ)

def strictUpper (x : {p : Fin n × Fin n // p.1 < p.2} → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if h : i < j then x ⟨(i, j), h⟩ else 0

theorem det_one_add_strictUpper (x : {p : Fin n × Fin n // p.1 < p.2} → R) :
    (1 + strictUpper R n x).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [strictUpper]
  · intro i j hij
    have h1 : ¬ i < j := not_lt.2 (le_of_lt hij)
    have h2 : i ≠ j := ne_of_gt hij
    simp [strictUpper, h1, h2, Matrix.one_apply_ne h2]

def unitOf (x : {p : Fin n × Fin n // p.1 < p.2} → R) : GL (Fin n) R where
  val := 1 + strictUpper R n x
  inv := (1 + strictUpper R n x).adjugate
  val_inv := by rw [Matrix.mul_adjugate, det_one_add_strictUpper, one_smul]
  inv_val := by rw [Matrix.adjugate_mul, det_one_add_strictUpper, one_smul]

theorem unitOf_mem (x : {p : Fin n × Fin n // p.1 < p.2} → R) :
    unitOf R n x ∈ GlobalTheory.SmGL.unipB R (Fin n) := by
  refine (GlobalTheory.SmGL.mem_unipB R).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · have h1 : ¬ i < j := not_lt.2 (le_of_lt hji)
    have h2 : i ≠ j := ne_of_gt hji
    simp [unitOf, strictUpper, h1, Matrix.one_apply_ne h2]
  · simp [unitOf, strictUpper]

end GlobalTheory.UnipCoords

open GlobalTheory.UnipCoords in
theorem GlobalTheory.UnipCoords.unipCoordsHomeomorph : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ),
    ∃ e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ₜ ({p : Fin n × Fin n // p.1 < p.2} → R),
      ∀ u : GlobalTheory.SmGL.unipB R (Fin n), e u = fun p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2 := by
  intro R _ _ _ n
  have hX : Continuous (fun x : {p : Fin n × Fin n // p.1 < p.2} → R => strictUpper R n x) := by
    refine continuous_matrix fun i j => ?_
    by_cases h : i < j
    · simp only [strictUpper, Matrix.of_apply, h, dite_true]; exact continuous_apply _
    · simp only [strictUpper, Matrix.of_apply, h, dite_false]; exact continuous_const
  let e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ ({p : Fin n × Fin n // p.1 < p.2} → R) :=
    { toFun := fun u p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2
      invFun := fun x => ⟨unitOf R n x, unitOf_mem R n x⟩
      left_inv := by
        rintro ⟨u, hu⟩
        obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hu
        apply Subtype.ext; apply Units.ext; ext i j
        change (1 + strictUpper R n _) i j = _
        rcases lt_trichotomy i j with h | h | h
        · simp [strictUpper, h, Matrix.one_apply_ne (ne_of_lt h)]
        · subst h; simp [strictUpper, h2]
        · have h' : ¬ i < j := not_lt.2 (le_of_lt h)
          simp [strictUpper, h', Matrix.one_apply_ne (ne_of_gt h), h1 i j h]
      right_inv := by
        intro x; funext p
        change (1 + strictUpper R n x) p.1.1 p.1.2 = x p
        simp [strictUpper, p.2, Matrix.one_apply_ne (ne_of_lt p.2)] }
  refine ⟨{ toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }, fun u => rfl⟩
  · refine continuous_pi fun p => ?_
    have hv : Continuous (fun u : GlobalTheory.SmGL.unipB R (Fin n) => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) :=
      (Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).comp continuous_subtype_val
    exact (continuous_apply_apply p.1.1 p.1.2).comp hv
  · refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact continuous_const.add hX
    · exact (continuous_const.add hX).matrix_adjugate
end
end

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_upperUnitriangular_entries_homeomorph : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ),
    ∃ e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ₜ ({p : Fin n × Fin n // p.1 < p.2} → R),
      ∀ u : GlobalTheory.SmGL.unipB R (Fin n), e u = fun p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2 := by
  atlas_forward_decl GlobalTheory.UnipCoords.unipCoordsHomeomorph
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.UnipCoord

abbrev Pos (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

variable {R : Type} [CommRing R] {n : ℕ}

def mat (x : Pos n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if h : i < j then x ⟨(i, j), h⟩ else if i = j then 1 else 0

theorem mat_lt (x : Pos n → R) {i j : Fin n} (h : i < j) : mat x i j = x ⟨(i, j), h⟩ := by
  simp [mat, h]

theorem mat_self (x : Pos n → R) (i : Fin n) : mat x i i = 1 := by
  simp [mat]

theorem mat_gt (x : Pos n → R) {i j : Fin n} (h : j < i) : mat x i j = 0 := by
  simp [mat, not_lt.2 h.le, h.ne']

theorem det_mat (x : Pos n → R) : (mat x).det = 1 := by
  have hu : (mat x).IsUpperTriangular := fun i j h => mat_gt x h
  rw [Matrix.det_of_isUpperTriangular hu]
  simp [mat_self]

def unit (x : Pos n → R) : GL (Fin n) R :=
  ⟨mat x, (mat x).adjugate, by rw [Matrix.mul_adjugate, det_mat, one_smul],
    by rw [Matrix.adjugate_mul, det_mat, one_smul]⟩

theorem unit_mem (x : Pos n → R) : unit x ∈ GlobalTheory.SmGL.unipB R (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB R).2 ⟨fun i j h => mat_gt x h, fun i => mat_self x i⟩

def ofCoords (x : Pos n → R) : GlobalTheory.SmGL.unipB R (Fin n) := ⟨unit x, unit_mem x⟩

def coords (u : GlobalTheory.SmGL.unipB R (Fin n)) : Pos n → R :=
  fun p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2

theorem val_ofCoords (x : Pos n → R) :
    (((ofCoords x : GlobalTheory.SmGL.unipB R (Fin n)) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = mat x := rfl

theorem coords_ofCoords (x : Pos n → R) : coords (ofCoords x) = x := by
  funext p
  simp only [coords, val_ofCoords, mat_lt x p.2]

theorem mat_coords (u : GlobalTheory.SmGL.unipB R (Fin n)) :
    mat (coords u) = ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 u.2
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [mat_lt _ h]; rfl
  · rw [mat_self, h2]
  · rw [mat_gt _ h, h1 i j h]

theorem ofCoords_coords (u : GlobalTheory.SmGL.unipB R (Fin n)) : ofCoords (coords u) = u :=
  Subtype.ext (Units.ext (mat_coords u))

def equiv : GlobalTheory.SmGL.unipB R (Fin n) ≃ (Pos n → R) where
  toFun := coords
  invFun := ofCoords
  left_inv := ofCoords_coords
  right_inv := coords_ofCoords

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord
variable {R : Type} [CommRing R] {n : ℕ} [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_mat : Continuous (mat : (Pos n → R) → Matrix (Fin n) (Fin n) R) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : i < j
  · simp only [mat, dif_pos h]; exact continuous_apply _
  · simp only [mat, dif_neg h]; exact continuous_const

theorem continuous_coords : Continuous (coords : GlobalTheory.SmGL.unipB R (Fin n) → Pos n → R) :=
  continuous_pi fun p => (continuous_apply _).comp ((continuous_apply _).comp
    ((Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).comp continuous_subtype_val))

theorem continuous_ofCoords : Continuous (ofCoords : (Pos n → R) → GlobalTheory.SmGL.unipB R (Fin n)) := by
  have h : Continuous (fun x : Pos n → R => unit x) :=
    Units.continuous_iff.2 ⟨continuous_mat, continuous_mat.matrix_adjugate⟩
  exact h.subtype_mk _

def homeo : GlobalTheory.SmGL.unipB R (Fin n) ≃ₜ (Pos n → R) where
  toEquiv := equiv
  continuous_toFun := continuous_coords
  continuous_invFun := continuous_ofCoords

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord

theorem measurePreserving_shear {R : Type} [AddGroup R] [MeasurableSpace R] [MeasurableAdd₂ R]
    {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p] (μ : Measure R) [SigmaFinite μ]
    [μ.IsAddLeftInvariant] (G : ({i // ¬ p i} → R) → ({i // p i} → R)) (hG : Measurable G) :
    MeasurePreserving (fun (y : ι → R) (i : ι) => if h : p i then G (fun j => y j) ⟨i, h⟩ + y i else y i)
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => R) p
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p
  have hsk : MeasurePreserving (fun z : ({i // ¬ p i} → R) × ({i // p i} → R) => (z.1, G z.1 + z.2))
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
    (MeasurePreserving.id _).skew_product (g := fun b a => G b + a)
      ((hG.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun b => map_add_left_eq_self _ _)
  have hψ : MeasurePreserving (fun z : ({i // p i} → R) × ({i // ¬ p i} → R) => (G z.2 + z.1, z.2))
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
    (Measure.measurePreserving_swap.comp hsk).comp Measure.measurePreserving_swap
  have hc := (he.symm e).comp (hψ.comp he)
  convert hc using 1
  funext y i
  by_cases h : p i <;> simp [e, MeasurableEquiv.piEquivPiSubtypeProd, h]

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord
variable {R : Type} [CommRing R] {n : ℕ}

def rowG (x : Pos n → R) (ρ : ℕ) :
    ({q : Pos n // ¬ (q.1.1 : ℕ) = ρ} → R) → ({q : Pos n // (q.1.1 : ℕ) = ρ} → R) :=
  fun b q => x q.1 + ∑ k : Fin n, if h : q.1.1.1 < k ∧ k < q.1.1.2 then
    x ⟨(q.1.1.1, k), h.1⟩ * b ⟨⟨(k, q.1.1.2), h.2⟩, by
      show ¬ (k : ℕ) = ρ
      have h1 := Fin.lt_def.1 h.1
      have h2 := q.2
      omega⟩ else 0

theorem mat_mul_apply_row (x y : Pos n → R) (a b : Fin n) (hab : a < b) :
    (mat x * mat y) a b = y ⟨(a, b), hab⟩ + x ⟨(a, b), hab⟩ +
      ∑ k : Fin n, if h : a < k ∧ k < b then x ⟨(a, k), h.1⟩ * y ⟨(k, b), h.2⟩ else 0 := by
  have key : ∀ k : Fin n, mat x a k * mat y k b = (if k = a then y ⟨(a, b), hab⟩ else 0) +
      (if k = b then x ⟨(a, b), hab⟩ else 0) +
      (if h : a < k ∧ k < b then x ⟨(a, k), h.1⟩ * y ⟨(k, b), h.2⟩ else 0) := by
    intro k
    rcases lt_trichotomy k a with h1 | rfl | h1
    · have : ¬ (a < k ∧ k < b) := fun h => (lt_asymm h1 h.1)
      simp [mat_gt x h1, h1.ne, (h1.trans hab).ne, this]
    · simp [mat_self, mat_lt y hab, hab.ne, lt_irrefl]
    · rcases lt_trichotomy k b with h2 | rfl | h2
      · simp [mat_lt x h1, mat_lt y h2, h1.ne', h2.ne, h1, h2]
      · simp [mat_lt x h1, mat_self, h1.ne', lt_irrefl]
      · have : ¬ (a < k ∧ k < b) := fun h => (lt_asymm h2 h.2)
        simp [mat_gt y h2, h1.ne', h2.ne', this]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem mat_mul_apply_other (x y : Pos n → R) (a b : Fin n) (hx : ∀ p : Pos n, p.1.1 = a → x p = 0) :
    (mat x * mat y) a b = mat y a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [mat_self, one_mul]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [mat_gt x h, zero_mul]
    · rw [mat_lt x h, hx _ rfl, zero_mul]
  · simp

theorem coords_mul_row (x y : Pos n → R) (ρ : ℕ) (hx : ∀ p : Pos n, ¬ (p.1.1 : ℕ) = ρ → x p = 0) :
    coords (ofCoords x * ofCoords y) = fun q =>
      if h : (q.1.1 : ℕ) = ρ then rowG x ρ (fun j => y j) ⟨q, h⟩ + y q else y q := by
  funext q
  obtain ⟨⟨a, b⟩, hab⟩ := q
  change (mat x * mat y) a b = _
  by_cases h : (a : ℕ) = ρ
  · rw [dif_pos h, mat_mul_apply_row x y a b hab]
    simp only [rowG]
    ring
  · rw [dif_neg h, mat_mul_apply_other x y a b (fun p hp => hx p (by rw [hp]; exact h)), mat_lt y hab]

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R] [BorelSpace R]
  [SecondCountableTopology R] {n : ℕ} [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)]

theorem measurable_rowG (x : Pos n → R) (ρ : ℕ) : Measurable (rowG x ρ) := by
  refine measurable_pi_lambda _ fun q => ?_
  refine Measurable.const_add (Finset.measurable_sum _ fun k _ => ?_) _
  by_cases h : q.1.1.1 < k ∧ k < q.1.1.2
  · simp only [dif_pos h]
    exact (measurable_pi_apply _).const_mul _
  · simp only [dif_neg h]
    exact measurable_const

def coordMeasure (μR : Measure R) : Measure (GlobalTheory.SmGL.unipB R (Fin n)) :=
  Measure.map ofCoords (Measure.pi fun _ : Pos n => μR)

theorem measurable_ofCoords : Measurable (ofCoords : (Pos n → R) → GlobalTheory.SmGL.unipB R (Fin n)) :=
  continuous_ofCoords.measurable

theorem measurable_coords : Measurable (coords : GlobalTheory.SmGL.unipB R (Fin n) → Pos n → R) :=
  continuous_coords.measurable

theorem map_mul_row (μR : Measure R) [SigmaFinite μR] [μR.IsAddLeftInvariant] (x : Pos n → R) (ρ : ℕ)
    (hx : ∀ p : Pos n, ¬ (p.1.1 : ℕ) = ρ → x p = 0) :
    Measure.map (ofCoords x * ·) (coordMeasure (n := n) μR) = coordMeasure μR := by
  have hsh := measurePreserving_shear (fun q : Pos n => (q.1.1 : ℕ) = ρ) μR (rowG x ρ) (measurable_rowG x ρ)
  have hc : (fun y => ofCoords x * ofCoords y) = ofCoords ∘ fun (y : Pos n → R) (q : Pos n) =>
      if h : (q.1.1 : ℕ) = ρ then rowG x ρ (fun j => y j) ⟨q, h⟩ + y q else y q := by
    funext y
    rw [Function.comp_apply, ← coords_mul_row x y ρ hx, ofCoords_coords]
  rw [coordMeasure, Measure.map_map (measurable_const_mul _) measurable_ofCoords]
  change Measure.map (fun y => ofCoords x * ofCoords y) _ = _
  rw [hc, ← Measure.map_map measurable_ofCoords hsh.measurable, hsh.map_eq]

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord
variable {R : Type} [CommRing R] {n : ℕ}

theorem ofCoords_eq_mul (x : Pos n → R) (ρ : ℕ) (hx : ∀ p : Pos n, (p.1.1 : ℕ) < ρ → x p = 0) :
    ofCoords x = ofCoords (fun p => if (p.1.1 : ℕ) = ρ then 0 else x p) *
      ofCoords (fun p => if (p.1.1 : ℕ) = ρ then x p else 0) := by
  apply Subtype.ext; apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, val_ofCoords]
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · by_cases hi : (i : ℕ) = ρ
    · rw [mat_mul_apply_other _ _ i j (fun p hp => by simp [hp, hi]), mat_lt _ hij, mat_lt _ hij]
      simp [hi]
    · rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · rw [mat_self, mul_one, mat_lt _ hij, mat_lt _ hij]; simp [hi]
      · intro k _ hk
        rcases lt_trichotomy k j with hkj | rfl | hkj
        · rw [mat_lt _ hkj]
          by_cases hk' : (k : ℕ) = ρ
          · rcases lt_trichotomy i k with hik | rfl | hik
            · rw [mat_lt _ hik]
              have : (i : ℕ) < ρ := hk' ▸ Fin.lt_def.1 hik
              rw [if_neg hi, hx ⟨(i, k), hik⟩ this, zero_mul]
            · exact absurd hk' hi
            · rw [mat_gt _ hik, zero_mul]
          · simp [hk']
        · exact absurd rfl hk
        · rw [mat_gt _ hkj, mul_zero]
      · simp
  · rw [mat_self, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [mat_self, mat_self, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [mat_gt _ h, zero_mul]
      · rw [mat_gt _ h, mul_zero]
    · simp
  · rw [mat_gt _ hij, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rcases lt_or_ge k i with h | h
    · rw [mat_gt _ h, zero_mul]
    · rw [mat_gt _ (lt_of_lt_of_le hij h), mul_zero]

variable [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R] [BorelSpace R]
  [SecondCountableTopology R] [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)]

theorem map_mul_ofCoords (μR : Measure R) [SigmaFinite μR] [μR.IsAddLeftInvariant] :
    ∀ m : ℕ, ∀ x : Pos n → R, (∀ p : Pos n, (p.1.1 : ℕ) + m < n → x p = 0) →
      Measure.map (ofCoords x * ·) (coordMeasure (n := n) μR) = coordMeasure μR := by
  intro m
  induction m with
  | zero =>
    intro x hx
    exact map_mul_row μR x 0 fun p _ => hx p (by simpa using p.1.1.2)
  | succ m ih =>
    intro x hx
    have hsplit := ofCoords_eq_mul x (n - (m + 1)) fun p hp => hx p (by omega)
    have ha := ih (fun p => if (p.1.1 : ℕ) = n - (m + 1) then 0 else x p) fun p hp => by
      by_cases h : (p.1.1 : ℕ) = n - (m + 1)
      · simp [h]
      · simp only [h, if_false]; exact hx p (by omega)
    have hw := map_mul_row μR (fun p => if (p.1.1 : ℕ) = n - (m + 1) then x p else 0) (n - (m + 1))
      fun p hp => by simp [hp]
    rw [hsplit]
    conv_lhs => rw [show (fun y => ofCoords (fun p => if (p.1.1 : ℕ) = n - (m + 1) then 0 else x p) *
        ofCoords (fun p => if (p.1.1 : ℕ) = n - (m + 1) then x p else 0) * y) =
      (ofCoords (fun p => if (p.1.1 : ℕ) = n - (m + 1) then 0 else x p) * ·) ∘
        (ofCoords (fun p => if (p.1.1 : ℕ) = n - (m + 1) then x p else 0) * ·) from
      funext fun y => mul_assoc _ _ _]
    rw [← Measure.map_map (measurable_const_mul _) (measurable_const_mul _), hw, ha]

instance (μR : Measure R) [SigmaFinite μR] [μR.IsAddLeftInvariant] :
    (coordMeasure (n := n) μR).IsMulLeftInvariant := by
  refine ⟨fun u => ?_⟩
  rw [← ofCoords_coords u]
  exact map_mul_ofCoords μR n _ fun p hp => by omega

instance [T2Space R] (μR : Measure R) [IsFiniteMeasureOnCompacts μR] [SigmaFinite μR] :
    IsFiniteMeasureOnCompacts (coordMeasure (n := n) μR) := by
  refine ⟨fun K hK => ?_⟩
  rw [coordMeasure, Measure.map_apply measurable_ofCoords hK.measurableSet]
  have : ofCoords ⁻¹' K = coords '' K := Set.ext fun y => ⟨fun hy => ⟨ofCoords y, hy, coords_ofCoords y⟩,
    fun ⟨u, hu, he⟩ => by rw [Set.mem_preimage, ← he, ofCoords_coords]; exact hu⟩
  rw [this]
  exact (hK.image continuous_coords).measure_lt_top

instance (μR : Measure R) [μR.IsOpenPosMeasure] [SigmaFinite μR] :
    (coordMeasure (n := n) μR).IsOpenPosMeasure :=
  continuous_ofCoords.isOpenPosMeasure_map fun u => ⟨coords u, ofCoords_coords u⟩

end GlobalTheory.UnipCoord

open GlobalTheory.UnipCoord in

theorem GlobalTheory.UnipCoord.map_coords_haar : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (n : ℕ)
    [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)] (μR : Measure R) [μR.IsAddHaarMeasure]
    (ν : Measure (GlobalTheory.SmGL.unipB R (Fin n))) [ν.IsHaarMeasure],
    ∃ c : ℝ≥0∞, Measure.map (fun (u : GlobalTheory.SmGL.unipB R (Fin n)) (p : {p : Fin n × Fin n // p.1 < p.2}) =>
        ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2) ν = c • Measure.pi (fun _ => μR) := by
  intro R _ _ _ _ _ _ _ _ n _ _ μR _ ν _
  haveI : LocallyCompactSpace (GlobalTheory.SmGL.unipB R (Fin n)) :=
    (homeo (R := R) (n := n)).isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (GlobalTheory.SmGL.unipB R (Fin n)) :=
    (homeo (R := R) (n := n)).isInducing.secondCountableTopology
  haveI : (coordMeasure (n := n) μR).IsHaarMeasure := Measure.IsHaarMeasure.mk
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, ν = c • coordMeasure μR :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul ν (coordMeasure μR)⟩
  refine ⟨c, ?_⟩
  change Measure.map coords ν = _
  rw [hc, Measure.map_smul, coordMeasure, Measure.map_map measurable_coords measurable_ofCoords]
  have : coords ∘ (ofCoords : (Pos n → R) → GlobalTheory.SmGL.unipB R (Fin n)) = id := funext coords_ofCoords
  rw [this, Measure.map_id]
end
end

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_map_entries_haar_unitriangular_eq_smul_pi : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (n : ℕ)
    [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)] (μR : Measure R) [μR.IsAddHaarMeasure]
    (ν : Measure (GlobalTheory.SmGL.unipB R (Fin n))) [ν.IsHaarMeasure],
    ∃ c : ℝ≥0∞, Measure.map (fun (u : GlobalTheory.SmGL.unipB R (Fin n)) (p : {p : Fin n × Fin n // p.1 < p.2}) =>
        ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2) ν = c • Measure.pi (fun _ => μR) := by
  atlas_forward_decl GlobalTheory.UnipCoord.map_coords_haar
end

section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addHaar_map_mul_finiteIdeleOfUniformizerPowers : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))), (∀ v, v ∉ s → m v = 0) →
    ∀ [MeasurableSpace (AdeleRing (𝓞 E) E)] [BorelSpace (AdeleRing (𝓞 E) E)] (μR : Measure (AdeleRing (𝓞 E) E)) [μR.IsAddHaarMeasure],
    Measure.map (fun x : AdeleRing (𝓞 E) E => ((finId E (GlobalTheory.CellDec.adl ϖ m) : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) * x) μR =
      ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) • μR := by
  first | exact @GlobalTheory.AdeleScale.map_mul_finId_adl | exact GlobalTheory.AdeleScale.map_mul_finId_adl | (intros; apply GlobalTheory.AdeleScale.map_mul_finId_adl <;> assumption)
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec.ModulusPf

variable {E : Type} [Field E] [NumberField E]

theorem adl_add (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m m' : HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    GlobalTheory.CellDec.adl ϖ (m + m') = GlobalTheory.CellDec.adl ϖ m * GlobalTheory.CellDec.adl ϖ m' := by
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro v
  change ((ϖ v ^ (m + m') v : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
    ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m' v : (v.adicCompletion E)ˣ) : v.adicCompletion E)
  rw [Finsupp.add_apply, _root_.zpow_add, Units.val_mul]

theorem adl_sub (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m m' : HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    GlobalTheory.CellDec.adl ϖ (m - m') = GlobalTheory.CellDec.adl ϖ m * (GlobalTheory.CellDec.adl ϖ m')⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← adl_add, sub_add_cancel]

theorem zpow_sum_real {ι : Type} (q : ℝ) (hq : q ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

theorem sum_pairs_eq_wtS {n : ℕ} (a : Fin n → ℤ) :
    ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (a p.1.1 - a p.1.2) = GlobalTheory.CellDec.wtS n a := by
  classical
  rw [GlobalTheory.CellDec.wtS, ← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2)
    (by simp) (fun p : Fin n × Fin n => a p.1 - a p.2), Finset.sum_filter, Fintype.sum_prod_type]

end GlobalTheory.CellDec.ModulusPf

namespace GlobalTheory.CellDec.ModulusPf

theorem modulus_conj : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    (A : Set (GlobalTheory.CellDec.NA E n)), MeasurableSet A →
    ν {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = GlobalTheory.CellDec.tl n ϖ l * (u : GA E n) * (GlobalTheory.CellDec.tl n ϖ l)⁻¹} =
      ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ν A := by
  intro E _ _ n _ _ ν _ ϖ hϖ l A hA
  classical
  set t := GlobalTheory.CellDec.tl n ϖ l with ht
  let d : Fin n → (AdeleRing (𝓞 E) E)ˣ := fun i => finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l))
  have htd : t = GlobalTheory.SmGL.diagT (Ad E) (Fin n) d := GlobalTheory.CellDec.tl_eq_diagT ϖ l
  let φ : GlobalTheory.CellDec.NA E n → GlobalTheory.CellDec.NA E n := fun u => ⟨t * u * t⁻¹, GlobalTheory.CellDec.tl_conj_mem ϖ l u.2⟩
  have hφc : Continuous φ :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hset : {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = t * (u : GA E n) * t⁻¹} = φ ⁻¹' A := by
    ext u
    constructor
    · rintro ⟨a, ha, h⟩
      have : φ u = a := Subtype.ext h.symm
      simpa [Set.mem_preimage, this] using ha
    · intro hu
      exact ⟨φ u, hu, rfl⟩
  rw [hset, ← Measure.map_apply hφc.measurable hA]

  let co : GlobalTheory.CellDec.NA E n → ({p : Fin n × Fin n // p.1 < p.2} → Ad E) :=
    fun u p => ((u : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) p.1.1 p.1.2
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_upperUnitriangular_entries_homeomorph (Ad E) n
  have hco : ⇑e = co := funext he
  let μR : Measure (Ad E) := Measure.addHaar
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_map_entries_haar_unitriangular_eq_smul_pi (Ad E) n μR ν
  let mm : {p : Fin n × Fin n // p.1 < p.2} → (HeightOneSpectrum (𝓞 E) →₀ ℤ) := fun p =>
    Finsupp.mapRange (fun x : Fin n → ℤ => x p.1.1) rfl l - Finsupp.mapRange (fun x : Fin n → ℤ => x p.1.2) rfl l
  let a : {p : Fin n × Fin n // p.1 < p.2} → Ad E := fun p => ((finId E (GlobalTheory.CellDec.adl ϖ (mm p)) : (Ad E)ˣ) : Ad E)
  let S : ({p : Fin n × Fin n // p.1 < p.2} → Ad E) → ({p : Fin n × Fin n // p.1 < p.2} → Ad E) := fun x p => a p * x p
  have hentry : ∀ (u : GA E n) (i j : Fin n), ((t * u * t⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
      ((d i : Ad E) * (((d j)⁻¹ : (Ad E)ˣ) : Ad E)) * (u : Matrix (Fin n) (Fin n) (Ad E)) i j := by
    intro u i j
    rw [htd, ← map_inv, Units.val_mul, Units.val_mul, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    simp only [Pi.inv_apply]
    ring
  have ha : ∀ p, a p = (d p.1.1 : Ad E) * (((d p.1.2)⁻¹ : (Ad E)ˣ) : Ad E) := by
    intro p
    simp only [a, mm, d, adl_sub, map_mul, map_inv, Units.val_mul]
  have hSco : co ∘ φ = S ∘ co := by
    funext u p
    simp only [Function.comp_apply, co, S, φ]
    rw [hentry, ha]
  let k : {p : Fin n × Fin n // p.1 < p.2} → ℝ≥0∞ := fun p => ENNReal.ofReal (∏ v ∈ l.support, (qV E v : ℝ) ^ (mm p v))
  have hk : ∀ p, Measure.map (fun x : Ad E => a p * x) μR = k p • μR := fun p =>
    GlobalTheory.T.addHaar_map_mul_finiteIdeleOfUniformizerPowers E ϖ hϖ (mm p) l.support (fun v hv => by simp [mm, Finsupp.notMem_support_iff.1 hv]) μR
  haveI : ∀ p, SigmaFinite (k p • μR) := fun p => (inferInstance : SigmaFinite ((Real.toNNReal _) • μR))
  have hSm : Measurable S := by
    refine measurable_pi_lambda _ fun p => ?_
    exact (measurable_const_mul (a p)).comp (measurable_pi_apply p)
  have hS : Measure.map S (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR) =
      (∏ p, k p) • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
    have h1 : Measure.pi (fun p => k p • μR) = Measure.map S (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR) := by
      refine Measure.pi_eq fun s hs => ?_
      rw [Measure.map_apply hSm (MeasurableSet.univ_pi hs)]
      rw [show S ⁻¹' Set.univ.pi s = Set.univ.pi fun p => (fun x : Ad E => a p * x) ⁻¹' s p from
        Set.preimage_pi Set.univ s fun p (x : Ad E) => a p * x]
      rw [Measure.pi_pi]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← hk p, Measure.map_apply (measurable_const_mul _) (hs p)]
    have h2 : Measure.pi (fun p => k p • μR) = (∏ p, k p) • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
      refine Measure.pi_eq fun s hs => ?_
      rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
      rfl
    rw [← h1, h2]
  have hK : (∏ p, k p) = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) := by
    simp only [k]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun p _ => Finset.prod_nonneg fun v _ => zpow_nonneg (Nat.cast_nonneg _) _)]
    congr 1
    rw [Finset.prod_comm, GlobalTheory.CellDec.dinv]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hq : (qV E v : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by rw [qV, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    rw [zpow_sum_real _ hq, ← sum_pairs_eq_wtS]
    congr 1
  have key : Measure.map φ ν = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) • ν := by
    have hem : Measurable e := e.continuous.measurable
    have h3 : Measure.map e (Measure.map φ ν) = Measure.map e (ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) • ν) := by
      have hc' : Measure.map e ν = c • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
        rw [hco]; exact hc
      rw [Measure.map_map hem hφc.measurable, hco, hSco, ← Measure.map_map hSm (hco ▸ hem), ← hco, hc',
        Measure.map_smul, Measure.map_smul, hS, hc', ← hK, smul_comm]
    have h4 := congrArg (Measure.map e.toMeasurableEquiv.symm) h3
    rwa [show (⇑e : GlobalTheory.CellDec.NA E n → _) = ⇑e.toMeasurableEquiv from rfl, MeasurableEquiv.map_symm_map,
      MeasurableEquiv.map_symm_map] at h4
  rw [key]
  rfl
end GlobalTheory.CellDec.ModulusPf

end
end

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_uniformizer_translate : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    (A : Set (GlobalTheory.CellDec.NA E n)), MeasurableSet A →
    ν {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = GlobalTheory.CellDec.tl n ϖ l * (u : GA E n) * (GlobalTheory.CellDec.tl n ϖ l)⁻¹} =
      ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ν A := by
  atlas_forward_decl GlobalTheory.CellDec.ModulusPf.modulus_conj
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

noncomputable section

namespace GlobalTheory.CellDec.RatUnip

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem row_mul_split (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (r : Fin n → E) (j : Fin n) :
    ∑ k, algebraMap E (Ad E) (r k) * w k j =
      (∑ k, if k < j then algebraMap E (Ad E) (r k) * w k j else 0) + algebraMap E (Ad E) (r j) := by
  have key : ∀ k, algebraMap E (Ad E) (r k) * w k j =
      (if k < j then algebraMap E (Ad E) (r k) * w k j else 0) +
        (if j = k then algebraMap E (Ad E) (r k) else 0) := by
    intro k
    rcases lt_trichotomy k j with h | rfl | h
    · simp [h, h.ne']
    · simp [hd]
    · simp [not_lt.2 h.le, h.ne, hl k j h]
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

theorem row_unique (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (i : Fin n) (r r' : Fin n → E)
    (h0 : ∀ k, k < i → r k = 0) (h0' : ∀ k, k < i → r' k = 0) (h1 : r i = 1) (h1' : r' i = 1)
    (hF : ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E)
    (hF' : ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r' k) * w k j ∈ GroundTheory.Global.fundamentalSet E) :
    r = r' := by
  suffices h : ∀ m : ℕ, ∀ j : Fin n, j.val < m → r j = r' j from
    funext fun j => h _ j j.val.lt_succ_self
  intro m
  induction m with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact ih j hj
    rcases lt_trichotomy j i with h | rfl | h
    · rw [h0 j h, h0' j h]
    · rw [h1, h1']
    · have hs : (∑ k, if k < j then algebraMap E (Ad E) (r k) * w k j else 0) =
          ∑ k, if k < j then algebraMap E (Ad E) (r' k) * w k j else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs with hk
        · rw [ih k (by have := Fin.lt_def.1 hk; omega)]
        · rfl
      have a := hF j h
      have b := hF' j h
      rw [row_mul_split w hl hd] at a b
      rw [hs] at a
      obtain ⟨c, -, hc⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet E
        (∑ k, if k < j then algebraMap E (Ad E) (r' k) * w k j else 0)
      have e1 := hc (-r j) (by simpa using a)
      have e2 := hc (-r' j) (by simpa using b)
      exact neg_injective (e1.trans e2.symm)

theorem row_exists (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (i : Fin n) :
    ∃ r : Fin n → E, (∀ k, k < i → r k = 0) ∧ r i = 1 ∧
      ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E := by
  suffices h : ∀ m : ℕ, ∃ r : Fin n → E, (∀ k, k < i → r k = 0) ∧ r i = 1 ∧
      ∀ j : Fin n, i < j → j.val < m →
        ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E by
    obtain ⟨r, h0, h1, h2⟩ := h n
    exact ⟨r, h0, h1, fun j hj => h2 j hj j.isLt⟩
  intro m
  induction m with
  | zero =>
    exact ⟨Pi.single i 1, fun k hk => by simp [Pi.single_apply, hk.ne], by simp,
      fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨r, h0, h1, h2⟩ := ih
    by_cases hm : ∃ jm : Fin n, jm.val = m ∧ i < jm
    · obtain ⟨jm, hjm, hijm⟩ := hm
      obtain ⟨c, hc, -⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet E
        (∑ k, algebraMap E (Ad E) (r k) * w k jm)
      refine ⟨r - Pi.single jm c, fun k hk => ?_, ?_, fun j hij hj => ?_⟩
      · simp [h0 k hk, Pi.single_apply, (hk.trans hijm).ne]
      · simp [h1, Pi.single_apply, hijm.ne]
      · have hsum : ∑ k, algebraMap E (Ad E) ((r - Pi.single jm c : Fin n → E) k) * w k j =
            ∑ k, algebraMap E (Ad E) (r k) * w k j - algebraMap E (Ad E) c * w jm j := by
          simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
          congr 1
          rw [Finset.sum_eq_single jm]
          · simp
          · intro k _ hk; simp [Pi.single_apply, hk]
          · simp
        rw [hsum]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · have hlt : j < jm := by rw [Fin.lt_def]; omega
          rw [hl jm j hlt, mul_zero, sub_zero]
          exact h2 j hij hj
        · have : j = jm := Fin.ext (hj.trans hjm.symm)
          subst this
          rw [hd, mul_one]; exact hc
    · refine ⟨r, h0, h1, fun j hij hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact h2 j hij hj
      · exact absurd ⟨j, hj, hij⟩ hm

end GlobalTheory.CellDec.RatUnip

namespace GlobalTheory.CellDec

open GlobalTheory.CellDec.RatUnip

theorem existsUnique_ratUnip_mul_mem_fundamentalSet (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GA E n)
    (hu : u ∈ GlobalTheory.CellDec.NA E n) :
    ∃! γ : GL (Fin n) E, γ ∈ GlobalTheory.SmGL.unipB E (Fin n) ∧ ∀ i j : Fin n, i < j →
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E := by
  obtain ⟨hl, hd⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  have hent : ∀ (γ : GL (Fin n) E) (i j : Fin n),
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
        ∑ k, algebraMap E (Ad E) ((γ : Matrix (Fin n) (Fin n) E) i k) * (u : Matrix (Fin n) (Fin n) (Ad E)) k j := by
    intro γ i j
    simp [ratGL, Matrix.mul_apply]
  choose r h0 h1 hF using row_exists (u : Matrix (Fin n) (Fin n) (Ad E)) hl hd
  let M : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => r i k
  have hM : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular (show M.BlockTriangular id from fun i j hij => h0 i j hij)]
    simp [M, h1]
  refine ⟨Matrix.nonsingInvUnit M hM,
    ⟨(GlobalTheory.SmGL.mem_unipB E).2 ⟨fun i j hij => h0 i j hij, fun i => h1 i⟩, fun i j hij => ?_⟩, ?_⟩
  · rw [hent]; exact hF i j hij
  · rintro γ ⟨hγ, hγF⟩
    obtain ⟨gl, gd⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hγ
    apply Units.ext
    ext i j
    have := row_unique (u : Matrix (Fin n) (Fin n) (Ad E)) hl hd i
      (fun k => (γ : Matrix (Fin n) (Fin n) E) i k) (r i) (fun k hk => gl i k hk) (h0 i) (gd i) (h1 i)
      (fun j hij => by rw [← hent]; exact hγF i j hij) (hF i)
    exact congrFun this j

end GlobalTheory.CellDec
end
end

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_ratUnitriangular_mul_entries_mem_fundamentalSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GA E n), u ∈ GlobalTheory.CellDec.NA E n →
    ∃! γ : GL (Fin n) E, γ ∈ GlobalTheory.SmGL.unipB E (Fin n) ∧ ∀ i j : Fin n, i < j →
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E := by
  atlas_forward_decl GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.CellDec

theorem isCompact_unip_entries_mem :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (C : Set (Ad E)), IsCompact C →
    IsCompact {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} := by
  intro E _ _ n C hC
  classical
  let S : Fin n → Fin n → Set (Ad E) := fun i j => if j < i then {0} else if i = j then {1} else C
  let P : Set (Matrix (Fin n) (Fin n) (Ad E)) := Set.univ.pi fun i => Set.univ.pi (S i)
  have hP : IsCompact P := by
    refine isCompact_univ_pi fun i => isCompact_univ_pi fun j => ?_
    simp only [S]
    split_ifs
    · exact isCompact_singleton
    · exact isCompact_singleton
    · exact hC
  have memP : ∀ M : Matrix (Fin n) (Fin n) (Ad E), M ∈ P ↔
      (∀ i j, j < i → M i j = 0) ∧ (∀ i, M i i = 1) ∧ ∀ i j, i < j → M i j ∈ C := by
    intro M
    change (∀ i ∈ Set.univ, ∀ j ∈ Set.univ, M i j ∈ S i j) ↔ _
    simp only [S]
    constructor
    · intro h
      refine ⟨fun i j hji => ?_, fun i => ?_, fun i j hij => ?_⟩
      · have := h i trivial j trivial; rw [if_pos hji] at this; exact this
      · have := h i trivial i trivial; rw [if_neg (lt_irrefl i), if_pos rfl] at this; exact this
      · have := h i trivial j trivial; rw [if_neg (not_lt.2 hij.le), if_neg hij.ne] at this; exact this
    · rintro ⟨h0, h1, hc⟩ i - j -
      split_ifs with hji hij
      · exact h0 i j hji
      · subst hij; exact h1 i
      · exact hc i j (lt_of_le_of_ne (not_lt.1 hji) hij)
  have hdet : ∀ M ∈ P, M.det = 1 := by
    intro M hM
    obtain ⟨h0, h1, -⟩ := (memP M).1 hM
    rw [Matrix.det_of_isUpperTriangular (fun i j hji => h0 i j hji)]
    simp [h1]
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have key : (Units.embedProduct (Matrix (Fin n) (Fin n) (Ad E))) ''
      {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} =
      (fun M => (M, MulOpposite.op M.adjugate)) '' P := by
    ext x
    constructor
    · rintro ⟨g, ⟨hN, hc⟩, rfl⟩
      obtain ⟨h0, h1⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hN
      have hgP : (g : Matrix (Fin n) (Fin n) (Ad E)) ∈ P := (memP _).2 ⟨h0, h1, hc⟩
      refine ⟨g, hgP, ?_⟩
      have hadj : (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) := by
        calc (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate
            = (((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) * g) * (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate := by
              rw [Units.inv_mul, Matrix.one_mul]
          _ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) * ((g : Matrix (Fin n) (Fin n) (Ad E)) * (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate) := by
              rw [Matrix.mul_assoc]
          _ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) := by
              rw [Matrix.mul_adjugate, hdet _ hgP, one_smul, Matrix.mul_one]
      simp only [Units.embedProduct_apply, hadj]
    · rintro ⟨M, hM, rfl⟩
      have hd := hdet M hM
      let g : GA E n := ⟨M, M.adjugate, by rw [Matrix.mul_adjugate, hd, one_smul],
        by rw [Matrix.adjugate_mul, hd, one_smul]⟩
      obtain ⟨h0, h1, hc⟩ := (memP M).1 hM
      refine ⟨g, ⟨(GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨h0, h1⟩, hc⟩, ?_⟩
      rfl
  rw [key]
  exact hP.image (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate))

end GlobalTheory.CellDec
end

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_adelicUnitriangular_entries_mem_compact : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (C : Set (Ad E)), IsCompact C →
    IsCompact {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} := by
  atlas_forward_decl GlobalTheory.CellDec.isCompact_unip_entries_mem
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CellDec

def unipFund (E : Type) [Field E] [NumberField E] (n : ℕ) : Set (NA E n) :=
  {u | ∀ i j : Fin n, i < j → ((u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E}

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem ratGL_mem_NA {γ : GL (Fin n) E} (hγ : γ ∈ GlobalTheory.SmGL.unipB E (Fin n)) : ratGL E n γ ∈ NA E n := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hγ
  refine (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [ratGL, h1 i j hij]
  · simp [ratGL, h2 i]

theorem exists_fundamentalDomain_NE (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)]
    [BorelSpace (GA E n)] (ν : Measure (NA E n)) [ν.IsHaarMeasure] : ∃ D : Set (NA E n),
    IsFundamentalDomain ((NE E n).subgroupOf (NA E n)) D ν ∧ 0 < ν D ∧ ν D < ⊤ := by
  classical
  have hfd : IsFundamentalDomain ((NE E n).subgroupOf (NA E n)) (unipFund E n) ν := by
    refine IsFundamentalDomain.mk' ?_ ?_
    · refine MeasurableSet.nullMeasurableSet ?_
      have : unipFund E n = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j),
          (fun u : NA E n => ((u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) ⁻¹'
            GroundTheory.Global.fundamentalSet E := by
        ext u; simp [unipFund]
      rw [this]
      refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
      refine (Continuous.measurable ?_) (GroundTheory.Global.measurableSet_fundamentalSet E)
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
    · intro x
      obtain ⟨γ, ⟨hγ, hγD⟩, huniq⟩ := GlobalTheory.T.existsUnique_ratUnitriangular_mul_entries_mem_fundamentalSet E n (x : GA E n) x.2
      refine ⟨⟨⟨ratGL E n γ, ratGL_mem_NA hγ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩)⟩,
        fun i j hij => hγD i j hij, ?_⟩
      intro g hg
      obtain ⟨γ', hγ', hγ'g⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
      have he : γ' = γ := huniq γ' ⟨hγ', fun i j hij => by
        have := hg i j hij
        rw [hγ'g]; exact this⟩
      apply Subtype.ext; apply Subtype.ext
      change ((g : NA E n) : GA E n) = ratGL E n γ
      rw [← hγ'g, he]
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hG : Countable ((NE E n).subgroupOf (NA E n)) := by
    have h : ∀ g : (NE E n).subgroupOf (NA E n), ∃ γ : GL (Fin n) E, ratGL E n γ = ((g : NA E n) : GA E n) :=
      fun g => by
        obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
        exact ⟨γ, hγ⟩
    choose f hf using h
    have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
    have : Countable (GL (Fin n) E) :=
      Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E))
        fun a b h => Units.ext h
    exact Function.Injective.countable (f := f) fun a b hab =>
      Subtype.ext (Subtype.ext (by rw [← hf a, ← hf b, hab]))
  have hinv : SMulInvariantMeasure ((NE E n).subgroupOf (NA E n)) (NA E n) ν :=
    ⟨fun g s _ => by
      have : (fun x : NA E n => g • x) = fun x => (g : NA E n) * x := rfl
      show ν ((fun x => g • x) ⁻¹' s) = ν s
      rw [this]; exact measure_preimage_mul ν (g : NA E n) s⟩
  refine ⟨unipFund E n, hfd, pos_iff_ne_zero.2 (hfd.measure_ne_zero (NeZero.ne ν)), ?_⟩
  set C : Set (Ad E) := closure (GroundTheory.Global.fundamentalSetInfinite E) ×ˢ
    (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (FiniteAdeleRing (𝓞 E) E)) with hCdef
  have hC : IsCompact C := (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite E).prod
    (GroundTheory.Global.isCompact_integralFiniteAdeles E)
  set K : Set (GA E n) := {g : GA E n | g ∈ NA E n ∧ ∀ i j : Fin n, i < j →
    (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} with hKdef
  have hK : IsCompact ((Subtype.val : NA E n → GA E n) ⁻¹' K) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype,
      Set.inter_eq_left.2 (fun g hg => hg.1)]
    exact GlobalTheory.T.isCompact_adelicUnitriangular_entries_mem_compact E n C hC
  refine (measure_mono fun u hu => ?_).trans_lt hK.measure_lt_top
  refine ⟨u.2, fun i j hij => ?_⟩
  have h := hu i j hij
  exact ⟨subset_closure h.1, h.2⟩

end GlobalTheory.CellDec
end
end

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_rational_upperUnitriangular : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure], ∃ D : Set (GlobalTheory.CellDec.NA E n),
    IsFundamentalDomain ((GlobalTheory.CellDec.NE E n).subgroupOf (GlobalTheory.CellDec.NA E n)) D ν ∧ 0 < ν D ∧ ν D < ⊤ := by
  atlas_forward_decl GlobalTheory.CellDec.exists_fundamentalDomain_NE
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

namespace ChangeVar

theorem locallyCompact_GA_chv : LocallyCompactSpace (GA E n) :=
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_GA_chv : SecondCountableTopology (GA E n) :=
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

theorem isClosed_NA : IsClosed ((NA E n : Subgroup (GA E n)) : Set (GA E n)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have hv : Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E)) := Units.continuous_val
  have : ((NA E n : Subgroup (GA E n)) : Set (GA E n)) =
      (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i), {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i j = 0}) ∩
      ⋂ i : Fin n, {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact GlobalTheory.SmGL.mem_unipB (Ad E)
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_)
    (isClosed_iInter fun i => ?_)
  · exact isClosed_eq (hv.matrix_elem i j) continuous_const
  · exact isClosed_eq (hv.matrix_elem i i) continuous_const

theorem NE_le_NA : NE E n ≤ NA E n := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hu
  refine (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · change algebraMap E (Ad E) ((u : Matrix (Fin n) (Fin n) E) i j) = 0
    rw [h1 i j hij, map_zero]
  · change algebraMap E (Ad E) ((u : Matrix (Fin n) (Fin n) E) i i) = 1
    rw [h2 i, map_one]

theorem countable_NE : Countable (NE E n) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  exact ((Set.countable_range (ratGL E n)).mono (by rintro _ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩)).to_subtype

theorem tl_inv_conj_mem (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {u : GA E n} (hu : u ∈ NA E n) :
    (tl n ϖ l)⁻¹ * u * tl n ϖ l ∈ NA E n := by
  have h := diagT_conj_mem (n := n) (R := Ad E)
    (fun i => finId E (adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)))⁻¹ hu
  rw [map_inv, inv_inv, ← tl_eq_diagT] at h
  exact h

end ChangeVar

open ChangeVar

theorem lintegral_tl_inv_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (μ : Measure (GA E n)) [μ.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (𝓕 : Set (GA E n)),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕 μ → ∀ F : GA E n → ℝ≥0∞, Measurable F →
    (∀ u ∈ GlobalTheory.CellDec.NA E n, ∀ g, F (u * g) = F g) →
    ∫⁻ g in 𝓕, F ((GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g) ∂μ = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ∫⁻ g in 𝓕, F g ∂μ := by
  intro E _ _ n _ _ μ _ ϖ hϖ l 𝓕 h𝓕 F hF hinv
  haveI : LocallyCompactSpace (GA E n) := locallyCompact_GA_chv
  haveI : SecondCountableTopology (GA E n) := secondCountable_GA_chv
  haveI : SigmaCompactSpace (GA E n) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite μ := inferInstance
  haveI : MeasurableMul₂ (GA E n) := inferInstance
  haveI : MeasurableInv (GA E n) := inferInstance
  haveI : LocallyCompactSpace (NA E n) := isClosed_NA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (NA E n) :=
    isClosed_NA.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : SigmaCompactSpace (NA E n) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI := countable_NE (E := E) (n := n)
  set ν : Measure (NA E n) := Measure.haar with hν
  haveI : ν.IsInvInvariant := GlobalTheory.T.haar_measure_inverse_invariant E n ν
  haveI : SFinite ν := inferInstance
  obtain ⟨D, hD, hD0, hDtop⟩ := GlobalTheory.T.exists_fundamentalDomain_rational_upperUnitriangular E n ν
  set t := tl n ϖ l with ht

  let cM : NA E n ≃* NA E n :=
    { toFun := fun u => ⟨t * u * t⁻¹, tl_conj_mem ϖ l u.2⟩
      invFun := fun u => ⟨t⁻¹ * u * t, tl_inv_conj_mem ϖ l u.2⟩
      left_inv := fun u => Subtype.ext (by simp only; group)
      right_inv := fun u => Subtype.ext (by simp only; group)
      map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcM : ∀ u : NA E n, ((cM u : NA E n) : GA E n) = t * u * t⁻¹ := fun _ => rfl
  let c : NA E n ≃ᵐ NA E n :=
    { toEquiv := cM.toEquiv
      measurable_toFun := ((measurable_mul_const _).comp ((measurable_const_mul _).comp measurable_subtype_coe)).subtype_mk
      measurable_invFun := ((measurable_mul_const _).comp ((measurable_const_mul _).comp measurable_subtype_coe)).subtype_mk }
  have hmod : ∀ A, MeasurableSet A → ν (c ⁻¹' A) = ENNReal.ofReal (dinv n l) * ν A := by
    intro A hA
    rw [← GlobalTheory.T.haar_measure_uniformizer_translate E n ν ϖ hϖ l A hA]
    congr 1
    ext u
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨a, ha, hau⟩
      convert ha
      exact Subtype.ext hau.symm
  have hmap : Measure.map c ν = ENNReal.ofReal (dinv n l) • ν := by
    ext A hA
    rw [Measure.map_apply c.measurable hA, hmod A hA, Measure.smul_apply, smul_eq_mul]
  have hmod' : ∀ A, ν (c ⁻¹' A) = ENNReal.ofReal (dinv n l) * ν A := fun A => by
    rw [← c.map_apply, hmap, Measure.smul_apply, smul_eq_mul]

  set Γ : Subgroup (NA E n) := (NE E n).subgroupOf (NA E n) with hΓ
  set Γ' : Subgroup (NA E n) := Γ.comap cM.toMonoidHom with hΓ'
  have hΓmap : Γ.map (NA E n).subtype = NE E n := by
    rw [hΓ, Subgroup.subgroupOf_map_subtype, inf_of_le_left NE_le_NA]
  have hmemΓ' : ∀ x : GA E n, x ∈ Γ'.map (NA E n).subtype ↔ t * x * t⁻¹ ∈ NE E n := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hy)
    · intro hx
      have hxN : x ∈ NA E n := by
        have := tl_inv_conj_mem ϖ l (NE_le_NA hx)
        rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at this
      exact ⟨⟨x, hxN⟩, Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  haveI : Countable Γ := Function.Injective.countable (f := fun g : Γ => (⟨(g : NA E n), g.2⟩ : NE E n))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : NE E n => (z : GA E n)) h))
  haveI : Countable Γ' := Function.Injective.countable (f := fun g : Γ' => (⟨cM g, g.2⟩ : Γ))
    fun a b h => Subtype.ext (cM.injective (congrArg (fun z : Γ => (z : NA E n)) h))

  have hD' : IsFundamentalDomain Γ' (c ⁻¹' D) ν := by
    have hsymm : ∀ u : NA E n, ((cM.symm u : NA E n) : GA E n) = t⁻¹ * u * t := fun _ => rfl
    have hc : ∀ u : NA E n, c u = cM u := fun _ => rfl
    refine hD.preimage_of_equiv (f := c) ⟨c.measurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
      (e := fun g : Γ => (⟨cM.symm g, Subgroup.mem_comap.2 (by
          rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact g.2)⟩ : Γ'))
      ⟨fun a b h => Subtype.ext (cM.symm.injective (congrArg (fun z : Γ' => (z : NA E n)) h)),
        fun g => ⟨⟨cM g, g.2⟩, Subtype.ext (by simp only [MulEquiv.symm_apply_apply])⟩⟩ ?_
    intro g x
    apply Subtype.ext
    simp only [Subgroup.smul_def, smul_eq_mul, hc, hcM, hsymm, Subgroup.coe_mul]
    group
  have h𝓕Γ : IsFundamentalDomain (Γ.map (NA E n).subtype) 𝓕 μ := by rw [hΓmap]; exact h𝓕
  have h𝓕' : IsFundamentalDomain (Γ'.map (NA E n).subtype) ((fun g => t * g) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv (f := fun g => t * g) (measurePreserving_mul_left μ t).quasiMeasurePreserving
      (e := fun g : NE E n => (⟨t⁻¹ * g * t, (hmemΓ' _).2 (by convert g.2 using 1; group)⟩ : Γ'.map (NA E n).subtype))
      ⟨fun a b h => Subtype.ext (by
          have h' := congrArg (fun z : Γ'.map (NA E n).subtype => t * (z : GA E n) * t⁻¹) h
          simpa [mul_assoc] using h'),
        fun y => ⟨⟨t * y * t⁻¹, (hmemΓ' y).1 y.2⟩, Subtype.ext (by simp only; group)⟩⟩ ?_
    intro g x
    change t * ((t⁻¹ * g * t) * x) = (g : GA E n) * (t * x)
    group
  have key := GlobalTheory.T.lintegral_quotient_comparison_fundamentalDomains μ (NA E n) ν Γ Γ' D (c ⁻¹' D) hD hD' 𝓕 ((fun g => t * g) ⁻¹' 𝓕) h𝓕Γ h𝓕' F hF
    (fun h g => hinv h h.2 g)
  rw [hmod'] at key
  have hchg : ∫⁻ g in 𝓕, F (t⁻¹ * g) ∂μ = ∫⁻ g in (fun g => t * g) ⁻¹' 𝓕, F g ∂μ := by
    rw [← (measurePreserving_mul_left μ t).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.mulLeft t).measurableEmbedding (fun b => F (t⁻¹ * b)) 𝓕]
    simp only [inv_mul_cancel_left]
  rw [hchg]
  refine ((ENNReal.mul_right_inj hD0.ne' hDtop.ne).1 ?_)
  rw [← key]
  ring

end GlobalTheory.CellDec
end
end

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_uniformizerTorus_translate_unipotentQuotient : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (μ : Measure (GA E n)) [μ.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (𝓕 : Set (GA E n)),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕 μ → ∀ F : GA E n → ℝ≥0∞, Measurable F →
    (∀ u ∈ GlobalTheory.CellDec.NA E n, ∀ g, F (u * g) = F g) →
    ∫⁻ g in 𝓕, F ((GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g) ∂μ = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ∫⁻ g in 𝓕, F g ∂μ := by
  atlas_forward_decl GlobalTheory.CellDec.lintegral_tl_inv_mul
end
