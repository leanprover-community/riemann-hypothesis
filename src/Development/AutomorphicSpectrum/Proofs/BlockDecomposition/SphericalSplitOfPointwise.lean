import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta

section Split

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem intInd_of_mem {x : F} (h : x ∈ 𝒪[F]) : intInd x = 1 := by
  simp [intInd, h]

theorem intInd_of_notMem {x : F} (h : x ∉ 𝒪[F]) : intInd x = 0 := by
  simp [intInd, h]

theorem intInd_congr {x y : F} (h : modulus x = modulus y) : intInd x = intInd y := by
  have hiff : x ∈ 𝒪[F] ↔ y ∈ 𝒪[F] := by
    rw [← modulus_le_one_iff, ← modulus_le_one_iff, h]
  by_cases hx : x ∈ 𝒪[F]
  · rw [intInd_of_mem hx, intInd_of_mem (hiff.1 hx)]
  · rw [intInd_of_notMem hx, intInd_of_notMem (fun hy => hx (hiff.2 hy))]

theorem isLocallyConstant_intInd : IsLocallyConstant (intInd : F → ℂ) := by
  have hO : IsOpen (𝒪[F] : Set F) := by
    rw [← coe_valBall_zero]; exact isOpen_valBall 0
  have hC : IsCompact (𝒪[F] : Set F) := by
    rw [← coe_valBall_zero]; exact isCompact_valBall 0
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ 𝒪[F]
  · filter_upwards [hO.mem_nhds hx] with y hy
    rw [intInd_of_mem hy, intInd_of_mem hx]
  · filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hx] with y hy
    rw [intInd_of_notMem hy, intInd_of_notMem hx]

theorem isLocallyConstant_phiS : IsLocallyConstant (phiS : F × F → ℂ) :=
  (isLocallyConstant_intInd.comp_continuous continuous_fst).mul
    (isLocallyConstant_intInd.comp_continuous continuous_snd)

theorem hasCompactSupport_phiS : HasCompactSupport (phiS : F × F → ℂ) := by
  have hC : IsCompact (𝒪[F] : Set F) := by
    rw [← coe_valBall_zero]; exact isCompact_valBall 0
  refine HasCompactSupport.intro (hC.prod hC) fun p hp => ?_
  unfold phiS
  by_cases h1 : p.1 ∈ 𝒪[F]
  · have h2 : p.2 ∉ 𝒪[F] := fun h2 => hp ⟨h1, h2⟩
    rw [intInd_of_notMem h2, mul_zero]
  · rw [intInd_of_notMem h1, zero_mul]

theorem mem_units_iff_modulus {u : Fˣ} :
    u ∈ unitFiltrationUnits F 0 ↔ modulus (u : F) = 1 := by
  rw [mem_unitFiltrationUnits_zero_iff_ord, modulus_of_ne_zero u.ne_zero]
  constructor
  · intro h; rw [h]; simp
  · intro h
    have h1 : (residueCard F : NNReal) ^ (-ord (u : F)) = (residueCard F : NNReal) ^ (0 : ℤ) := by
      rw [h, zpow_zero]
    have := zpow_right_injective₀ (zero_lt_one.trans one_lt_residueCard_nnreal)
      one_lt_residueCard_nnreal.ne' h1
    omega

theorem char_eq_one {c : Fˣ →* ℂˣ} (hc : IsUnramifiedChar c) {u : Fˣ}
    (hu : modulus (u : F) = 1) : ((c u : ℂˣ) : ℂ) = 1 := by
  have : c u = 1 := hc (mem_units_iff_modulus.2 hu)
  rw [this, Units.val_one]

def sphJ (c₁ c₂ : Fˣ →* ℂˣ) (D m : F) (u : Fˣ) : ℂ :=
  intInd (m * u)⁻¹ * intInd (D * u / m) * ((c₁ u : ℂˣ) : ℂ) * (((c₂ u)⁻¹ : ℂˣ) : ℂ)

theorem sphJ_congr (c₁ c₂ : Fˣ →* ℂˣ) {D D' m m' : F} (hD : modulus D = modulus D')
    (hm : modulus m = modulus m') : sphJ c₁ c₂ D m = sphJ c₁ c₂ D' m' := by
  funext u
  unfold sphJ
  rw [intInd_congr (x := (m * u)⁻¹) (y := (m' * u)⁻¹) (by simp only [modulus_inv, modulus_mul, hm]),
    intInd_congr (x := D * u / m) (y := D' * u / m')
      (by simp only [div_eq_mul_inv, modulus_inv, modulus_mul, hm, hD])]

theorem sphJ_eq_zero (c₁ c₂ : Fˣ →* ℂˣ) {D m : F} (hm : m ≠ 0)
    (h : ¬ modulus D ≤ modulus m ^ 2) (u : Fˣ) : sphJ c₁ c₂ D m u = 0 := by
  unfold sphJ
  by_cases h1 : (m * u)⁻¹ ∈ 𝒪[F]
  · by_cases h2 : D * u / m ∈ 𝒪[F]
    · exfalso
      apply h
      have hm0 := modulus_pos hm
      have hu0 := modulus_pos u.ne_zero
      have a1 := modulus_le_one_iff.2 h1
      have a2 := modulus_le_one_iff.2 h2
      rw [modulus_inv, modulus_mul] at a1
      rw [div_eq_mul_inv, modulus_mul, modulus_mul, modulus_inv] at a2
      have b1 : 1 ≤ modulus m * modulus (u : F) :=
        (inv_le_one₀ (mul_pos hm0 hu0)).1 a1
      have b2 : modulus D * modulus (u : F) ≤ modulus m := by
        have := mul_le_mul_of_nonneg_right a2 (le_of_lt hm0)
        rwa [mul_assoc, inv_mul_cancel₀ hm0.ne', mul_one, one_mul] at this
      calc modulus D ≤ modulus D * (modulus m * modulus (u : F)) := le_mul_of_one_le_right zero_le b1
        _ = modulus m * (modulus D * modulus (u : F)) := by ring
        _ ≤ modulus m * modulus m := mul_le_mul_right b2 _
        _ = modulus m ^ 2 := by ring
    · rw [intInd_of_notMem h2]; simp
  · rw [intInd_of_notMem h1]; simp

end Split


end GlobalTheory.CompanionTheory.SphTheta
