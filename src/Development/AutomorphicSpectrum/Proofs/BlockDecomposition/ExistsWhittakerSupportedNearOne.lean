import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestVectorNonvanishingLocal
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

namespace GlobalTheory.CompanionTheory.CharTriv

theorem eq_one_of_sq_iter_near (z : ℂ) (h : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  have step : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hw := h k
      set w := z ^ (2 ^ k) with hwdef
      have e : z ^ (2 ^ (k + 1)) - 1 = (w - 1) * (w + 1) := by
        rw [hwdef, pow_succ 2 k, pow_mul]; ring
      have h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
        have e2 : (2 : ℂ) = (w + 1) - (w - 1) := by ring
        have h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
          rw [e2]; exact norm_sub_le _ _
        have h4 : ‖(2 : ℂ)‖ = 2 := by simp
        linarith
      rw [e, norm_mul, pow_succ]
      have hn : 0 ≤ ‖w - 1‖ := norm_nonneg _
      have hz : 0 ≤ ‖z - 1‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h2 hn]
  by_contra hne
  have pos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 : 1 < (3 / 2 : ℝ) ^ k * ‖z - 1‖ := by
    rwa [div_lt_iff₀ pos] at hk
  have := step k
  have := h k
  linarith

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem pow_sub_one_mem_valBall {n : ℤ} (hn : 0 ≤ n) {a : F} (ha : a - 1 ∈ valBall F n) (k : ℕ) :
    a ^ k - 1 ∈ valBall F n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1) - 1 = (a ^ k - 1) * (a - 1) + (a ^ k - 1) + (a - 1) := by ring
    rw [e]
    exact add_mem (add_mem (valBall_antitone (by omega) (mul_mem_valBall ih ha)) ih) ha

end GlobalTheory.CompanionTheory.CharTriv

theorem GlobalTheory.CompanionTheory.CharTriv.exists_trivial_on_principal : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ν : Fˣ →* ℂˣ), IsUnit1 ν → ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧ 1 ≤ n ∧ ∀ a : Fˣ, (a : F) - 1 ∈ valBall F (n : ℤ) → ν a = 1 := by
  intro F _ _ _ _ _ _ ν hν n₀
  have hc : Continuous ν := hν.1
  have hV : IsOpen {z : ℂˣ | ‖(z : ℂ) - 1‖ < 1 / 2} :=
    isOpen_lt ((Units.continuous_val.sub continuous_const).norm) continuous_const
  have hU : ν ⁻¹' {z : ℂˣ | ‖(z : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Fˣ) :=
    hc.continuousAt.preimage_mem_nhds (hV.mem_nhds (by simp))
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  have hshift : Filter.Tendsto (fun x : F => x + 1) (𝓝 0) (𝓝 ((1 : Fˣ) : F)) := by
    have := (continuous_add_right (1 : F)).tendsto (0 : F)
    simpa using this
  obtain ⟨m, -, hm⟩ := hasBasis_nhds_zero_valBall.mem_iff.1 (hshift ht)
  refine ⟨max n₀ (max 1 m.toNat), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _), ?_⟩
  intro a ha
  have hle : m ≤ ((max n₀ (max 1 m.toNat) : ℕ) : ℤ) := by omega
  have key : ∀ k : ℕ, ‖((ν a : ℂˣ) : ℂ) ^ (2 ^ k) - 1‖ < 1 / 2 := by
    intro k
    have h1 := GlobalTheory.CompanionTheory.CharTriv.pow_sub_one_mem_valBall (Int.natCast_nonneg _) ha (2 ^ k)
    have h2 : ((a ^ (2 ^ k) : Fˣ) : F) ∈ t := by
      have := hm (valBall_antitone hle h1)
      simpa using this
    have h3 := htU (show a ^ (2 ^ k) ∈ (Units.val : Fˣ → F) ⁻¹' t from h2)
    simpa using h3
  exact Units.ext (by simpa using GlobalTheory.CompanionTheory.CharTriv.eq_one_of_sq_iter_near _ key)
end

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

namespace GlobalTheory.CompanionTheory.SmallSec

theorem modulus_eq_one_of_sub_one_mem_valBall_pos (F : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (hn : 1 ≤ n) (a : Fˣ)
    (ha : (a : F) - 1 ∈ valBall F (n : ℤ)) : modulus (a : F) = 1 := by
  have hd : (a : F) - 1 ∈ valBall F (ord (1 : F) + 1) := by
    rw [ord_one, zero_add]
    exact valBall_antitone (by exact_mod_cast hn) ha
  have h := ord_add_eq (one_ne_zero : (1 : F) ≠ 0) hd
  rw [add_sub_cancel, ord_one] at h
  exact GroundTheory.LocalField.modulus_eq_one_iff.2 h

end GlobalTheory.CompanionTheory.SmallSec
end

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.TorSB

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem psi_isLocallyConstant {ψ : AddChar F Circle} (hψ : IsStd ψ) :
    IsLocallyConstant fun r : F => ((ψ r : Circle) : ℂ) := by
  have h := isTrivialOn_addCharConductor hψ.1 hψ.2.1
  rw [hψ.2.2] at h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' (valBall F 0 : Set F),
    (isOpen_valBall 0).preimage (continuous_id.sub continuous_const), ?_, fun y hy => ?_⟩
  · show x - x ∈ valBall F 0
    rw [sub_self]
    exact (valBall F 0).zero_mem
  · have h1 : ψ (y - x) = 1 := h _ hy
    have h2 : y = x + (y - x) := by ring
    show ((ψ y : Circle) : ℂ) = ((ψ x : Circle) : ℂ)
    rw [h2, AddChar.map_add_eq_mul, h1, mul_one]

theorem indicator_isLocallyConstant {X : Type} [TopologicalSpace X] {S : Set X} (hS : IsClopen S)
    {f : X → ℂ} (hf : IsLocallyConstant f) : IsLocallyConstant (S.indicator f) := by
  have h := (LocallyConstant.indicator (⟨f, hf⟩ : LocallyConstant X ℂ) hS).isLocallyConstant
  have e : S.indicator f = ((LocallyConstant.indicator (⟨f, hf⟩ : LocallyConstant X ℂ) hS) : X → ℂ) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, LocallyConstant.indicator_of_mem _ hS hx]
      rfl
    · rw [Set.indicator_of_notMem hx, LocallyConstant.indicator_of_notMem _ hS hx]
  rw [e]
  exact h

theorem torF_mem (n : ℕ) : torF F n ∈ schwartzBruhat F := by
  have hcont : Continuous fun x : F => x - 1 := continuous_id.sub continuous_const
  have hcl : IsClopen ({x : F | x - 1 ∈ valBall F (n : ℤ)} : Set F) :=
    ⟨(isClosed_valBall (n : ℤ)).preimage hcont, (isOpen_valBall (n : ℤ)).preimage hcont⟩
  have hK : IsCompact ({x : F | x - 1 ∈ valBall F (n : ℤ)} : Set F) := by
    have : ({x : F | x - 1 ∈ valBall F (n : ℤ)} : Set F) =
        (fun y : F => y + 1) '' (valBall F (n : ℤ) : Set F) := by
      ext x
      constructor
      · intro hx
        exact ⟨x - 1, hx, by ring⟩
      · rintro ⟨y, hy, rfl⟩
        show y + 1 - 1 ∈ valBall F (n : ℤ)
        simpa using hy
    rw [this]
    exact (isCompact_valBall (n : ℤ)).image (continuous_id.add continuous_const)
  refine ⟨indicator_isLocallyConstant hcl (IsLocallyConstant.const (1 : ℂ)), ?_⟩
  exact HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _

theorem torG_mem {ψ : AddChar F Circle} (hψ : IsStd ψ) (n : ℕ) : torG ψ n ∈ schwartzBruhat F := by
  have hcl : IsClopen (valBall F (-(n : ℤ)) : Set F) :=
    ⟨isClosed_valBall _, isOpen_valBall _⟩
  refine ⟨indicator_isLocallyConstant hcl (psi_isLocallyConstant hψ), ?_⟩
  exact HasCompactSupport.intro (isCompact_valBall (-(n : ℤ)))
    fun x hx => Set.indicator_of_notMem hx _

theorem pt_mem {f g : F → ℂ} (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F) :
    Ad3.SchwartzSpaceL2.pt f g ∈ GodementSectionLocal.schwartzBruhat2 F := by
  refine GodementSectionLocal.mem_schwartzBruhat2.2
    ⟨(hf.1.comp_continuous (continuous_apply 0)).mul (hg.1.comp_continuous (continuous_apply 1)), ?_⟩
  refine HasCompactSupport.intro
    ((hf.2.isCompact.prod hg.2.isCompact).image (Homeomorph.finTwoArrow (X := F)).symm.continuous)
    fun x hx => ?_
  by_contra hne
  refine hx ⟨(x 0, x 1), ⟨subset_tsupport _ fun h => hne ?_, subset_tsupport _ fun h => hne ?_⟩, ?_⟩
  · simp [Ad3.SchwartzSpaceL2.pt, h]
  · simp [Ad3.SchwartzSpaceL2.pt, h]
  · ext j
    fin_cases j <;> simp

theorem tor_schwartzBruhat : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ n : ℕ, 1 ≤ n →
  torF F n ∈ schwartzBruhat F ∧ torG ψ n ∈ schwartzBruhat F ∧ Ad3.SchwartzSpaceL2.pt (torF F n) (torG ψ n) ∈ GodementSectionLocal.schwartzBruhat2 F := by
  intro F _ _ _ _ _ _ ψ hψ n _
  exact ⟨torF_mem n, torG_mem hψ n, pt_mem (torF_mem n) (torG_mem hψ n)⟩

end GlobalTheory.CompanionTheory.TorSB
end
end

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.KirTorus

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem val_eq_one {x : F} {n : ℕ} (hn : 1 ≤ n) (hx : x - 1 ∈ valBall F (n : ℤ)) :
    normalizedValuation F x = 1 := by
  have h1 : normalizedValuation F (x - 1) < 1 := by
    refine lt_of_le_of_lt (mem_valBall.mp hx) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    have : (1 : ℤ) ≤ n := by exact_mod_cast hn
    omega
  have := Valuation.map_one_add_of_lt (normalizedValuation F) h1
  simpa using this

theorem inv_sub_one_mem {x : F} {n : ℕ} (hn : 1 ≤ n) (hx0 : x ≠ 0)
    (hx : x - 1 ∈ valBall F (n : ℤ)) : x⁻¹ - 1 ∈ valBall F (n : ℤ) := by
  have hv := val_eq_one hn hx
  have e : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by field_simp; ring
  rw [e, mem_valBall, map_mul, Valuation.map_neg, map_inv₀, hv, inv_one, mul_one]
  exact mem_valBall.mp hx

theorem mul_sub_one_mem {x y : F} {n : ℕ} (hn : 1 ≤ n) (hx : x - 1 ∈ valBall F (n : ℤ))
    (hy : y - 1 ∈ valBall F (n : ℤ)) : x * y - 1 ∈ valBall F (n : ℤ) := by
  have hv := val_eq_one hn hy
  have e : x * y - 1 = (x - 1) * y + (y - 1) := by ring
  rw [e]
  refine add_mem ?_ hy
  rw [mem_valBall, map_mul, hv, mul_one]
  exact mem_valBall.mp hx

variable [MeasurableSpace F] [BorelSpace F]

theorem localFourier_torG {ψ : AddChar F Circle} (hψ : IsStd ψ) (n : ℕ) (y : F) :
    localFourier (selfDualMeasure ψ) ψ (torG ψ n) y =
      (((selfDualMeasure ψ).real (valBall F (-(n : ℤ)) : Set F) : ℝ) : ℂ) *
        (valBall F (n : ℤ) : Set F).indicator (fun _ => (1 : ℂ)) (1 + y) := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have key := localFourier_indicator_valBall (selfDualMeasure ψ) hc h1 (-(n : ℤ)) (1 + y)
  rw [h0, zero_sub, neg_neg] at key
  rw [← key]
  unfold localFourier
  congr 1
  funext x
  by_cases hx : x ∈ (valBall F (-(n : ℤ)) : Set F)
  · rw [torG, Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_add, mul_one,
      AddChar.map_add_eq_mul, Circle.coe_mul, one_mul]
  · rw [torG, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, zero_mul]

theorem one_sub_inv_mem_iff {n : ℕ} (hn : 1 ≤ n) (h : Fˣ) :
    (1 + -((h⁻¹ : Fˣ) : F)) ∈ valBall F (n : ℤ) ↔ (h : F) - 1 ∈ valBall F (n : ℤ) := by
  constructor
  · intro hh
    have h2 : ((h⁻¹ : Fˣ) : F) - 1 ∈ valBall F (n : ℤ) := by
      have := neg_mem hh
      rwa [show -(1 + -((h⁻¹ : Fˣ) : F)) = ((h⁻¹ : Fˣ) : F) - 1 by ring] at this
    have := inv_sub_one_mem hn (h⁻¹).ne_zero h2
    simpa using this
  · intro hh
    have h2 := inv_sub_one_mem hn h.ne_zero hh
    have := neg_mem h2
    rw [show -((h : F)⁻¹ - 1) = 1 + -((h⁻¹ : Fˣ) : F) by simp; ring] at this
    exact this

theorem torus_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (n : ℕ), 1 ≤ n → (∀ a : Fˣ, (a : F) - 1 ∈ valBall F (n : ℤ) → ν a = 1) →
  ∀ a : Fˣ,
    ((a : F) - 1 ∈ valBall F (n : ℤ) → ∫ h : Fˣ, (((ν h)⁻¹ * ν⁻¹ h : ℂˣ) : ℂ) * torF F n ((h : F) * a) *
        localFourier (selfDualMeasure ψ) ψ (torG ψ n) (-((h⁻¹ : Fˣ) : F)) ∂multHaar F =
      (((selfDualMeasure ψ).real (valBall F (-(n : ℤ)) : Set F) : ℝ) : ℂ) * (((multHaar F).real {h : Fˣ | (h : F) - 1 ∈ valBall F (n : ℤ)} : ℝ) : ℂ)) ∧
    ((a : F) - 1 ∉ valBall F (n : ℤ) → ∫ h : Fˣ, (((ν h)⁻¹ * ν⁻¹ h : ℂˣ) : ℂ) * torF F n ((h : F) * a) *
        localFourier (selfDualMeasure ψ) ψ (torG ψ n) (-((h⁻¹ : Fˣ) : F)) ∂multHaar F = 0) := by
  intro F _ _ _ _ _ _ ψ hψ ν n hn hν a
  set V : ℂ := (((selfDualMeasure ψ).real (valBall F (-(n : ℤ)) : Set F) : ℝ) : ℂ) with hV
  set H : Set Fˣ := {h : Fˣ | (h : F) - 1 ∈ valBall F (n : ℤ)} with hH
  have hfour : ∀ h : Fˣ, localFourier (selfDualMeasure ψ) ψ (torG ψ n) (-((h⁻¹ : Fˣ) : F)) =
      H.indicator (fun _ => V) h := by
    intro h
    rw [localFourier_torG hψ]
    by_cases hh : h ∈ H
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem
        (show (1 + -((h⁻¹ : Fˣ) : F)) ∈ (valBall F (n : ℤ) : Set F) from
          (one_sub_inv_mem_iff hn h).mpr hh), mul_one]
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem
        (show (1 + -((h⁻¹ : Fˣ) : F)) ∉ (valBall F (n : ℤ) : Set F) from
          fun h' => hh ((one_sub_inv_mem_iff hn h).mp h')), mul_zero]
  have hmeas : MeasurableSet H :=
    ((isOpen_valBall (n : ℤ)).preimage
      ((Units.continuous_val).sub continuous_const)).measurableSet
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · have e : ∀ h : Fˣ, (((ν h)⁻¹ * ν⁻¹ h : ℂˣ) : ℂ) * torF F n ((h : F) * a) *
        localFourier (selfDualMeasure ψ) ψ (torG ψ n) (-((h⁻¹ : Fˣ) : F)) =
        H.indicator (fun _ => V) h := by
      intro h
      rw [hfour]
      by_cases hh : h ∈ H
      · have hνh : ν h = 1 := hν h hh
        have hm : (h : F) * a ∈ {x : F | x - 1 ∈ valBall F (n : ℤ)} := mul_sub_one_mem hn hh ha
        rw [Set.indicator_of_mem hh, torF, Set.indicator_of_mem hm, MonoidHom.inv_apply, hνh]
        simp
      · rw [Set.indicator_of_notMem hh, mul_zero]
    simp_rw [e]
    rw [integral_indicator_const _ hmeas, Complex.real_smul, mul_comm]
  · have e : ∀ h : Fˣ, (((ν h)⁻¹ * ν⁻¹ h : ℂˣ) : ℂ) * torF F n ((h : F) * a) *
        localFourier (selfDualMeasure ψ) ψ (torG ψ n) (-((h⁻¹ : Fˣ) : F)) = 0 := by
      intro h
      rw [hfour]
      by_cases hh : h ∈ H
      · have hm : (h : F) * a ∉ {x : F | x - 1 ∈ valBall F (n : ℤ)} := by
          intro hm
          apply ha
          have h2 := inv_sub_one_mem hn h.ne_zero hh
          have := mul_sub_one_mem hn h2 hm
          rwa [inv_mul_cancel_left₀ h.ne_zero] at this
        rw [torF, Set.indicator_of_notMem hm, mul_zero, zero_mul]
      · rw [Set.indicator_of_notMem hh, mul_zero]
    simp_rw [e]
    simp

end GlobalTheory.CompanionTheory.KirTorus
end
end

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

namespace GlobalTheory.CompanionTheory.VolNe

theorem volumes_ne_zero : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
  (∀ k : ℤ, (selfDualMeasure ψ).real (valBall F k : Set F) ≠ 0) ∧
  (∀ n : ℕ, 1 ≤ n → (multHaar F).real {h : Fˣ | (h : F) - 1 ∈ valBall F (n : ℤ)} ≠ 0) ∧
  (∀ m : ℕ, (LFS.hG ψ).real (GLnLocal.congruenceSubgroup F 2 m : Set (GL (Fin 2) F)) ≠ 0) := by
  intro F _ _ _ _ _ _ ψ
  refine ⟨fun k => ?_, fun n hn => ?_, fun m => ?_⟩
  · have ho : IsOpen (valBall F k : Set F) := isOpen_valBall k
    have hc : IsCompact (valBall F k : Set F) := isCompact_valBall k
    have hne : (valBall F k : Set F).Nonempty := ⟨0, zero_mem _⟩
    exact (ENNReal.toReal_pos (ho.measure_pos _ hne).ne' hc.measure_lt_top.ne).ne'
  · set H : Set Fˣ := {h : Fˣ | (h : F) - 1 ∈ valBall F (n : ℤ)} with hH
    have ho : IsOpen H :=
      (isOpen_valBall (n : ℤ)).preimage (Units.continuous_val.sub continuous_const)
    have hne : H.Nonempty := ⟨1, by simp [hH, zero_mem]⟩
    have himg : (Units.val '' H : Set F) = (fun x : F => 1 + x) '' (valBall F (n : ℤ) : Set F) := by
      ext y
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨(h : F) - 1, hh, by ring⟩
      · rintro ⟨x, hx, rfl⟩
        have hy : (1 + x : F) ≠ 0 := by
          intro h0
          have hx1 : x = -1 := by linear_combination h0
          rw [hx1] at hx
          have h1 : normalizedValuation F (-1 : F) ≤ WithZero.exp (-(n : ℤ)) := hx
          rw [Valuation.map_neg, map_one] at h1
          have h2 : (WithZero.exp (0 : ℤ)) ≤ WithZero.exp (-(n : ℤ)) := by
            rw [WithZero.exp_zero]; exact h1
          have h3 := WithZero.exp_le_exp.mp h2
          omega
        refine ⟨Units.mk0 _ hy, ?_, rfl⟩
        simpa [hH] using hx
    have hc : IsCompact H := by
      rw [isOpenEmbedding_units_val.isEmbedding.isCompact_iff, himg]
      exact (isCompact_valBall (n : ℤ)).image (continuous_const.add continuous_id)
    exact (ENNReal.toReal_pos (ho.measure_pos _ hne).ne' hc.measure_lt_top.ne).ne'
  · haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance
    have ho := GLnLocal.isOpen_congruenceSubgroup F 2 m
    have hc := GLnLocal.isCompact_congruenceSubgroup F 2 m
    have hne : (GLnLocal.congruenceSubgroup F 2 m : Set (GL (Fin 2) F)).Nonempty := ⟨1, one_mem _⟩
    exact (ENNReal.toReal_pos (ho.measure_pos _ hne).ne' hc.measure_lt_top.ne).ne'

end GlobalTheory.CompanionTheory.VolNe
end

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.SmallSec

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isClopen_ball (n : ℤ) : IsClopen (valBall F n : Set F) :=
  ⟨isClosed_valBall n, isOpen_valBall n⟩

theorem isClopen_secSet (m : ℕ) : IsClopen (secSet F m) := by
  have e : ∀ i j, Continuous fun X : Matrix (Fin 2) (Fin 3) F => X i j :=
    fun i j => continuous_id.matrix_elem i j
  have hb : ∀ (n : ℤ) (f : Matrix (Fin 2) (Fin 3) F → F), Continuous f →
      IsClopen {X | f X ∈ valBall F n} :=
    fun n f hf => (isClopen_ball n).preimage hf
  exact (hb _ _ ((e 0 0).sub continuous_const)).inter <|
    (hb _ _ (e 0 1)).inter <| (hb _ _ (e 1 0)).inter <|
    (hb _ _ ((e 1 1).sub continuous_const)).inter <| (hb _ _ (e 0 2)).inter (hb _ _ (e 1 2))

theorem isCompact_secSet (m : ℕ) : IsCompact (secSet F m) := by
  set A : Set F := (valBall F (m : ℤ) : Set F) ∪ ((fun x => x + 1) '' (valBall F (m : ℤ) : Set F)) ∪
    (valBall F (-(m : ℤ)) : Set F) with hA
  have hAc : IsCompact A :=
    ((isCompact_valBall _).union ((isCompact_valBall _).image (continuous_id.add continuous_const))).union
      (isCompact_valBall _)
  have hbox : IsCompact (Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 3 => A) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hAc
  refine IsCompact.of_isClosed_subset hbox (isClopen_secSet m).1 ?_
  rintro X ⟨h00, h01, h10, h11, h02, h12⟩ i - j -
  have s1 : ∀ {x : F}, x ∈ valBall F (m : ℤ) → x ∈ A := fun h => Or.inl (Or.inl h)
  have s2 : ∀ {x : F}, x - 1 ∈ valBall F (m : ℤ) → x ∈ A :=
    fun {x} h => Or.inl (Or.inr ⟨x - 1, h, sub_add_cancel x 1⟩)
  have s3 : ∀ {x : F}, x ∈ valBall F (-(m : ℤ)) → x ∈ A := fun h => Or.inr h
  fin_cases i <;> fin_cases j
  · exact s2 h00
  · exact s1 h01
  · exact s3 h02
  · exact s1 h10
  · exact s2 h11
  · exact s3 h12

theorem isLocallyConstant_of_isStd {ψ : AddChar F Circle} (hψ : IsStd ψ) :
    IsLocallyConstant fun x : F => (ψ x : ℂ) := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨{y | y - x ∈ valBall F 0}, (isOpen_valBall 0).preimage (continuous_id.sub continuous_const),
    by simp [zero_mem], fun y hy => ?_⟩
  have : ψ y = ψ (y - x) * ψ x := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
  rw [this, ht _ hy, one_mul]

end

theorem secFun_mem_SB_of_isStd : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
    IsStd ψ → ∀ m : ℕ, secFun ψ m ∈ LFS.SB F := by
  intro F _ _ _ _ _ _ ψ hψ m
  have hg : IsLocallyConstant fun X : Matrix (Fin 2) (Fin 3) F => (ψ (X 1 2) : ℂ) :=
    (isLocallyConstant_of_isStd hψ).comp_continuous (continuous_id.matrix_elem 1 2)
  have hS := isClopen_secSet (F := F) m
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun X => ?_,
    HasCompactSupport.intro (isCompact_secSet m) fun X hX => Set.indicator_of_notMem hX _⟩
  by_cases hX : X ∈ secSet F m
  · obtain ⟨U, hU, hXU, hUc⟩ := (IsLocallyConstant.iff_exists_open _).1 hg X
    refine ⟨U ∩ secSet F m, hU.inter hS.2, ⟨hXU, hX⟩, fun Y hY => ?_⟩
    simp only [secFun]
    rw [Set.indicator_of_mem hY.2, Set.indicator_of_mem hX]
    exact hUc Y hY.1
  · refine ⟨(secSet F m)ᶜ, hS.1.isOpen_compl, hX, fun Y hY => ?_⟩
    simp only [secFun]
    rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem hX]

end GlobalTheory.CompanionTheory.SmallSec
end
end

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.SmallSec

theorem ball_char_std {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)
    (hψ : IsStd ψ) (m : ℕ) (a : F) :
    ∫ t, (valBall F (-(m : ℤ)) : Set F).indicator (fun _ => (1 : ℂ)) t * (ψ (t * a) : ℂ)
        ∂selfDualMeasure ψ =
      (((selfDualMeasure ψ).real (valBall F (-(m : ℤ)) : Set F) : ℝ) : ℂ) *
        (valBall F (m : ℤ) : Set F).indicator (fun _ => (1 : ℂ)) a := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have h := localFourier_indicator_valBall (selfDualMeasure ψ) hc h1 (-(m : ℤ)) a
  rw [h0, zero_sub, neg_neg] at h
  exact h

theorem pFT_secFun_of_mem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)
    (hψ : IsStd ψ) (m : ℕ) (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F)
    (hA : A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧ A 1 0 ∈ valBall F (m : ℤ) ∧
      A 1 1 - 1 ∈ valBall F (m : ℤ)) :
    GL2LocalData.pFT ψ (secFun ψ m) A ξ =
      ((((selfDualMeasure ψ).real (valBall F (-(m : ℤ)) : Set F) : ℝ) : ℂ) *
        (valBall F (m : ℤ) : Set F).indicator (fun _ => (1 : ℂ)) (-ξ 0)) *
      ((((selfDualMeasure ψ).real (valBall F (-(m : ℤ)) : Set F) : ℝ) : ℂ) *
        (valBall F (m : ℤ) : Set F).indicator (fun _ => (1 : ℂ)) (1 - ξ 1)) := by
  obtain ⟨a1, a2, a3, a4⟩ := hA
  have e : ∀ y : Fin 2 → F, secFun ψ m (GL2LocalData.cat3 A y) * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) =
      ∏ i : Fin 2, (fun (i : Fin 2) (t : F) =>
        (valBall F (-(m : ℤ)) : Set F).indicator (fun _ => (1 : ℂ)) t *
          (ψ (t * ![-ξ 0, 1 - ξ 1] i) : ℂ)) i (y i) := by
    intro y
    rw [Fin.prod_univ_two]
    by_cases h0 : y 0 ∈ valBall F (-(m : ℤ))
    · by_cases h1 : y 1 ∈ valBall F (-(m : ℤ))
      · have hm : GL2LocalData.cat3 A y ∈ secSet F m := by
          simp only [secSet, GL2LocalData.cat3, Set.mem_setOf_eq]
          simpa using ⟨a1, a2, a3, a4, h0, h1⟩
        have hy : GL2LocalData.cat3 A y 1 2 = y 1 := by simp [GL2LocalData.cat3]
        simp only [secFun, Set.indicator_of_mem hm, hy,
          Set.indicator_of_mem (show y 0 ∈ (valBall F (-(m : ℤ)) : Set F) from h0),
          Set.indicator_of_mem (show y 1 ∈ (valBall F (-(m : ℤ)) : Set F) from h1), one_mul]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 2
        ring
      · have hm : GL2LocalData.cat3 A y ∉ secSet F m := by
          intro h
          apply h1
          simpa [GL2LocalData.cat3] using h.2.2.2.2.2
        simp only [secFun, Set.indicator_of_notMem hm,
          Set.indicator_of_notMem (show y 1 ∉ (valBall F (-(m : ℤ)) : Set F) from h1)]
        simp
    · have hm : GL2LocalData.cat3 A y ∉ secSet F m := by
        intro h
        apply h0
        simpa [GL2LocalData.cat3] using h.2.2.2.2.1
      simp only [secFun, Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (show y 0 ∉ (valBall F (-(m : ℤ)) : Set F) from h0)]
      simp
  unfold GL2LocalData.pFT LFS.vol2
  have key := integral_fintype_prod_eq_prod (μ := fun _ : Fin 2 => selfDualMeasure ψ)
    (fun (i : Fin 2) (t : F) => (valBall F (-(m : ℤ)) : Set F).indicator (fun _ => (1 : ℂ)) t *
      (ψ (t * ![-ξ 0, 1 - ξ 1] i) : ℂ))
  refine (integral_congr_ae (Filter.Eventually.of_forall e)).trans (key.trans ?_)
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ball_char_std ψ hψ, ball_char_std ψ hψ]

theorem pFT_secFun_of_notMem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)
    (m : ℕ) (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F)
    (hA : ¬ (A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧
      A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ))) :
    GL2LocalData.pFT ψ (secFun ψ m) A ξ = 0 := by
  have e : ∀ y : Fin 2 → F, secFun ψ m (GL2LocalData.cat3 A y) * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) = 0 := by
    intro y
    have hm : GL2LocalData.cat3 A y ∉ secSet F m := by
      intro h
      apply hA
      simpa [GL2LocalData.cat3] using (⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩ :
        GL2LocalData.cat3 A y 0 0 - 1 ∈ valBall F (m : ℤ) ∧ GL2LocalData.cat3 A y 0 1 ∈ valBall F (m : ℤ) ∧
        GL2LocalData.cat3 A y 1 0 ∈ valBall F (m : ℤ) ∧ GL2LocalData.cat3 A y 1 1 - 1 ∈ valBall F (m : ℤ))
    simp only [secFun, Set.indicator_of_notMem hm, zero_mul]
  unfold GL2LocalData.pFT
  simp_rw [e]
  simp

theorem pFT_secFun : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (m : ℕ) (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F),
  ((A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧ A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ) ∧ ξ 0 ∈ valBall F (m : ℤ) ∧ ξ 1 - 1 ∈ valBall F (m : ℤ)) → GL2LocalData.pFT ψ (secFun ψ m) A ξ = (((selfDualMeasure ψ).real (valBall F (-(m : ℤ)) : Set F) : ℝ) : ℂ) ^ 2) ∧
  (¬ (A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧ A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ) ∧ ξ 0 ∈ valBall F (m : ℤ) ∧ ξ 1 - 1 ∈ valBall F (m : ℤ)) → GL2LocalData.pFT ψ (secFun ψ m) A ξ = 0) := by
  intro F _ _ _ _ _ _ ψ hψ m A ξ
  have hneg : -ξ 0 ∈ valBall F (m : ℤ) ↔ ξ 0 ∈ valBall F (m : ℤ) := neg_mem_iff
  have hsub : 1 - ξ 1 ∈ valBall F (m : ℤ) ↔ ξ 1 - 1 ∈ valBall F (m : ℤ) := by
    rw [← neg_sub, neg_mem_iff]
  constructor
  · rintro ⟨a1, a2, a3, a4, x0, x1⟩
    rw [pFT_secFun_of_mem ψ hψ m A ξ ⟨a1, a2, a3, a4⟩,
      Set.indicator_of_mem (show -ξ 0 ∈ (valBall F (m : ℤ) : Set F) from hneg.mpr x0),
      Set.indicator_of_mem (show 1 - ξ 1 ∈ (valBall F (m : ℤ) : Set F) from hsub.mpr x1)]
    ring
  · intro h
    by_cases hA : A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧
        A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ)
    · obtain ⟨a1, a2, a3, a4⟩ := hA
      rw [pFT_secFun_of_mem ψ hψ m A ξ ⟨a1, a2, a3, a4⟩]
      by_cases x0 : ξ 0 ∈ valBall F (m : ℤ)
      · have x1 : ξ 1 - 1 ∉ valBall F (m : ℤ) := fun x1 => h ⟨a1, a2, a3, a4, x0, x1⟩
        rw [Set.indicator_of_notMem (show 1 - ξ 1 ∉ (valBall F (m : ℤ) : Set F) from
          fun hx => x1 (hsub.mp hx))]
        simp
      · rw [Set.indicator_of_notMem (show -ξ 0 ∉ (valBall F (m : ℤ) : Set F) from
          fun hx => x0 (hneg.mp hx))]
        simp
    · exact pFT_secFun_of_notMem ψ m A ξ hA

end GlobalTheory.CompanionTheory.SmallSec
end
end

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.SintSec

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem ball_iff {y : F} {m : ℕ} :
    y ∈ valBall F (m : ℤ) ↔
      ValuativeRel.valuation F y ≤ ValuativeRel.valuation F (GLnLocal.uniformizer F : F) ^ m := by
  rw [← map_pow, ← normalizedValuation_le_iff, map_pow,
    normalizedValuation_uniformizer (GLnLocal.irreducible_uniformizer F), ← WithZero.exp_nsmul,
    mem_valBall]
  simp

theorem modulus_of_sub_one {x : F} (h : x - 1 ∈ valBall F 1) : modulus x = 1 := by
  have := modulus_add_eq (x := (1 : F)) (d := x - 1) one_ne_zero (by rw [ord_one]; simpa using h)
  simpa using this

theorem inv_mem_zero {x : F} (h : x - 1 ∈ valBall F 1) : x⁻¹ ∈ valBall F 0 := by
  obtain ⟨h0, ho⟩ := modulus_eq_one_iff.1 (modulus_of_sub_one h)
  rw [mem_valBall_iff_le_ord (inv_ne_zero h0), ord_inv h0, ho]
  simp

theorem one_mem_zero : (1 : F) ∈ valBall F 0 :=
  mem_valBall_zero_iff.2 (one_mem _)

theorem mem_zero_of_mem {x : F} {m : ℤ} (hm : 0 ≤ m) (h : x ∈ valBall F m) : x ∈ valBall F 0 :=
  valBall_antitone hm h

theorem mem_zero_of_sub {x : F} {m : ℤ} (hm : 0 ≤ m) (h : x - 1 ∈ valBall F m) :
    x ∈ valBall F 0 := by
  have := add_mem (mem_zero_of_mem hm h) one_mem_zero
  simpa using this

theorem mul_zero_mem {m : ℤ} {x y : F} (hx : x ∈ valBall F m) (hy : y ∈ valBall F 0) :
    x * y ∈ valBall F m := by
  simpa using mul_mem_valBall hx hy

theorem det_sub_one {m : ℕ} {A : Matrix (Fin 2) (Fin 2) F}
    (h00 : A 0 0 - 1 ∈ valBall F (m : ℤ)) (h01 : A 0 1 ∈ valBall F (m : ℤ))
    (h10 : A 1 0 ∈ valBall F (m : ℤ)) (h11 : A 1 1 - 1 ∈ valBall F (m : ℤ)) :
    A.det - 1 ∈ valBall F (m : ℤ) := by
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by omega
  have e : A.det - 1 = (A 0 0 - 1) * A 1 1 + (A 1 1 - 1) - A 0 1 * A 1 0 := by
    rw [Matrix.det_fin_two]; ring
  rw [e]
  exact sub_mem (add_mem (mul_zero_mem h00 (mem_zero_of_sub hm0 h11)) h11)
    (mul_zero_mem h01 (mem_zero_of_mem hm0 h10))

theorem mem_K_iff {m : ℕ} (hm : 1 ≤ m) (g : GL (Fin 2) F) :
    g ∈ GLnLocal.congruenceSubgroup F 2 m ↔
      g.val 0 0 - 1 ∈ valBall F (m : ℤ) ∧ g.val 0 1 ∈ valBall F (m : ℤ) ∧
        g.val 1 0 ∈ valBall F (m : ℤ) ∧ g.val 1 1 - 1 ∈ valBall F (m : ℤ) := by
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by omega
  have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  constructor
  · intro hg
    have h := ((GLnLocal.mem_congruenceSubgroup_iff F 2).1 hg).2
    refine ⟨ball_iff.2 ?_, ball_iff.2 ?_, ball_iff.2 ?_, ball_iff.2 ?_⟩
    · simpa using h 0 0
    · simpa using h 0 1
    · simpa using h 1 0
    · simpa using h 1 1
  · rintro ⟨h00, h01, h10, h11⟩
    have hd := det_sub_one h00 h01 h10 h11
    have hdi : (g.val).det⁻¹ ∈ valBall F 0 := inv_mem_zero (valBall_antitone hm1 hd)
    have z00 := mem_zero_of_sub hm0 h00
    have z01 := mem_zero_of_mem hm0 h01
    have z10 := mem_zero_of_mem hm0 h10
    have z11 := mem_zero_of_sub hm0 h11
    have hinv : (g⁻¹ : GL (Fin 2) F).val =
        (g.val).det⁻¹ • !![g.val 1 1, -g.val 0 1; -g.val 1 0, g.val 0 0] := by
      rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
    have hmul : ∀ {x : F}, x ∈ valBall F 0 → (g.val).det⁻¹ * x ∈ 𝒪[F] := fun hx =>
      mem_valBall_zero_iff.1 (by simpa using mul_mem_valBall hdi hx)
    refine (GLnLocal.mem_congruenceSubgroup_iff F 2).2
      ⟨(GLnLocal.mem_integralGL_iff F 2).2 ⟨?_, ?_⟩, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j
      · exact mem_valBall_zero_iff.1 z00
      · exact mem_valBall_zero_iff.1 z01
      · exact mem_valBall_zero_iff.1 z10
      · exact mem_valBall_zero_iff.1 z11
    · intro i j
      change (g⁻¹ : GL (Fin 2) F).val i j ∈ 𝒪[F]
      rw [hinv]
      fin_cases i <;> fin_cases j
      · simpa using hmul z11
      · simpa using hmul (neg_mem z01)
      · simpa using hmul (neg_mem z10)
      · simpa using hmul z00
    · intro i j
      fin_cases i <;> fin_cases j
      · simpa using ball_iff.1 h00
      · simpa using ball_iff.1 h01
      · simpa using ball_iff.1 h10
      · simpa using ball_iff.1 h11

def RowOK (m : ℕ) (h : GL (Fin 2) F) : Prop :=
  h.val 1 0 ∈ valBall F (m : ℤ) ∧ h.val 1 1 - 1 ∈ valBall F (m : ℤ)

theorem rowOK_mul {m : ℕ} (hm : 1 ≤ m) {h k : GL (Fin 2) F} (hh : RowOK m h)
    (hk : k ∈ GLnLocal.congruenceSubgroup F 2 m) : RowOK m (h * k) := by
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by omega
  obtain ⟨h00, h01, h10, h11⟩ := (mem_K_iff hm k).1 hk
  obtain ⟨a, b⟩ := hh
  have e0 : (h * k).val 1 0 =
      h.val 1 0 * k.val 0 0 + ((h.val 1 1 - 1) * k.val 1 0 + k.val 1 0) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e1 : (h * k).val 1 1 - 1 =
      h.val 1 0 * k.val 0 1 + ((h.val 1 1 - 1) * k.val 1 1 + (k.val 1 1 - 1)) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  refine ⟨?_, ?_⟩
  · rw [e0]
    exact add_mem (mul_zero_mem a (mem_zero_of_sub hm0 h00))
      (add_mem (mul_zero_mem b (mem_zero_of_mem hm0 h10)) h10)
  · rw [e1]
    exact add_mem (mul_zero_mem a (mem_zero_of_mem hm0 h01))
      (add_mem (mul_zero_mem b (mem_zero_of_sub hm0 h11)) h11)

theorem rowOK_mul_inv_iff {m : ℕ} (hm : 1 ≤ m) {h g : GL (Fin 2) F}
    (hg : g ∈ GLnLocal.congruenceSubgroup F 2 m) : RowOK m (h * g⁻¹) ↔ RowOK m h := by
  constructor
  · intro hh
    simpa using rowOK_mul hm hh hg
  · intro hh
    exact rowOK_mul hm hh (inv_mem hg)

theorem mp_det_of_mem {m : ℕ} (hm : 1 ≤ m) {g : GL (Fin 2) F}
    (hg : g ∈ GLnLocal.congruenceSubgroup F 2 m) :
    mp (Matrix.GeneralLinearGroup.det g) (1 / 2) = 1 := by
  have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  obtain ⟨h00, h01, h10, h11⟩ := (mem_K_iff hm g).1 hg
  have hmod : modulus (g.val).det = 1 :=
    modulus_of_sub_one (valBall_antitone hm1 (det_sub_one h00 h01 h10 h11))
  simp [mp, hmod]

end

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (W' : GL (Fin 2) F → ℂ) (m : ℕ), 1 ≤ m →
  (∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, W' (g * u) = W' g) →
  ∀ Φ ∈ LFS.SB F, ∀ V : ℂ,
  (∀ (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F), (A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧ A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ) ∧ ξ 0 ∈ valBall F (m : ℤ) ∧ ξ 1 - 1 ∈ valBall F (m : ℤ)) → GL2LocalData.pFT ψ Φ A ξ = V) →
  (∀ (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F), ¬ (A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧ A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ) ∧ ξ 0 ∈ valBall F (m : ℤ) ∧ ξ 1 - 1 ∈ valBall F (m : ℤ)) → GL2LocalData.pFT ψ Φ A ξ = 0) →
  (∀ h : GL (Fin 2) F, h.val 1 0 ∈ valBall F (m : ℤ) → h.val 1 1 - 1 ∈ valBall F (m : ℤ) →
    LFS.Wp ψ W' Φ (GL2LocalData.em h) = (V * (((LFS.hG ψ).real (GLnLocal.congruenceSubgroup F 2 m : Set (GL (Fin 2) F)) : ℝ) : ℂ)) * mp (Matrix.GeneralLinearGroup.det h) (1 / 2) * W' h) ∧
  (∀ h : GL (Fin 2) F, ¬ (h.val 1 0 ∈ valBall F (m : ℤ) ∧ h.val 1 1 - 1 ∈ valBall F (m : ℤ)) → LFS.Wp ψ W' Φ (GL2LocalData.em h) = 0) := by
  intro F _ _ _ _ _ _ ψ hψ W' m hm hW Φ hΦ V hV h0
  have hmeas : MeasurableSet (GLnLocal.congruenceSubgroup F 2 m : Set (GL (Fin 2) F)) :=
    (GLnLocal.isOpen_congruenceSubgroup F 2 m).measurableSet
  have key := fun h => GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.main F ψ hψ W' Φ hΦ h
  refine ⟨fun h h1 h2 => ?_, fun h hn => ?_⟩
  · have hrow : RowOK m h := ⟨h1, h2⟩
    have hf : (fun g : GL (Fin 2) F => GL2LocalData.pFT ψ Φ g.val (GL2LocalData.e2r (h * g⁻¹)) *
        mp (Matrix.GeneralLinearGroup.det g) (1 / 2) * W' (h * g⁻¹)) =
        (GLnLocal.congruenceSubgroup F 2 m : Set (GL (Fin 2) F)).indicator
          (fun _ => V * W' h) := by
      funext g
      by_cases hg : g ∈ GLnLocal.congruenceSubgroup F 2 m
      · rw [Set.indicator_of_mem (show g ∈ (GLnLocal.congruenceSubgroup F 2 m : Set _) from hg)]
        obtain ⟨a00, a01, a10, a11⟩ := (mem_K_iff hm g).1 hg
        obtain ⟨r0, r1⟩ := (rowOK_mul_inv_iff hm hg).2 hrow
        rw [hV g.val (GL2LocalData.e2r (h * g⁻¹)) ⟨a00, a01, a10, a11, r0, r1⟩, mp_det_of_mem hm hg,
          hW h g⁻¹ (inv_mem hg), mul_one]
      · rw [Set.indicator_of_notMem (show g ∉ (GLnLocal.congruenceSubgroup F 2 m : Set _) from hg),
          h0 g.val (GL2LocalData.e2r (h * g⁻¹))
            (fun c => hg ((mem_K_iff hm g).2 ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1⟩))]
        simp
    rw [key h, hf, integral_indicator_const _ hmeas, Complex.real_smul]
    ring
  · have hf : (fun g : GL (Fin 2) F => GL2LocalData.pFT ψ Φ g.val (GL2LocalData.e2r (h * g⁻¹)) *
        mp (Matrix.GeneralLinearGroup.det g) (1 / 2) * W' (h * g⁻¹)) = fun _ => 0 := by
      funext g
      rw [h0 g.val (GL2LocalData.e2r (h * g⁻¹)) ?_]
      · simp
      · rintro ⟨a00, a01, a10, a11, r0, r1⟩
        have hg := (mem_K_iff hm g).2 ⟨a00, a01, a10, a11⟩
        exact hn ((rowOK_mul_inv_iff hm hg).1 ⟨r0, r1⟩)
    rw [key h, hf]
    simp

end GlobalTheory.CompanionTheory.SintSec
end
end

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.SmallSecSupp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem valuation_le_of_mem_valBall {x : F} {m : ℕ} (h : x ∈ valBall F (m : ℤ)) :
    ValuativeRel.valuation F x ≤ ValuativeRel.valuation F (GLnLocal.uniformizer F : F) ^ m := by
  obtain ⟨a, ha, rfl⟩ := GodementJacquet.mem_valBall_iff_exists.1 h
  have ha' : ValuativeRel.valuation F a ≤ 1 := ha
  rw [map_mul, map_pow]
  exact mul_le_of_le_one_right' ha'

theorem valuation_eq_one_of_sub_one {x : F} (h : x - 1 ∈ valBall F 1) :
    ValuativeRel.valuation F x = 1 := by
  have h1 : ValuativeRel.valuation F (x - 1) < 1 := mem_valBall_one_iff.1 h
  have h2 : ValuativeRel.valuation F (x - 1) < ValuativeRel.valuation F (1 : F) := by
    simpa using h1
  simpa using Valuation.map_eq_of_sub_lt (ValuativeRel.valuation F) h2

theorem inv_mem_valBall_zero {x : F} (h : ValuativeRel.valuation F x = 1) :
    x⁻¹ ∈ valBall F 0 := by
  refine mem_valBall_zero_iff.2 ?_
  change ValuativeRel.valuation F x⁻¹ ≤ 1
  rw [map_inv₀, h, inv_one]

theorem ne_zero_of_valuation_eq_one {x : F} (h : ValuativeRel.valuation F x = 1) : x ≠ 0 := by
  rintro rfl
  simp at h

theorem mem_zero_of_nat {x : F} {m : ℕ} (h : x ∈ valBall F (m : ℤ)) : x ∈ valBall F 0 :=
  valBall_antitone (by positivity) h

theorem mem_one_of_nat {x : F} {m : ℕ} (hm : 1 ≤ m) (h : x ∈ valBall F (m : ℤ)) :
    x ∈ valBall F 1 :=
  valBall_antitone (by exact_mod_cast hm) h

theorem one_mem_zero : (1 : F) ∈ valBall F 0 := mem_valBall_zero_iff.2 (one_mem _)

theorem mem_zero_of_sub_one {x : F} {m : ℕ} (h : x - 1 ∈ valBall F (m : ℤ)) :
    x ∈ valBall F 0 := by
  simpa using add_mem (mem_zero_of_nat h) (one_mem_zero (F := F))

theorem mem_congruenceSubgroup_of_entries (g : GL (Fin 2) F) {m : ℕ} (hm : 1 ≤ m)
    (h00 : g.val 0 0 - 1 ∈ valBall F (m : ℤ)) (h01 : g.val 0 1 ∈ valBall F (m : ℤ))
    (h10 : g.val 1 0 ∈ valBall F (m : ℤ)) (h11 : g.val 1 1 - 1 ∈ valBall F (m : ℤ)) :
    g ∈ GLnLocal.congruenceSubgroup F 2 m := by
  have i00 : g.val 0 0 ∈ valBall F 0 := mem_zero_of_sub_one h00
  have i11 : g.val 1 1 ∈ valBall F 0 := mem_zero_of_sub_one h11
  have i01 : g.val 0 1 ∈ valBall F 0 := mem_zero_of_nat h01
  have i10 : g.val 1 0 ∈ valBall F 0 := mem_zero_of_nat h10
  have hD : g.val.det - 1 ∈ valBall F 1 := by
    rw [Matrix.det_fin_two]
    have e : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 - 1 =
        (g.val 0 0 - 1) * g.val 1 1 + (g.val 1 1 - 1) - g.val 0 1 * g.val 1 0 := by ring
    rw [e]
    refine sub_mem (add_mem ?_ (mem_one_of_nat hm h11)) ?_
    · simpa using mul_mem_valBall (mem_one_of_nat hm h00) i11
    · simpa using mul_mem_valBall (mem_one_of_nat hm h01) i10
  have hinv := inv_mem_valBall_zero (valuation_eq_one_of_sub_one hD)
  have hinvval : ((g⁻¹ : GL (Fin 2) F)).val = (g.val.det)⁻¹ • Matrix.adjugate g.val := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  have mulz : ∀ {y : F}, y ∈ valBall F 0 → (g.val.det)⁻¹ * y ∈ 𝒪[F] := fun hy =>
    mem_valBall_zero_iff.1 (by simpa using mul_mem_valBall hinv hy)
  rw [GLnLocal.mem_congruenceSubgroup_iff, GLnLocal.mem_integralGL_iff]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact mem_valBall_zero_iff.1 i00
    · exact mem_valBall_zero_iff.1 i01
    · exact mem_valBall_zero_iff.1 i10
    · exact mem_valBall_zero_iff.1 i11
  · change ((g⁻¹ : GL (Fin 2) F)).val i j ∈ 𝒪[F]
    rw [hinvval, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · simpa using mulz i11
    · simpa using mulz (neg_mem i01)
    · simpa using mulz (neg_mem i10)
    · simpa using mulz i00
  · fin_cases i <;> fin_cases j
    · simpa using valuation_le_of_mem_valBall h00
    · simpa using valuation_le_of_mem_valBall h01
    · simpa using valuation_le_of_mem_valBall h10
    · simpa using valuation_le_of_mem_valBall h11

theorem exists_decomp (h : GL (Fin 2) F) (hd : h.val 1 1 ≠ 0) :
    ∃ (a : Fˣ) (k : GL (Fin 2) F), (a : F) = h.val.det / h.val 1 1 ∧
      k.val = !![1, 0; h.val 1 0, h.val 1 1] ∧
      h = uni2 (h.val 0 1 / h.val 1 1) * (dg2 a 1 * k) := by
  have hdet : h.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero
  refine ⟨Units.mk0 (h.val.det / h.val 1 1) (div_ne_zero hdet hd),
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; h.val 1 0, h.val 1 1]
      (by simpa [Matrix.det_fin_two] using hd), rfl, rfl, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.det_fin_two, Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible] <;>
    field_simp <;> ring

theorem exists_decomp_congruence {m : ℕ} (hm : 1 ≤ m) (h : GL (Fin 2) F)
    (h10 : h.val 1 0 ∈ valBall F (m : ℤ)) (h11 : h.val 1 1 - 1 ∈ valBall F (m : ℤ)) :
    h.val 1 1 ≠ 0 ∧ ∃ (a : Fˣ) (k : GL (Fin 2) F), (a : F) = h.val.det / h.val 1 1 ∧
      k.val = !![1, 0; h.val 1 0, h.val 1 1] ∧ k ∈ GLnLocal.congruenceSubgroup F 2 m ∧
      h = uni2 (h.val 0 1 / h.val 1 1) * (dg2 a 1 * k) := by
  have hv := valuation_eq_one_of_sub_one (mem_one_of_nat hm h11)
  have hd := ne_zero_of_valuation_eq_one hv
  obtain ⟨a, k, ha, hk, e⟩ := exists_decomp h hd
  refine ⟨hd, a, k, ha, hk, ?_, e⟩
  refine mem_congruenceSubgroup_of_entries k hm ?_ ?_ ?_ ?_ <;> rw [hk]
  · simp
  · simp
  · simpa using h10
  · simpa using h11

theorem diag_mul_lower_triangular_val (a : Fˣ) (k : GL (Fin 2) F) {c d : F} (hk : k.val = !![1, 0; c, d]) :
    (dg2 a 1 * k).val = !![(a : F), 0; c, d] := by
  rw [Units.val_mul, hk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_mul_lower_entries (x : F) (g : GL (Fin 2) F) (j : Fin 2) :
    (uni2 x * g).val 1 j = g.val 1 j := by
  fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

variable [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem mp_det_half_eq_one {n : ℕ} (hn : 1 ≤ n) {u : GL (Fin 2) F}
    (hu : u ∈ GLnLocal.congruenceSubgroup F 2 n) :
    mp (Matrix.GeneralLinearGroup.det u) (1 / 2) = 1 := by
  have hD : ((Matrix.GeneralLinearGroup.det u : Fˣ) : F) - 1 ∈ valBall F 1 := by
    have e := fun i j => GodementSectionLocal.sub_one_mem_valBall_of_mem_congruenceSubgroup hu i j
    have h00 := e 0 0
    have h01 := e 0 1
    have h10 := e 1 0
    have h11 := e 1 1
    simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, sub_zero] at h00 h01 h10 h11
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    have e2 : u.val 0 0 * u.val 1 1 - u.val 0 1 * u.val 1 0 - 1 =
        (u.val 0 0 - 1) * u.val 1 1 + (u.val 1 1 - 1) - u.val 0 1 * u.val 1 0 := by ring
    rw [e2]
    refine sub_mem (add_mem ?_ (mem_one_of_nat hn h11)) ?_
    · simpa using mul_mem_valBall (mem_one_of_nat hn h00) (mem_zero_of_sub_one h11)
    · simpa using mul_mem_valBall (mem_one_of_nat hn h01) (mem_zero_of_nat h10)
  have hv := valuation_eq_one_of_sub_one hD
  have h1 : ((Matrix.GeneralLinearGroup.det u : Fˣ) : F) ∈ 𝒪[F] := by
    change ValuativeRel.valuation F _ ≤ 1
    exact hv.le
  have h2 : (((Matrix.GeneralLinearGroup.det u)⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    rw [Units.val_inv_eq_inv_val]
    exact mem_valBall_zero_iff.1 (inv_mem_valBall_zero hv)
  have hmod := GlobalTheory.CompanionTheory.LocalTestVectors.modulus_eq_one_of_integral h1 h2
  unfold mp
  rw [hmod]
  simp

theorem support_and_value : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (W' : GL (Fin 2) F → ℂ) (W : GL (Fin 3) F → ℂ) (n m : ℕ) (C c : ℂ), 1 ≤ n → n ≤ m →
  (∀ (y : F) (g : GL (Fin 2) F), W' (uni2 y * g) = (ψ y : ℂ) * W' g) →
  (∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, W' (g * u) = W' g) →
  (∀ a : Fˣ, (a : F) - 1 ∈ valBall F (n : ℤ) → W' (dg2 a 1) = C) →
  (∀ a : Fˣ, (a : F) - 1 ∉ valBall F (n : ℤ) → W' (dg2 a 1) = 0) →
  (∀ h : GL (Fin 2) F, h.val 1 0 ∈ valBall F (m : ℤ) → h.val 1 1 - 1 ∈ valBall F (m : ℤ) →
    W (GL2LocalData.em h) = c * mp (Matrix.GeneralLinearGroup.det h) (1 / 2) * W' h) →
  (∀ h : GL (Fin 2) F, ¬ (h.val 1 0 ∈ valBall F (m : ℤ) ∧ h.val 1 1 - 1 ∈ valBall F (m : ℤ)) → W (GL2LocalData.em h) = 0) →
  (∀ h, W (GL2LocalData.em h) ≠ 0 → ∃ x : F, ∃ u : GL (Fin 2) F, (u ∈ GLnLocal.congruenceSubgroup F 2 n ∧ u.val 1 0 ∈ valBall F (m : ℤ) ∧ u.val 1 1 - 1 ∈ valBall F (m : ℤ)) ∧ h = uni2 x * u) ∧
  ∀ (x : F) (u : GL (Fin 2) F), u ∈ GLnLocal.congruenceSubgroup F 2 n → u.val 1 0 ∈ valBall F (m : ℤ) → u.val 1 1 - 1 ∈ valBall F (m : ℤ) →
    W (GL2LocalData.em (uni2 x * u)) = (ψ x : ℂ) * (c * C) := by
  intro F _ _ _ _ _ _ ψ hψ W' W n m C c hn hnm hpsi hinv hC h0 hval hzero
  have hm : 1 ≤ m := hn.trans hnm
  have ball : ∀ {x : F}, x ∈ valBall F (m : ℤ) → x ∈ valBall F (n : ℤ) := fun h =>
    valBall_antitone (by exact_mod_cast hnm) h
  refine ⟨fun h hne => ?_, fun x u hu u10 u11 => ?_⟩
  · have hrow : h.val 1 0 ∈ valBall F (m : ℤ) ∧ h.val 1 1 - 1 ∈ valBall F (m : ℤ) := by
      by_contra hcon
      exact hne (hzero h hcon)
    obtain ⟨h10, h11⟩ := hrow
    obtain ⟨-, a, k, -, hk, hkm, e⟩ := exists_decomp_congruence hm h h10 h11
    have hW : W' h ≠ 0 := by
      intro h00
      apply hne
      rw [hval h h10 h11, h00, mul_zero]
    have hWa : W' (dg2 a 1) ≠ 0 := by
      intro h00
      apply hW
      rw [e, hpsi, hinv _ k hkm, h00, mul_zero]
    have ha : (a : F) - 1 ∈ valBall F (n : ℤ) := by
      by_contra hcon
      exact hWa (h0 a hcon)
    have hv := diag_mul_lower_triangular_val a k hk
    refine ⟨h.val 0 1 / h.val 1 1, dg2 a 1 * k, ⟨?_, ?_, ?_⟩, e⟩
    · refine mem_congruenceSubgroup_of_entries _ hn ?_ ?_ ?_ ?_ <;> rw [hv]
      · simpa using ha
      · simp
      · simpa using ball h10
      · simpa using ball h11
    · rw [hv]; simpa using h10
    · rw [hv]; simpa using h11
  · have e := fun i j => GodementSectionLocal.sub_one_mem_valBall_of_mem_congruenceSubgroup hu i j
    have h00 := e 0 0
    have h01 := e 0 1
    simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, sub_zero] at h00 h01
    obtain ⟨hd, a, k, ha, hk, hkm, ed⟩ := exists_decomp_congruence hm u u10 u11
    have hv1 := valuation_eq_one_of_sub_one (mem_one_of_nat hm u11)
    have hdi := inv_mem_valBall_zero hv1
    have hy : u.val 0 1 / u.val 1 1 ∈ 𝒪[F] := by
      rw [div_eq_mul_inv]
      exact mem_valBall_zero_iff.1 (by simpa using mul_mem_valBall (mem_zero_of_nat h01) hdi)
    have hψy : (ψ (u.val 0 1 / u.val 1 1) : ℂ) = 1 :=
      GlobalTheory.CompanionTheory.SphOne.coe_eq_one_of_isStd hψ _ hy
    have ha1 : (a : F) - 1 ∈ valBall F (n : ℤ) := by
      have e3 : (a : F) - 1 =
          ((u.val 0 0 - 1) * u.val 1 1 - u.val 0 1 * u.val 1 0) * (u.val 1 1)⁻¹ := by
        rw [ha, Matrix.det_fin_two]
        field_simp
        ring
      rw [e3]
      have t1 : (u.val 0 0 - 1) * u.val 1 1 ∈ valBall F (n : ℤ) := by
        simpa using mul_mem_valBall h00 (mem_zero_of_sub_one u11)
      have t2 : u.val 0 1 * u.val 1 0 ∈ valBall F (n : ℤ) := by
        simpa using mul_mem_valBall h01 (mem_zero_of_nat u10)
      simpa using mul_mem_valBall (sub_mem t1 t2) hdi
    have hWu : W' u = C := by
      rw [ed, hpsi, hinv _ k hkm, hC a ha1, hψy, one_mul]
    have r10 : (uni2 x * u).val 1 0 ∈ valBall F (m : ℤ) := by rw [unipotent_mul_lower_entries]; exact u10
    have r11 : (uni2 x * u).val 1 1 - 1 ∈ valBall F (m : ℤ) := by rw [unipotent_mul_lower_entries]; exact u11
    rw [hval _ r10 r11, GlobalTheory.CompanionTheory.WhittakerPsi.det_left_unipotent_mul, mp_det_half_eq_one hn hu, hpsi, hWu]
    ring

end GlobalTheory.CompanionTheory.SmallSecSupp
end
end

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

namespace GlobalTheory.CompanionTheory.SmallSec

theorem torus : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ n₀ : ℕ,
  ∃ n : ℕ, n₀ ≤ n ∧ 1 ≤ n ∧ ∃ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∃ C : ℂ, C ≠ 0 ∧
    (∀ a : Fˣ, (a : F) - 1 ∈ valBall F (n : ℤ) → W2 ψ ν ν⁻¹ φ (dg2 a 1) = C) ∧
    (∀ a : Fˣ, (a : F) - 1 ∉ valBall F (n : ℤ) → W2 ψ ν ν⁻¹ φ (dg2 a 1) = 0) := by
  intro F _ _ _ _ _ _ ψ hψ ν hν n₀
  obtain ⟨n, hn, hn1, hν1⟩ := GlobalTheory.CompanionTheory.CharTriv.exists_trivial_on_principal F ν hν n₀
  obtain ⟨hf, hg, hφ⟩ := GlobalTheory.CompanionTheory.TorSB.tor_schwartzBruhat F ψ hψ n hn1
  obtain ⟨hV, hH, -⟩ := GlobalTheory.CompanionTheory.VolNe.volumes_ne_zero F ψ
  have hν' : IsUnit1 ν⁻¹ := by
    refine ⟨hν.1.inv, fun x => ?_⟩
    have := hν.2 x
    simp [this]
  refine ⟨n, hn, hn1, _, hφ, (((selfDualMeasure ψ).real (valBall F (-(n : ℤ)) : Set F) : ℝ) : ℂ) * (((multHaar F).real {h : Fˣ | (h : F) - 1 ∈ valBall F (n : ℤ)} : ℝ) : ℂ), mul_ne_zero (Complex.ofReal_ne_zero.2 (hV _))
    (Complex.ofReal_ne_zero.2 (hH n hn1)), fun a ha => ?_, fun a ha => ?_⟩
  · rw [GlobalTheory.CompanionTheory.WhittakerTorus.swd F ψ hψ ν ν⁻¹ hν hν' _ hf _ hg a, ((GlobalTheory.CompanionTheory.KirTorus.torus_integral F ψ hψ ν n hn1 hν1 a).1 ha)]
    have h1 : mp a (1 / 2) = 1 := by
      simp [mp, GlobalTheory.CompanionTheory.SmallSec.modulus_eq_one_of_sub_one_mem_valBall_pos F n hn1 a ha]
    rw [h1]
    simp [hν1 a ha]
  · rw [GlobalTheory.CompanionTheory.WhittakerTorus.swd F ψ hψ ν ν⁻¹ hν hν' _ hf _ hg a, ((GlobalTheory.CompanionTheory.KirTorus.torus_integral F ψ hψ ν n hn1 hν1 a).2 ha)]
    simp

theorem sec : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (W' : GL (Fin 2) F → ℂ) (m : ℕ), 1 ≤ m →
  (∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, W' (g * u) = W' g) →
  ∃ Φ ∈ LFS.SB F, ∃ c : ℂ, c ≠ 0 ∧
    (∀ h : GL (Fin 2) F, h.val 1 0 ∈ valBall F (m : ℤ) → h.val 1 1 - 1 ∈ valBall F (m : ℤ) →
      LFS.Wp ψ W' Φ (GL2LocalData.em h) = c * mp (Matrix.GeneralLinearGroup.det h) (1 / 2) * W' h) ∧
    (∀ h : GL (Fin 2) F, ¬ (h.val 1 0 ∈ valBall F (m : ℤ) ∧ h.val 1 1 - 1 ∈ valBall F (m : ℤ)) →
      LFS.Wp ψ W' Φ (GL2LocalData.em h) = 0) := by
  intro F _ _ _ _ _ _ ψ hψ W' m hm hW'
  obtain ⟨hV, -, hK⟩ := GlobalTheory.CompanionTheory.VolNe.volumes_ne_zero F ψ
  obtain ⟨h1, h0⟩ := GlobalTheory.CompanionTheory.SintSec.main F ψ hψ W' m hm hW' (secFun ψ m) (GlobalTheory.CompanionTheory.SmallSec.secFun_mem_SB_of_isStd F ψ hψ m) _
    (fun A ξ h => (GlobalTheory.CompanionTheory.SmallSec.pFT_secFun F ψ hψ m A ξ).1 h) (fun A ξ h => (GlobalTheory.CompanionTheory.SmallSec.pFT_secFun F ψ hψ m A ξ).2 h)
  exact ⟨secFun ψ m, GlobalTheory.CompanionTheory.SmallSec.secFun_mem_SB_of_isStd F ψ hψ m, _, mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (hV _)))
    (Complex.ofReal_ne_zero.2 (hK m)), h1, h0⟩

end GlobalTheory.CompanionTheory.SmallSec
namespace GlobalTheory.CompanionTheory.SmallSec

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
  (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ U ∈ 𝓝 (1 : GL (Fin 2) F),
  ∃ W ∈ LFS.VF ψ (V2 ψ ν ν⁻¹), ∃ (S : Set (GL (Fin 2) F)) (C₁ : ℂ), IsOpen S ∧ (1 : GL (Fin 2) F) ∈ S ∧ S ⊆ U ∧ S ⊆ GL2LocalData.K2 F ∧ C₁ ≠ 0 ∧
    (∀ h, W (GL2LocalData.em h) ≠ 0 → ∃ x, ∃ u ∈ S, h = uni2 x * u) ∧
    ∀ x, ∀ u ∈ S, W (GL2LocalData.em (uni2 x * u)) = (ψ x : ℂ) * C₁ := by
  intro F _ _ _ _ _ _ ψ hψ ν hν U hU
  have hν' : IsUnit1 ν⁻¹ := by
    refine ⟨?_, fun x => ?_⟩
    · exact hν.1.inv
    · have := hν.2 x
      simp [this]
  obtain ⟨n₀, -, hn₀⟩ := (GLnLocal.hasBasis_nhds_one F 2).mem_iff.mp hU
  obtain ⟨n, hn, hn1, φ, hφ, C, hC, hc1, hc0⟩ := GlobalTheory.CompanionTheory.SmallSec.torus F ψ hψ ν hν n₀
  obtain ⟨V, hV⟩ := GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth F ψ hψ ν ν⁻¹ hν hν' φ hφ
  obtain ⟨m', -, hm'⟩ := (GLnLocal.hasBasis_nhds_one F 2).mem_iff.mp
    (V.isOpen.mem_nhds V.one_mem)
  set W' := W2 ψ ν ν⁻¹ φ with hW'
  have hW'mem : W' ∈ V2 ψ ν ν⁻¹ := Submodule.subset_span ⟨φ, hφ, rfl⟩
  set m := max m' n with hm
  have hmm : ∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, W' (g * u) = W' g := fun g u hu =>
    hV g u (hm' (GLnLocal.congruenceSubgroup_antitone F 2 (le_max_left m' n) hu))
  have hm1 : 1 ≤ m := hn1.trans (le_max_right _ _)
  obtain ⟨Φ, hΦ, c, hc, hW1, hW0⟩ := GlobalTheory.CompanionTheory.SmallSec.sec F ψ hψ W' m hm1 hmm
  obtain ⟨hs1, hs2⟩ := GlobalTheory.CompanionTheory.SmallSecSupp.support_and_value F ψ hψ W' (LFS.Wp ψ W' Φ) n m C c hn1 (le_max_right _ _)
    (GlobalTheory.CompanionTheory.WhittakerPsi.whittaker_upper_unipotent_equivariance ψ ν ν⁻¹ φ) hmm hc1 hc0 hW1 hW0
  refine ⟨LFS.Wp ψ W' Φ, Submodule.subset_span ⟨W', hW'mem, Φ, hΦ, rfl⟩,
    {u | u ∈ GLnLocal.congruenceSubgroup F 2 n ∧ u.val 1 0 ∈ valBall F (m : ℤ) ∧
      u.val 1 1 - 1 ∈ valBall F (m : ℤ)}, c * C, ?_, ?_, ?_, ?_, mul_ne_zero hc hC, ?_, ?_⟩
  · have h1 : IsOpen {u : GL (Fin 2) F | u.val 1 0 ∈ valBall F (m : ℤ)} :=
      (isOpen_valBall (m : ℤ)).preimage (GLnLocal.continuous_entry F 2 1 0)
    have h2 : IsOpen {u : GL (Fin 2) F | u.val 1 1 - 1 ∈ valBall F (m : ℤ)} :=
      (isOpen_valBall (m : ℤ)).preimage ((GLnLocal.continuous_entry F 2 1 1).sub continuous_const)
    exact (GLnLocal.isOpen_congruenceSubgroup F 2 n).inter (h1.inter h2)
  · refine ⟨one_mem _, ?_, ?_⟩ <;> simp
  · exact fun u hu => hn₀ (GLnLocal.congruenceSubgroup_antitone F 2 hn hu.1)
  · exact fun u hu => GLnLocal.congruenceSubgroup_le F 2 n hu.1
  · intro h hh
    obtain ⟨x, u, hu, rfl⟩ := hs1 h hh
    exact ⟨x, u, hu, rfl⟩
  · rintro x u ⟨h1, h2, h3⟩
    exact hs2 x u h1 h2 h3

end GlobalTheory.CompanionTheory.SmallSec
end
