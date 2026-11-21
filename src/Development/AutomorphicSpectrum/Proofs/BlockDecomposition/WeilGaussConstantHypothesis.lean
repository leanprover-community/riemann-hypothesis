import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHaarMeasureComapSubtype
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LanglandsConstant

section Tate

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem localLFactor_half_ne_zero {μ : Kˣ →* ℂˣ} (hμ : Continuous μ)
    (h1 : ‖((μ (unifUnit K) : ℂˣ) : ℂ)‖ = 1) : localLFactor μ (1 / 2) ≠ 0 := by
  apply localLFactor_ne_zero hμ
  have h0 : quasiCharExponent μ = 0 := by simp [quasiCharExponent, h1]
  rw [h0]
  norm_num

theorem gam_one_half (ψ : AddChar K Circle) : Ad3.gam ψ (1 : Kˣ →* ℂˣ) (1 / 2) = 1 := by
  have hu : IsUnramifiedChar (1 : Kˣ →* ℂˣ) := isUnramifiedChar_iff.2 fun _ _ => rfl
  have hL : localLFactor (1 : Kˣ →* ℂˣ) (1 / 2) ≠ 0 :=
    localLFactor_half_ne_zero continuous_const (by simp)
  have hs : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
  unfold Ad3.gam
  rw [localEpsilon_of_isUnramified hu, inv_one, hs, mul_div_assoc, div_self hL]
  simp

end Tate

end GlobalTheory.CompanionTheory.LanglandsConstant
end
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam.TestFn

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def coset (V : Set Fˣ) (a : Fˣ) : Set Fˣ := (fun u => a⁻¹ * u) ⁻¹' V

def ind (V : Set Fˣ) (a : Fˣ) : F → ℂ := (Units.val '' coset V a).indicator fun _ => 1

theorem isOpen_coset {V : Set Fˣ} (hV : IsOpen V) (a : Fˣ) : IsOpen (coset V a) :=
  hV.preimage (continuous_const.mul continuous_id)

theorem isCompact_coset {V : Set Fˣ} (hV : IsCompact V) (a : Fˣ) : IsCompact (coset V a) := by
  have : coset V a = (fun u => a * u) '' V := by
    ext u
    constructor
    · intro h
      exact ⟨a⁻¹ * u, h, by simp⟩
    · rintro ⟨v, hv, rfl⟩
      simpa [coset] using hv
  rw [this]
  exact hV.image (continuous_const.mul continuous_id)

theorem ind_mem {V : Set Fˣ} (ho : IsOpen V) (hc : IsCompact V) (a : Fˣ) :
    ind V a ∈ schwartzBruhat F := by
  have hO : IsOpen (Units.val '' coset V a) :=
    isOpenEmbedding_units_val.isOpenMap _ (isOpen_coset ho a)
  have hK : IsCompact (Units.val '' coset V a) :=
    (isCompact_coset hc a).image Units.continuous_val
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · by_cases hx : x ∈ Units.val '' coset V a
    · exact ⟨_, hO, hx, fun y hy => by
        simp only [ind, Set.indicator_of_mem hx, Set.indicator_of_mem hy]⟩
    · exact ⟨_, hK.isClosed.isOpen_compl, hx, fun y hy => by
        simp only [ind, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩
  exact HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _

theorem ind_zero (V : Set Fˣ) (a : Fˣ) : ind V a 0 = 0 := by
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨u, -, hu⟩
  exact u.ne_zero hu

theorem ind_unit_of_mem {V : Set Fˣ} {a u : Fˣ} (hu : u ∈ coset V a) : ind V a (u : F) = 1 :=
  Set.indicator_of_mem (Set.mem_image_of_mem _ hu) _

theorem ind_unit_of_notMem {V : Set Fˣ} {a u : Fˣ} (hu : u ∉ coset V a) : ind V a (u : F) = 0 := by
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨v, hv, hvu⟩
  exact hu (Units.ext hvu ▸ hv)

theorem integrand_ind {V : Subgroup Fˣ} (hV0 : V ≤ unitFiltrationUnits F 0) {χ : Fˣ →* ℂˣ}
    (hVχ : V ≤ χ.ker) (a : Fˣ) (s : ℂ) (u : Fˣ) :
    ind (V : Set Fˣ) a u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ s =
      (coset (V : Set Fˣ) a).indicator
        (fun _ => ((χ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ s) u := by
  by_cases hu : u ∈ coset (V : Set Fˣ) a
  · rw [ind_unit_of_mem hu, Set.indicator_of_mem hu, one_mul]
    have hw : a⁻¹ * u ∈ V := hu
    have e : u = a * (a⁻¹ * u) := by simp
    have hχ : χ u = χ a := by
      conv_lhs => rw [e]
      rw [map_mul, MonoidHom.mem_ker.mp (hVχ hw), mul_one]
    have hm1 : modulus (((a⁻¹ * u : Fˣ)) : F) = 1 :=
      modulus_eq_one_iff.2 ⟨Units.ne_zero _, mem_unitFiltrationUnits_zero_iff_ord.1 (hV0 hw)⟩
    have hm : modulus (u : F) = modulus (a : F) := by
      conv_lhs => rw [e, Units.val_mul, modulus_mul, hm1, mul_one]
    rw [hχ, hm]
  · rw [ind_unit_of_notMem hu, Set.indicator_of_notMem hu, zero_mul, zero_mul]

variable [MeasurableSpace F] [BorelSpace F]

theorem measure_coset (V : Set Fˣ) (a : Fˣ) : multHaar F (coset V a) = multHaar F V :=
  measure_preimage_mul (multHaar F) a⁻¹ V

theorem integrable_coset {V : Subgroup Fˣ} (ho : IsOpen (V : Set Fˣ)) (hc : IsCompact (V : Set Fˣ))
    (a : Fˣ) (c : ℂ) :
    Integrable ((coset (V : Set Fˣ) a).indicator fun _ => c) (multHaar F) := by
  refine (integrable_indicator_iff (isOpen_coset ho a).measurableSet).2 ?_
  exact integrableOn_const (isCompact_coset hc a).measure_lt_top.ne

theorem integral_coset {V : Subgroup Fˣ} (ho : IsOpen (V : Set Fˣ)) (a : Fˣ) (c : ℂ) :
    ∫ u, (coset (V : Set Fˣ) a).indicator (fun _ => c) u ∂multHaar F =
      ((multHaar F).real (V : Set Fˣ) : ℂ) * c := by
  rw [integral_indicator_const c (isOpen_coset ho a).measurableSet, measureReal_def,
    measureReal_def, measure_coset]
  simp

theorem zeta_test {V : Subgroup Fˣ} (ho : IsOpen (V : Set Fˣ)) (hc : IsCompact (V : Set Fˣ))
    (hV0 : V ≤ unitFiltrationUnits F 0) {χ : Fˣ →* ℂˣ} (hVχ : V ≤ χ.ker) (t : Fˣ) :
    localZeta (fun x => ind (V : Set Fˣ) 1 x -
        ((modulus (t : F) : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) * ind (V : Set Fˣ) t x) χ (1 / 2) =
      ((multHaar F).real (V : Set Fˣ) : ℂ) * (1 - ((χ t : ℂˣ) : ℂ)) := by
  have hm0 : ((modulus (t : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (modulus_ne_zero t.ne_zero)
  have hcc : ((modulus (t : F) : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) * ((modulus (t : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ)
      = 1 := by
    rw [← Complex.cpow_add _ _ hm0, neg_add_cancel, Complex.cpow_zero]
  set c := ((modulus (t : F) : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) with hc_def
  have e : ∀ u : Fˣ, (ind (V : Set Fˣ) 1 u - c * ind (V : Set Fˣ) t u) * ((χ u : ℂˣ) : ℂ) *
        ((modulus (u : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      (coset (V : Set Fˣ) 1).indicator (fun _ => (1 : ℂ)) u -
        (coset (V : Set Fˣ) t).indicator (fun _ => ((χ t : ℂˣ) : ℂ)) u := by
    intro u
    have h1 := integrand_ind hV0 hVχ 1 (1 / 2) u
    have h2 := integrand_ind hV0 hVχ t (1 / 2) u
    have e1 : (fun _ : Fˣ => (((χ 1 : ℂˣ) : ℂ)) * ((modulus ((1 : Fˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ))
        = fun _ => (1 : ℂ) := by
      funext _
      simp
    rw [e1] at h1
    have e2 : c * (coset (V : Set Fˣ) t).indicator
        (fun _ => ((χ t : ℂˣ) : ℂ) * ((modulus (t : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) u =
        (coset (V : Set Fˣ) t).indicator (fun _ => ((χ t : ℂˣ) : ℂ)) u := by
      by_cases hu : u ∈ coset (V : Set Fˣ) t
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, mul_left_comm, hcc, mul_one]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
    rw [← e2, ← h1, ← h2]
    ring
  rw [localZeta]
  simp only [e]
  rw [integral_sub (integrable_coset ho hc 1 1) (integrable_coset ho hc t _),
    integral_coset ho 1, integral_coset ho t]
  ring

end GlobalTheory.CompanionTheory.GaussLam.TestFn

open GlobalTheory.CompanionTheory.GaussLam.TestFn in

theorem GlobalTheory.CompanionTheory.GaussLam.TestFn.exists_test : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (η : Fˣ →* ℂˣ), Continuous η → ∀ t : Fˣ, η t = -1 → ∃ g : F → ℂ, g ∈ schwartzBruhat F ∧ g 0 = 0 ∧ localZeta g 1 (1 / 2) = 0 ∧ localZeta g η (1 / 2) ≠ 0 := by
  intro F _ _ _ _ _ _ η hη t ht
  obtain ⟨n, hn⟩ := exists_unitFiltrationUnits_le_ker hη
  have ho := isOpen_unitFiltrationUnits (K := F) n
  have hc := isCompact_unitFiltrationUnits (K := F) n
  have hV0 : unitFiltrationUnits F n ≤ unitFiltrationUnits F 0 :=
    unitFiltrationUnits_antitone (Nat.zero_le n)
  have hvol : (multHaar F).real (unitFiltrationUnits F n : Set Fˣ) ≠ 0 := by
    rw [measureReal_def]
    refine ENNReal.toReal_ne_zero.mpr ⟨?_, hc.measure_lt_top.ne⟩
    exact (ho.measure_pos _ ⟨1, one_mem _⟩).ne'
  refine ⟨_, ?_, ?_, (zeta_test ho hc hV0 (χ := 1) (fun _ _ => rfl) t).trans ?_,
    (zeta_test ho hc hV0 hn t).trans_ne ?_⟩
  · exact Submodule.sub_mem _ (ind_mem ho hc 1)
      (Submodule.smul_mem _ (((modulus (t : F) : ℝ) : ℂ) ^ (-(1 / 2) : ℂ)) (ind_mem ho hc t))
  · simp [ind_zero]
  · simp
  · rw [ht]
    have : ((multHaar F).real (unitFiltrationUnits F n : Set Fˣ) : ℂ) ≠ 0 := by
      exact_mod_cast hvol
    simp only [Units.val_neg, Units.val_one, sub_neg_eq_add]
    exact mul_ne_zero this (by norm_num)
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_zeta_separating_character : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (η : Fˣ →* ℂˣ), Continuous η → ∀ t : Fˣ, η t = -1 → ∃ g : F → ℂ, g ∈ schwartzBruhat F ∧ g 0 = 0 ∧ localZeta g 1 (1 / 2) = 0 ∧ localZeta g η (1 / 2) ≠ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GaussLam.TestFn.exists_test
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam.Til

open Topology

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem modulus_neg_eq (x : F) : modulus (-x) = modulus x := by
  have h : modulus (-1 : F) = 1 := by
    have h1 : modulus (-1 : F) * modulus (-1 : F) = 1 := by
      rw [← modulus_mul]; simp
    have h2 : modulus (-1 : F) ^ 2 = 1 := by rw [sq]; exact h1
    exact (pow_eq_one_iff.1 h2).resolve_right (by norm_num)
  rw [show -x = -1 * x by ring, modulus_mul, h, one_mul]

theorem eventually_modulus_eq {x : F} (hx : x ≠ 0) : ∀ᶠ y in 𝓝 x, modulus y = modulus x := by
  have hO : {z : F | z - x ∈ valBall F (ord x + 1)} ∈ 𝓝 x :=
    ((isOpen_valBall _).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  filter_upwards [hO] with y hy
  have := ord_add_eq hx hy
  rw [add_sub_cancel] at this
  rw [modulus_of_ne_zero this.1, modulus_of_ne_zero hx, this.2]

theorem eventually_eq_of_sign {η : Fˣ →* ℂˣ} (hc : Continuous η)
    (hs : ∀ a, ((η a : ℂˣ) : ℂ) = 1 ∨ ((η a : ℂˣ) : ℂ) = -1) (u : Fˣ) :
    ∀ᶠ v in 𝓝 u, η v = η u := by
  have hf : Continuous fun v : Fˣ => ((η v : ℂˣ) : ℂ) := Units.continuous_val.comp hc
  filter_upwards [(hf.tendsto u).eventually (Metric.ball_mem_nhds _ one_pos)] with v hv
  apply Units.ext
  have hv' : ‖((η v : ℂˣ) : ℂ) - ((η u : ℂˣ) : ℂ)‖ < 1 := by simpa [dist_eq_norm] using hv
  rcases hs v with h1 | h1 <;> rcases hs u with h2 | h2 <;> rw [h1, h2] at hv' <;> rw [h1, h2]
  · norm_num at hv'
  · norm_num at hv'

variable (E : Type) [CommRing E] [Algebra F E]

theorem gTil_zero (g : F → ℂ) : gTil E g (0 : F) = 0 := by
  simp [gTil]

theorem mem_of_gTil_ne_zero {g : F → ℂ} {N M : ℤ} (hN : ∀ h ∈ valBall F N, g h = 0)
    (hM : ∀ x, g x ≠ 0 → x ∈ valBall F M) {y : F} (hy : gTil E g y ≠ 0) :
    y ∈ valBall F (-N) ∧ y ∉ valBall F (1 - M) := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (gTil_zero E g)
  have hg : g (-y⁻¹) ≠ 0 := by
    intro h
    exact hy (by simp [gTil, h])
  have hi : y⁻¹ ≠ 0 := inv_ne_zero hy0
  have h1 : y⁻¹ ∉ valBall F N := fun h => hg (hN _ (neg_mem h))
  have h2 : y⁻¹ ∈ valBall F M := by
    have := neg_mem (hM _ hg)
    simpa using this
  rw [mem_valBall_iff_le_ord hi, ord_inv hy0] at h1 h2
  rw [mem_valBall_iff_le_ord hy0, mem_valBall_iff_le_ord hy0]
  omega

theorem gTil_mem {η : Fˣ →* ℂˣ} (hc : Continuous η)
    (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {g : F → ℂ} (hg : g ∈ schwartzBruhat F)
    (h0 : g 0 = 0) : gTil E g ∈ schwartzBruhat F := by
  obtain ⟨N, M, hN, hM⟩ := exists_invariant_of_mem_schwartzBruhat hg
  have hN' : ∀ h ∈ valBall F N, g h = 0 := fun h hh => by
    have := hN 0 h hh
    rwa [zero_add, h0] at this
  have hs : ∀ a, ((η a : ℂˣ) : ℂ) = 1 ∨ ((η a : ℂˣ) : ℂ) = -1 := fun a => by
    rw [hη, nsg]
    split_ifs <;> simp
  refine ⟨IsLocallyConstant.iff_eventually_eq _ |>.2 fun x => ?_, ?_⟩
  · by_cases hx : x = 0
    · subst hx
      have hO : (valBall F (1 - M) : Set F) ∈ 𝓝 (0 : F) :=
        (isOpen_valBall _).mem_nhds (zero_mem _)
      filter_upwards [hO] with y hy
      rw [gTil_zero]
      by_contra hne
      exact (mem_of_gTil_ne_zero E hN' hM hne).2 hy
    · have e1 : ∀ᶠ y in 𝓝 x, g (-y⁻¹) = g (-x⁻¹) := by
        have ht : Filter.Tendsto (fun y : F => -y⁻¹) (𝓝 x) (𝓝 (-x⁻¹)) :=
          (continuousAt_inv₀ hx).tendsto.neg
        exact ht.eventually ((IsLocallyConstant.iff_eventually_eq _).1 hg.1 _)
      have e2 : ∀ᶠ y in 𝓝 x, nsg E (-y) = nsg E (-x) := by
        let u : Fˣ := Units.mk0 x hx
        have hm : Filter.map (Units.val : Fˣ → F) (𝓝 u) = 𝓝 x :=
          (isOpenEmbedding_units_val (K := F)).map_nhds_eq u
        rw [← hm, Filter.eventually_map]
        filter_upwards [eventually_eq_of_sign hc hs u] with v hv
        have hneg : ∀ w : Fˣ, nsg E (-(w : F)) = ((η (-1) : ℂˣ) : ℂ) * ((η w : ℂˣ) : ℂ) := fun w => by
          rw [show -(w : F) = (((-1 : Fˣ) * w : Fˣ) : F) by simp, ← hη, map_mul, Units.val_mul]
        have hx' : x = (u : F) := rfl
        rw [hneg v, hx', hneg u, hv]
      filter_upwards [e1, e2, eventually_modulus_eq hx] with y h1 h2 h3
      simp only [gTil, h1, h2, h3]
  · refine HasCompactSupport.intro (isCompact_valBall (-N)) fun x hx => ?_
    by_contra hne
    exact hx (mem_of_gTil_ne_zero E hN' hM hne).1

theorem half_cpow {m : ℝ} (hm : 0 < m) :
    ∃ w : ℂ, w ≠ 0 ∧ ((m : ℂ)) ^ (1 / 2 : ℂ) = w ∧ ((m⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = w⁻¹ ∧
      (m : ℂ) = w * w := by
  have hne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨(m : ℂ) ^ (1 / 2 : ℂ), ?_, rfl, ?_, ?_⟩
  · simpa [Complex.cpow_eq_zero_iff] using hne
  · rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hm.le]; exact Real.pi_ne_zero.symm)]
  · rw [← Complex.cpow_add _ _ hne]
    norm_num

variable [MeasurableSpace F] [BorelSpace F]

theorem zeta_gTil {η : Fˣ →* ℂˣ} (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) (g : F → ℂ)
    (c : Fˣ →* ℂˣ) :
    localZeta (gTil E g) c (1 / 2) = ((c (-1) : ℂˣ) : ℂ) * localZeta g (η * c⁻¹) (1 / 2) := by
  haveI hlU : LocallyCompactSpace Fˣ := (isOpenEmbedding_units_val (K := F)).locallyCompactSpace
  haveI hsU : SecondCountableTopology Fˣ :=
    (isOpenEmbedding_units_val (K := F)).isEmbedding.secondCountableTopology
  haveI hI : (multHaar F).IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular _
  have hs : ∀ a, ((η a : ℂˣ) : ℂ) = 1 ∨ ((η a : ℂˣ) : ℂ) = -1 := fun a => by
    rw [hη, nsg]
    split_ifs <;> simp
  unfold localZeta
  rw [← integral_const_mul]
  set f : Fˣ → ℂ := fun u => gTil E g u * ((c u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ)
    with hf
  calc ∫ u, f u ∂multHaar F = ∫ u, f (-1 * u) ∂multHaar F :=
        (integral_mul_left_eq_self f (-1)).symm
    _ = ∫ u, f (-1 * u⁻¹) ∂multHaar F :=
        (integral_inv_eq_self (fun u => f (-1 * u)) (multHaar F)).symm
    _ = _ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      have hu : (((-1 : Fˣ) * v⁻¹ : Fˣ) : F) = -(v : F)⁻¹ := by simp
      have hm0 : 0 < ((modulus (v : F) : ℝ≥0) : ℝ) := by exact_mod_cast modulus_pos v.ne_zero
      obtain ⟨w, hw0, hw1, hw2, hw3⟩ := half_cpow hm0
      have hmod : ((modulus (-(v : F)⁻¹) : ℝ≥0) : ℝ) = ((modulus (v : F) : ℝ≥0) : ℝ)⁻¹ := by
        rw [modulus_neg_eq, modulus_inv, NNReal.coe_inv]
      have hn : nsg E (- -(v : F)⁻¹) = ((η v : ℂˣ) : ℂ) := by
        rw [neg_neg, ← Units.val_inv_eq_inv_val, ← hη, map_inv, Units.val_inv_eq_inv_val]
        rcases hs v with h | h <;> simp [h]
      have hg' : g (-(-(v : F)⁻¹)⁻¹) = g v := by simp
      have hcv : ((c v : ℂˣ) : ℂ) ≠ 0 := (c v).ne_zero
      simp only [hf, gTil, hu, hg', hn, hmod]
      rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hw2, MonoidHom.mul_apply,
        MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hw1]
      push_cast
      rw [inv_inv, hw3]
      field_simp

end GlobalTheory.CompanionTheory.GaussLam.Til

namespace GlobalTheory.CompanionTheory.GaussLam

theorem gTil_schwartzBruhat_zeta : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (η : Fˣ →* ℂˣ), Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → GlobalTheory.CompanionTheory.GaussLam.gTil E g ∈ schwartzBruhat F ∧ ∀ c : Fˣ →* ℂˣ, localZeta (GlobalTheory.CompanionTheory.GaussLam.gTil E g) c (1 / 2) = ((c (-1) : ℂˣ) : ℂ) * localZeta g (η * c⁻¹) (1 / 2) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ η hc hη g hg h0
  exact ⟨Til.gTil_mem E hc hη hg h0, fun c => Til.zeta_gTil E hη g c⟩

end GlobalTheory.CompanionTheory.GaussLam
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_character_norm_group : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (η : Fˣ →* ℂˣ), Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → GlobalTheory.CompanionTheory.GaussLam.gTil E g ∈ schwartzBruhat F ∧ ∀ c : Fˣ →* ℂˣ, localZeta (GlobalTheory.CompanionTheory.GaussLam.gTil E g) c (1 / 2) = ((c (-1) : ℂˣ) : ℂ) * localZeta g (η * c⁻¹) (1 / 2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GaussLam.gTil_schwartzBruhat_zeta
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam

section Subst

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem modulus_neg_eq (x : F) : modulus (-x) = modulus x := by
  have h1 : modulus (-1 : F) = 1 := by
    have h : modulus (-1 : F) * modulus (-1 : F) = 1 := by
      rw [← modulus_mul]; simp [modulus_one]
    have h2 : modulus (-1 : F) ^ 2 = 1 := by rw [sq]; exact h
    exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp h2
  rw [← neg_one_mul, modulus_mul, h1, one_mul]

variable [MeasurableSpace F] [BorelSpace F]

theorem integral_haar_neg_inv (f : F → ℂ) :
    ∫ x, f x ∂haarIntegers F =
      ∫ a, ((modulus a : ℝ))⁻¹ • ((modulus a : ℝ))⁻¹ • f (-a⁻¹) ∂haarIntegers F := by
  haveI : (multHaar F).IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular (multHaar F)
  have hC : (multHaarConst F).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨multHaarConst_ne_zero, multHaarConst_ne_top⟩
  have hres : (haarIntegers F).restrict ({0}ᶜ : Set F) = haarIntegers F :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr haarIntegers_singleton_zero)
  have h1 := integral_multHaar (K := F) (fun x => (modulus x : ℝ) • f x)
  have h2 := integral_multHaar (K := F) (fun x => ((modulus x : ℝ))⁻¹ • f (-x⁻¹))
  rw [hres] at h1 h2
  have h3 : ∫ u : Fˣ, (modulus (u : F) : ℝ) • f (u : F) ∂multHaar F =
      ∫ u : Fˣ, ((modulus (u : F) : ℝ))⁻¹ • f (-(u : F)⁻¹) ∂multHaar F := by
    have e1 := integral_inv_eq_self (fun u : Fˣ =>
      (modulus (((-1 : Fˣ) * u : Fˣ) : F) : ℝ) • f (((-1 : Fˣ) * u : Fˣ) : F)) (multHaar F)
    have e2 := integral_mul_left_eq_self (μ := multHaar F)
      (fun u : Fˣ => (modulus (u : F) : ℝ) • f (u : F)) (-1 : Fˣ)
    rw [← e2, ← e1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [modulus_neg_eq, modulus_inv]
  rw [h1, h2] at h3
  have h4 := smul_right_injective ℂ hC h3
  rw [← h4]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (haarIntegers_singleton_zero (K := F))] with x hx
  have hm : (modulus x : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero hx
  rw [smul_smul, inv_mul_cancel₀ hm, one_smul]

end Subst

end GlobalTheory.CompanionTheory.GaussLam

open GlobalTheory.CompanionTheory.GaussLam in

theorem GlobalTheory.CompanionTheory.GaussLam.localFourier_gTil : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → ∀ η : Fˣ →* ℂˣ, Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → ∀ t : F, localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) t = GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g t := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ _ η _ hη g _ _ t
  have hsq : ∀ a : F, a ≠ 0 → nsg E a⁻¹ = nsg E a := by
    intro a ha
    have h1 := hη (Units.mk0 a ha)
    have h2 := hη (Units.mk0 a ha)⁻¹
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, map_inv] at h1 h2
    rw [← h2, ← h1]
    have h3 : nsg E a = 1 ∨ nsg E a = -1 := by
      unfold nsg; split_ifs <;> simp
    rw [← h1] at h3
    rcases h3 with h3 | h3 <;> simp [h3]
  show ∫ x, gTil E g x * (χ (x * t) : ℂ) ∂selfDualMeasure χ = _
  rw [hAvg, selfDualMeasure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_haar_neg_inv]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  by_cases ha : a = 0
  · subst ha
    simp [modulus_zero]
  have hm : (modulus a : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero ha
  have e1 : -(-a⁻¹)⁻¹ = a := by simp
  have e2 : - -a⁻¹ = a⁻¹ := by simp
  have e3 : -a⁻¹ * t = -t / a := by field_simp
  simp only [gTil, e1, e2, e3, modulus_neg_eq, modulus_inv, hsq a ha, NNReal.coe_inv, inv_inv,
    Complex.real_smul]
  push_cast
  have hmc : ((modulus a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm
  field_simp
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_constant_quadratic_character : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → ∀ η : Fˣ →* ℂˣ, Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → ∀ t : F, localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) t = GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GaussLam.localFourier_gTil
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam

theorem localZeta_comp_norm_half (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E]
    [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (η : Fˣ →* ℂˣ) (hc : Continuous η)
    (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) (κ : ℝ) (hκ : FibProp F E κ) (f : F → ℂ)
    (hf : f ∈ schwartzBruhat F) :
    localZeta (fun x : E => f (Algebra.norm F x)) 1 (1 / 2) =
      (κ / 2 : ℂ) * (localZeta f 1 (1 / 2) + localZeta f η (1 / 2)) := by
  classical
  set h : Fˣ → ℂ := fun a => f a * (((1 : Fˣ →* ℂˣ) a : ℂˣ) : ℂ) *
    ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hh
  set g : E → ℂ := fun x => f (Algebra.norm F x) *
    ((modulus (Algebra.norm F x) : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hg
  have hgu : (fun x : Eˣ => g x) = h ∘ normUnits F E := by
    funext x
    simp [hh, hg, coe_normUnits]
  have hcont : Continuous (fun x : Eˣ => g x) := by
    rw [hgu]
    exact (continuous_localZeta_integrand hf continuous_one (1 / 2)).comp
      (continuous_normUnits F E)
  have hinv : ∀ (x : E) (u : Eˣ), Algebra.norm F (u : E) = 1 → g (x * u) = g x := by
    intro x u hu
    simp only [hg, map_mul, hu, mul_one]
  have hL : localZeta (fun x : E => f (Algebra.norm F x)) 1 (1 / 2) = ∫ x : Eˣ, g x ∂multHaar E := by
    unfold localZeta
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hg, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) (E := E)]
  have hfib : ∀ a : Fˣ, nfib E g a =
      (1 / 2 : ℂ) * (h a + f a * ((η a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
    intro a
    by_cases hr : ∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)
    · have e1 : nfib E g a = g (hr.choose : E) := dif_pos hr
      have e2 : ((η a : ℂˣ) : ℂ) = 1 := by rw [hη, nsg, if_pos hr]
      rw [e1, e2]
      simp only [hg, hh, hr.choose_spec]
      simp
      ring
    · have e1 : nfib E g a = 0 := dif_neg hr
      have e2 : ((η a : ℂˣ) : ℂ) = -1 := by rw [hη, nsg, if_neg hr]
      rw [e1, e2]
      simp only [hh]
      simp
  have hexp1 : quasiCharExponent (1 : Fˣ →* ℂˣ) = 0 := by
    simp [quasiCharExponent]
  have hexpη : quasiCharExponent η = 0 := by
    have : ‖((η (unifUnit F) : ℂˣ) : ℂ)‖ = 1 := by
      rw [hη, nsg]
      split_ifs <;> simp
    simp [quasiCharExponent, this]
  have hi1 := integrable_localZeta (s := 1 / 2) hf (continuous_one : Continuous (1 : Fˣ →* ℂˣ))
    (by rw [hexp1]; norm_num)
  have hi2 := integrable_localZeta (s := 1 / 2) hf hc (by rw [hexpη]; norm_num)
  rw [hL, (hκ g hcont hinv).2, integral_congr_ae (Filter.Eventually.of_forall hfib),
    integral_const_mul, integral_add hi1 hi2]
  unfold localZeta
  push_cast
  ring

end GlobalTheory.CompanionTheory.GaussLam
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_group_index_two : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (η : Fˣ →* ℂˣ), Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ κ : ℝ, FibProp F E κ → ∀ f : F → ℂ, f ∈ schwartzBruhat F → localZeta (fun x : E => f (Algebra.norm F x)) 1 (1 / 2) = (κ / 2 : ℂ) * (localZeta f 1 (1 / 2) + localZeta f η (1 / 2)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GaussLam.localZeta_comp_norm_half
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.NormSB

open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep

section Quadratic

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

theorem continuous_norm_quadratic : Continuous (fun x : E => Algebra.norm F x) := by
  haveI := GroundTheory.LocalField.isModuleTopology F E
  obtain ⟨c, hc⟩ := Algebra.trace_surjective F E 1
  have e : (fun x : E => Algebra.norm F x) =
      fun x => Algebra.trace F E (c * (x * conj F E x)) := by
    funext x
    rw [← algebraMap_norm_eq_mul_conj, mul_comm c, ← Algebra.smul_def, map_smul, hc, smul_eq_mul,
      mul_one]
  rw [e]
  exact (IsModuleTopology.continuous_of_linearMap (Algebra.trace F E)).comp
    (continuous_const.mul (continuous_id.mul continuous_conj))

theorem residueDegree_pos_quadratic : 0 < residueDegree F E := by
  rcases Nat.eq_zero_or_pos (residueDegree F E) with h | h
  · have h1 := residueCard_eq_pow (K := F) (E := E)
    rw [h, pow_zero] at h1
    have h2 := one_lt_residueCard (K := E)
    omega
  · exact h

theorem mem_valBall_of_norm_mem {M : ℤ} {x : E} (h : Algebra.norm F x ∈ valBall F M) :
    x ∈ valBall E (-|M|) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_mem _
  have hN : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx
  rw [mem_valBall_iff_le_ord hN, ord_norm (K := F) (L := E)] at h
  rw [mem_valBall_iff_le_ord hx]
  have hd : (1 : ℤ) ≤ (residueDegree F E : ℤ) := by
    exact_mod_cast residueDegree_pos_quadratic F E
  by_contra hlt
  push_neg at hlt
  have hM1 : -|M| ≤ M := neg_abs_le M
  have hM0 : -|M| ≤ 0 := by simp
  nlinarith

end Quadratic

end GlobalTheory.CompanionTheory.NormSB

theorem GlobalTheory.CompanionTheory.NormSB.comp_norm_mem_schwartzBruhat :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (f : F → ℂ), f ∈ schwartzBruhat F → (fun x : E => f (Algebra.norm F x)) ∈ schwartzBruhat E := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ f hf
  obtain ⟨-, M, -, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  refine mem_schwartzBruhat.2 ⟨hf.1.comp_continuous (GlobalTheory.CompanionTheory.NormSB.continuous_norm_quadratic F E),
    HasCompactSupport.intro (isCompact_valBall (-|M|)) fun x hx => ?_⟩
  by_contra hne
  exact hx (GlobalTheory.CompanionTheory.NormSB.mem_valBall_of_norm_mem F E (hM _ hne))
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_norm_form_pullback : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (f : F → ℂ), f ∈ schwartzBruhat F → (fun x : E => f (Algebra.norm F x)) ∈ schwartzBruhat E := by
  atlas_forward_decl GlobalTheory.CompanionTheory.NormSB.comp_norm_mem_schwartzBruhat
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

namespace GlobalTheory.CompanionTheory.GaussLam

theorem continuous_norm_quadExt : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (Algebra.norm F : E → F) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _
  exact GroundTheory.LocalField.continuous_algebraNorm F E

end GlobalTheory.CompanionTheory.GaussLam
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_algebra_norm : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (Algebra.norm F : E → F) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GaussLam.continuous_norm_quadExt
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam.Left

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

theorem continuous_gal (τ : E ≃ₐ[F] E) : Continuous τ := by
  rcases GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.eq_one_or_eq_conj τ with rfl | rfl
  · exact continuous_id
  · exact GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.continuous_conj

theorem comp_norm_mem {f : F → ℂ} (hf : f ∈ schwartzBruhat F) :
    (fun x : E => f (Algebra.norm F x)) ∈ schwartzBruhat E := by
  obtain ⟨N, M, -, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  refine ⟨hf.1.comp_continuous (continuous_algebraNorm F E), ?_⟩
  refine HasCompactSupport.intro (isCompact_valBall (min M 0)) fun x hx => ?_
  by_contra h0
  apply hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (zero_mem _)
  have hN0 : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx0
  have h1 := (mem_valBall_iff_le_ord hN0).1 (hM _ h0)
  rw [ord_norm (K := F) (L := E)] at h1
  have hd : (1 : ℤ) ≤ residueDegree F E := by exact_mod_cast residueDegree_pos F E
  show x ∈ valBall E (min M 0)
  rw [mem_valBall_iff_le_ord hx0]
  by_contra hlt
  push_neg at hlt
  have h2 : ord x < 0 := lt_of_lt_of_le hlt (min_le_right _ _)
  have h3 : ord x < M := lt_of_lt_of_le hlt (min_le_left _ _)
  nlinarith

theorem fts_mem [MeasurableSpace E] [BorelSpace E] {ψ : AddChar E Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (μ : Measure E) [μ.IsAddHaarMeasure] (σ : E ≃ₐ[F] E) {Φ : E → ℂ} (hΦ : Φ ∈ schwartzBruhat E) :
    (fun u => localFourier μ ψ Φ (σ u)) ∈ schwartzBruhat E := by
  have h := localFourier_mem_schwartzBruhat μ hψ hψ1 hΦ
  let e : E ≃ₜ E := ⟨σ.toEquiv, continuous_gal σ, continuous_gal σ.symm⟩
  exact ⟨h.1.comp_continuous e.continuous, h.2.comp_homeomorph e⟩

theorem real_apply_eq_actE_real_inv_mul [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
    (χ : AddChar F Circle) (hχ : Continuous χ) (hχ1 : χ ≠ 1) (σ : E ≃ₐ[F] E) {Φ : E → ℂ}
    (hΦ : Φ ∈ SBE E) {g : F → ℂ} (hg : g ∈ schwartzBruhat F) :
    ∫ a, g a * ∫ u, (χ (a * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ ∂selfDualMeasure χ =
      ∫ z, Φ z * localFourier (muE E χ) (chE E χ)
        (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) (σ.symm z) ∂muE E χ := by
  have hχE : Continuous (chE E χ) := continuous_traceChar hχ hχ1
  have hχE1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
  have hΦ' : Φ ∈ schwartzBruhat E := hΦ
  have hc : Continuous fun x : F => (χ x : ℂ) := continuous_subtype_val.comp hχ
  have hcE : Continuous fun x : E => (chE E χ x : ℂ) := continuous_subtype_val.comp hχE
  have hN : Continuous (Algebra.norm F : E → F) := continuous_algebraNorm F E
  obtain ⟨T, hT⟩ : ∃ T, T = FTE E χ σ Φ := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : E → ℂ, Ψ = fun x => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x) :=
    ⟨_, rfl⟩
  rw [← hT, ← hΨ]
  have hTu : ∀ u, T u = ∫ z, Φ z * (chE E χ (σ u * z) : ℂ) ∂muE E χ := fun u => by rw [hT]; rfl
  have hTe : T = fun u => localFourier (muE E χ) (chE E χ) Φ (σ u) := by
    funext u
    rw [hTu, localFourier]
    simp only [mul_comm (σ u)]
  have hTsb : T ∈ schwartzBruhat E := hTe ▸ fts_mem hχE hχE1 _ σ hΦ'
  have hΨsb : Ψ ∈ schwartzBruhat E :=
    hΨ ▸ comp_norm_mem (localFourier_mem_schwartzBruhat _ hχ hχ1 hg)
  have hgi := integrable_of_mem_schwartzBruhat (selfDualMeasure χ) hg
  have hTi := integrable_of_mem_schwartzBruhat (muE E χ) hTsb
  have hΦi := integrable_of_mem_schwartzBruhat (muE E χ) hΦ'
  have hΨi := integrable_of_mem_schwartzBruhat (muE E χ) hΨsb
  have s1 : ∫ a, g a * ∫ u, (χ (a * Algebra.norm F u) : ℂ) * T u ∂muE E χ ∂selfDualMeasure χ =
      ∫ u, T u * Ψ u ∂muE E χ := by
    let G : F → E → ℂ := fun a u => g a * ((χ (a * Algebra.norm F u) : ℂ) * T u)
    have hG : Integrable (Function.uncurry G) ((selfDualMeasure χ).prod (muE E χ)) := by
      have hdom := hgi.norm.mul_prod hTi.norm
      refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
      · refine Continuous.aestronglyMeasurable ?_
        exact (hg.1.continuous.comp continuous_fst).mul
          ((hc.comp (continuous_fst.mul (hN.comp continuous_snd))).mul
            (hTsb.1.continuous.comp continuous_snd))
      · simp [G, Function.uncurry, Circle.norm_coe]
    calc ∫ a, g a * ∫ u, (χ (a * Algebra.norm F u) : ℂ) * T u ∂muE E χ ∂selfDualMeasure χ
        = ∫ a, ∫ u, G a u ∂muE E χ ∂selfDualMeasure χ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
          exact (integral_const_mul _ _).symm
      _ = ∫ u, ∫ a, G a u ∂selfDualMeasure χ ∂muE E χ := integral_integral_swap hG
      _ = ∫ u, T u * Ψ u ∂muE E χ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          show ∫ a, G a u ∂selfDualMeasure χ = T u * Ψ u
          rw [hΨ]
          show _ = T u * ∫ a, g a * (χ (a * Algebra.norm F u) : ℂ) ∂selfDualMeasure χ
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
          show g a * ((χ (a * Algebra.norm F u) : ℂ) * T u) = _
          ring
  have s2 : ∫ u, T u * Ψ u ∂muE E χ =
      ∫ z, Φ z * localFourier (muE E χ) (chE E χ) Ψ (σ.symm z) ∂muE E χ := by
    let H : E → E → ℂ := fun u z => Φ z * (chE E χ (σ u * z) : ℂ) * Ψ u
    have hH : Integrable (Function.uncurry H) ((muE E χ).prod (muE E χ)) := by
      have hdom := hΨi.norm.mul_prod hΦi.norm
      refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
      · refine Continuous.aestronglyMeasurable ?_
        exact ((hΦ'.1.continuous.comp continuous_snd).mul
          (hcE.comp (((continuous_gal σ).comp continuous_fst).mul continuous_snd))).mul
            (hΨsb.1.continuous.comp continuous_fst)
      · simp [H, Function.uncurry, Circle.norm_coe, mul_comm]
    calc ∫ u, T u * Ψ u ∂muE E χ = ∫ u, ∫ z, H u z ∂muE E χ ∂muE E χ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          show T u * Ψ u = ∫ z, Φ z * (chE E χ (σ u * z) : ℂ) * Ψ u ∂muE E χ
          rw [integral_mul_const, hTu]
      _ = ∫ z, ∫ u, H u z ∂muE E χ ∂muE E χ := integral_integral_swap hH
      _ = ∫ z, Φ z * localFourier (muE E χ) (chE E χ) Ψ (σ.symm z) ∂muE E χ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          show ∫ u, H u z ∂muE E χ = Φ z * ∫ u, Ψ u * (chE E χ (u * σ.symm z) : ℂ) ∂muE E χ
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          have e : chE E χ (σ u * z) = chE E χ (u * σ.symm z) := by
            show χ (Algebra.trace F E (σ u * z)) = χ (Algebra.trace F E (u * σ.symm z))
            have e1 : σ (u * σ.symm z) = σ u * z := by rw [map_mul, AlgEquiv.apply_symm_apply]
            rw [← e1, Algebra.trace_eq_of_algEquiv]
          show Φ z * (chE E χ (σ u * z) : ℂ) * Ψ u = _
          rw [e]
          ring
  exact s1.trans s2

theorem left_average : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, ∀ Φ ∈ SBE E, ∀ g : F → ℂ, g ∈ schwartzBruhat F → ∫ a, g a * ∫ u, (χ (a * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ ∂selfDualMeasure χ = ∫ z, Φ z * localFourier (muE E χ) (chE E χ) (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) (σ.symm z) ∂muE E χ := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 σ Φ hΦ g hg
  exact real_apply_eq_actE_real_inv_mul χ hχ hχ1 σ hΦ hg

end GlobalTheory.CompanionTheory.GaussLam.Left
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_gauss_constant_square : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, ∀ Φ ∈ SBE E, ∀ g : F → ℂ, g ∈ schwartzBruhat F → ∫ a, g a * ∫ u, (χ (a * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ ∂selfDualMeasure χ = ∫ z, Φ z * localFourier (muE E χ) (chE E χ) (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) (σ.symm z) ∂muE E χ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GaussLam.Left.left_average
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
open Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam.Right

section Norm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

omit [ValuativeRel E] in

theorem mem_valBall_of_modulus_lt {d : F} {n : ℤ} (h : modulus d < (residueCard F : ℝ≥0) ^ (-n)) :
    d ∈ valBall F n := by
  by_cases h0 : d = 0
  · subst h0; exact zero_mem _
  rw [mem_valBall_iff_le_ord h0]
  rw [modulus_of_ne_zero h0] at h
  have := (zpow_lt_zpow_iff_right₀ one_lt_residueCard_nnreal).1 h
  omega

variable (F) in

theorem continuous_normE : Continuous (fun z : E => Algebra.norm F z) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc : Continuous (fun z : E => z * GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E z
      - x * GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E x) :=
    (continuous_id.mul GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.continuous_conj).sub continuous_const
  have hm := (continuous_modulus (K := E)).comp hc
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, hasBasis_nhds_zero_valBall.tendsto_right_iff]
  intro n _
  have hq : (0 : ℝ≥0) < (residueCard F : ℝ≥0) ^ (-n) :=
    zpow_pos (zero_lt_one.trans one_lt_residueCard_nnreal) _
  have ht : Tendsto (fun z : E => modulus (z * GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E z
      - x * GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E x)) (𝓝 x) (𝓝 0) := by
    simpa [Function.comp_def] using hm.tendsto x
  have hev := ht.eventually (gt_mem_nhds (pow_pos hq 2))
  filter_upwards [hev] with z hz
  refine mem_valBall_of_modulus_lt ?_
  have hz' : modulus (algebraMap F E (Algebra.norm F z - Algebra.norm F x)) <
      ((residueCard F : ℝ≥0) ^ (-n)) ^ 2 := by
    rw [map_sub, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.algebraMap_norm_eq_mul_conj,
      GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.algebraMap_norm_eq_mul_conj]
    exact hz
  rw [GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_algebraMap] at hz'
  exact lt_of_pow_lt_pow_left₀ 2 zero_le hz'

end Norm

def kern (E : Type) [Field E] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Algebra F E] (χ : AddChar F Circle) (g : F → ℂ) (Φ : E → ℂ)
    (p : F × E) : ℂ :=
  g p.1 * nsg E p.1 * (((modulus p.1 : ℝ)⁻¹ : ℝ) : ℂ) *
    ((χ (-(Algebra.norm F p.2) / p.1) : ℂ) * Φ p.2)

section Kernel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

theorem continuousAt_nsg {η : Fˣ →* ℂˣ} (hηc : Continuous η)
    (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {a : F} (ha : a ≠ 0) :
    ContinuousAt (nsg E : F → ℂ) a := by
  have hcomp : Continuous ((nsg E : F → ℂ) ∘ (Units.val : Fˣ → F)) := by
    have : ((nsg E : F → ℂ) ∘ (Units.val : Fˣ → F)) = fun u => ((η u : ℂˣ) : ℂ) := by
      funext u; exact (hη u).symm
    rw [this]
    exact Units.continuous_val.comp hηc
  have hoe : IsOpenEmbedding (Units.val : Fˣ → F) := by
    refine ⟨Units.isEmbedding_val₀, ?_⟩
    have hr : Set.range (Units.val : Fˣ → F) = {0}ᶜ := by
      ext x
      constructor
      · rintro ⟨u, rfl⟩
        exact u.ne_zero
      · intro h
        exact ⟨Units.mk0 x h, rfl⟩
    rw [hr]
    exact isOpen_compl_singleton
  have := hoe.continuousAt_iff (g := (nsg E : F → ℂ)) (x := Units.mk0 a ha)
  simpa using this.1 hcomp.continuousAt

theorem continuous_kern {χ : AddChar F Circle} (hχ : Continuous χ) {η : Fˣ →* ℂˣ}
    (hηc : Continuous η) (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {Φ : E → ℂ}
    (hΦ : Continuous Φ) {g : F → ℂ} (hg : IsLocallyConstant g) (hg0 : g 0 = 0) :
    Continuous (kern E χ g Φ) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a, z⟩
  by_cases ha : a = 0
  · subst ha
    have hopen : {b : F | g b = 0} ∈ 𝓝 (0 : F) :=
      (hg.isOpen_fiber 0).mem_nhds hg0
    have hev : kern E χ g Φ =ᶠ[𝓝 ((0 : F), z)] fun _ => 0 := by
      have := continuous_fst.continuousAt (x := ((0 : F), z)) hopen
      filter_upwards [this] with p hp
      have hp' : g p.1 = 0 := hp
      simp [kern, hp']
    exact (continuousAt_const (y := (0 : ℂ))).congr hev.symm
  · have h1 : ContinuousAt (fun p : F × E => g p.1) (a, z) :=
      (hg.continuous.comp continuous_fst).continuousAt
    have h2 : ContinuousAt (fun p : F × E => nsg E p.1) (a, z) :=
      ContinuousAt.comp (f := Prod.fst) (g := (nsg E : F → ℂ)) (continuousAt_nsg hηc hη ha)
        continuous_fst.continuousAt
    have h3 : ContinuousAt (fun p : F × E => (((modulus p.1 : ℝ)⁻¹ : ℝ) : ℂ)) (a, z) := by
      have hm : Continuous (fun p : F × E => ((modulus p.1 : ℝ≥0) : ℝ)) :=
        NNReal.continuous_coe.comp (continuous_modulus.comp continuous_fst)
      have hne : ((modulus a : ℝ≥0) : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero ha
      exact Complex.continuous_ofReal.continuousAt.comp (hm.continuousAt.inv₀ hne)
    have h4 : ContinuousAt (fun p : F × E => -(Algebra.norm F p.2) / p.1) (a, z) :=
      (((continuous_normE F).comp continuous_snd).neg.continuousAt).div
        continuous_fst.continuousAt ha
    have h5 : ContinuousAt (fun p : F × E => (χ (-(Algebra.norm F p.2) / p.1) : ℂ)) (a, z) :=
      ContinuousAt.comp (g := fun x : F => (χ x : ℂ))
        (continuous_subtype_val.comp hχ).continuousAt h4
    have h6 : ContinuousAt (fun p : F × E => Φ p.2) (a, z) :=
      (hΦ.comp continuous_snd).continuousAt
    exact ((h1.mul h2).mul h3).mul (h5.mul h6)

theorem hasCompactSupport_kern {χ : AddChar F Circle} {Φ : E → ℂ} (hΦ : HasCompactSupport Φ)
    {g : F → ℂ} (hg : HasCompactSupport g) : HasCompactSupport (kern E χ g Φ) := by
  refine HasCompactSupport.intro (hg.isCompact.prod hΦ.isCompact) ?_
  rintro ⟨a, z⟩ hp
  simp only [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · simp [kern, image_eq_zero_of_notMem_tsupport h]
  · simp [kern, image_eq_zero_of_notMem_tsupport h]

end Kernel

theorem avg_fubini : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ η : Fˣ →* ℂˣ, Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ Φ ∈ SBE E, ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → ∫ a, g a * (nsg E a * (((modulus a : ℝ)⁻¹ : ℝ) : ℂ) * ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) ∂selfDualMeasure χ = ∫ z, Φ z * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) ∂muE E χ := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 η hηc hη Φ hΦ g hg hg0
  have hint : Integrable (kern E χ g Φ) ((selfDualMeasure χ).prod (muE E χ)) :=
    (continuous_kern hχ hηc hη hΦ.1.continuous hg.1 hg0).integrable_of_hasCompactSupport
      (hasCompactSupport_kern hΦ.2 hg.2)
  have hsw := integral_integral_swap (f := fun a z => kern E χ g Φ (a, z)) hint
  have hL : ∀ a : F, g a * (nsg E a * (((modulus a : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) =
      ∫ z, kern E χ g Φ (a, z) ∂muE E χ := by
    intro a
    simp only [kern]
    rw [integral_const_mul]
    ring
  have hR : ∀ z : E, Φ z * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) =
      ∫ a, kern E χ g Φ (a, z) ∂selfDualMeasure χ := by
    intro z
    rw [GlobalTheory.CompanionTheory.GaussLam.hAvg, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [kern]
    ring
  simp only [hL, hR]
  exact hsw

end GlobalTheory.CompanionTheory.GaussLam.Right
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_gauss_constant_norm_one : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ η : Fˣ →* ℂˣ, Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ Φ ∈ SBE E, ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → ∫ a, g a * (nsg E a * (((modulus a : ℝ)⁻¹ : ℝ) : ℂ) * ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) ∂selfDualMeasure χ = ∫ z, Φ z * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) ∂muE E χ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GaussLam.Right.avg_fubini
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SBSep

theorem eq_of_integral_SBE_eq (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsAddHaarMeasure] (P Q : K → ℂ) (hP : Continuous P) (hQ : Continuous Q)
    (h : ∀ Φ ∈ SBE K, ∫ z, Φ z * P z ∂μ = ∫ z, Φ z * Q z ∂μ) : P = Q := by
  by_contra hne
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hne
  set D : K → ℂ := fun z => P z - Q z with hDdef
  have hDc : Continuous D := hP.sub hQ
  have hD0 : D z₀ ≠ 0 := sub_ne_zero.2 hz₀
  have hn : 0 < ‖D z₀‖ := norm_pos_iff.2 hD0
  have hW : {x : K | ‖D (z₀ + x) - D z₀‖ < ‖D z₀‖ / 2} ∩ (valBall K 0 : Set K) ∈ 𝓝 (0 : K) := by
    refine Filter.inter_mem ?_ (valBall_mem_nhds 0)
    have hc : Continuous fun x : K => ‖D (z₀ + x) - D z₀‖ := by fun_prop
    refine (isOpen_lt hc continuous_const).mem_nhds ?_
    simpa using half_pos hn
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hW
  let B : Set K := (fun z => z - z₀) ⁻¹' (V : Set K)
  have hBo : IsOpen B := V.isOpen.preimage (by fun_prop)
  have hBcl : IsClosed B := V.isClosed.preimage (by fun_prop)
  have hVc : IsCompact (V : Set K) :=
    (isCompact_valBall 0).of_isClosed_subset V.isClosed (fun x hx => (hV hx).2)
  have hBc : IsCompact B := (Homeomorph.subRight z₀).isCompact_preimage.2 hVc
  have hB0 : z₀ ∈ B := by
    change z₀ - z₀ ∈ (V : Set K)
    rw [sub_self]
    exact zero_mem V
  have hBm : MeasurableSet B := hBo.measurableSet
  have hμ : 0 < μ B := hBo.measure_pos μ ⟨z₀, hB0⟩
  have hμt : μ B < ⊤ := hBc.measure_lt_top
  let Φ : K → ℂ := B.indicator fun _ => 1
  have hΦ : Φ ∈ SBE K :=
    ⟨(LocallyConstant.indicator (LocallyConstant.const K (1 : ℂ)) ⟨hBcl, hBo⟩).isLocallyConstant,
      HasCompactSupport.intro hBc fun x hx => Set.indicator_of_notMem hx _⟩
  have hI : ∀ R : K → ℂ, ∫ z, Φ z * R z ∂μ = ∫ z in B, R z ∂μ := by
    intro R
    rw [← integral_indicator hBm]
    congr 1
    ext z
    by_cases hz : z ∈ B <;> simp [Φ, hz]
  have hPB : IntegrableOn P B μ := hP.continuousOn.integrableOn_compact hBc
  have hQB : IntegrableOn Q B μ := hQ.continuousOn.integrableOn_compact hBc
  have hDB : IntegrableOn D B μ := hDc.continuousOn.integrableOn_compact hBc
  have h0 : ∫ z in B, D z ∂μ = 0 := by
    have h1 := h Φ hΦ
    rw [hI, hI] at h1
    rw [hDdef, integral_sub hPB hQB, h1, sub_self]
  have hconst : ∫ z in B, (D z - D z₀) ∂μ = -(μ.real B • D z₀) := by
    rw [integral_sub hDB (integrableOn_const hμt.ne), h0, setIntegral_const, zero_sub]
  have hle : ‖∫ z in B, (D z - D z₀) ∂μ‖ ≤ (‖D z₀‖ / 2) * μ.real B := by
    refine norm_setIntegral_le_of_norm_le_const hμt fun z hz => ?_
    have h2 := (hV (show z - z₀ ∈ (V : Set K) from hz)).1
    have h3 : ‖D (z₀ + (z - z₀)) - D z₀‖ < ‖D z₀‖ / 2 := h2
    rw [add_sub_cancel] at h3
    exact h3.le
  have hpos : 0 < μ.real B := ENNReal.toReal_pos hμ.ne' hμt.ne
  rw [hconst, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le] at hle
  nlinarith [mul_pos hpos hn]

end GlobalTheory.CompanionTheory.SBSep
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_eq_of_schwartz_pairing : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] (P Q : K → ℂ), Continuous P → Continuous Q → (∀ Φ ∈ SBE K, ∫ z, Φ z * P z ∂μ = ∫ z, Φ z * Q z ∂μ) → P = Q := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SBSep.eq_of_integral_SBE_eq
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section
namespace GlobalTheory.CompanionTheory.GaussLam

theorem ptw : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ η : Fˣ →* ℂˣ, Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ γ : ℂ, (∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ = γ * nsg E (a : F) * (((modulus (a : F) : ℝ)⁻¹ : ℝ) : ℂ) * ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) → ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → ∀ w : E, localFourier (muE E χ) (chE E χ) (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) w = γ * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F w) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 σ hσ η hcη hη γ hγ g hg g0 w
  have hcE : Continuous (chE E χ) := GroundTheory.LocalField.continuous_traceChar hχ hχ1
  have hnE : chE E χ ≠ 1 := GroundTheory.LocalField.traceChar_ne_one hχ hχ1
  have hf := localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hg
  have hΨ := GlobalTheory.T.schwartz_norm_form_pullback F E _ hf
  have hFΨ := localFourier_mem_schwartzBruhat (muE E χ) hcE hnE hΨ
  have hσ1 : σ = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E := by
    rcases GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.eq_one_or_eq_conj σ with h | h
    · exact absurd h hσ
    · exact h
  have hσc : Continuous σ.symm := by
    have : (σ.symm : E → E) = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E := by
      funext x
      apply σ.injective
      rw [AlgEquiv.apply_symm_apply, hσ1, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj_conj]
    rw [this]
    exact GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.continuous_conj
  have hgt := (GlobalTheory.T.quadratic_character_norm_group F E η hcη hη g hg g0).1
  have hh : Continuous (GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g) := by
    have e : GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g = localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) :=
      funext fun t => (GlobalTheory.T.weil_constant_quadratic_character F E χ hχ η hcη hη g hg g0 t).symm
    rw [e]
    exact (localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hgt).1.continuous
  have hP := hFΨ.1.continuous.comp hσc
  have hQ : Continuous fun z : E => γ * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) :=
    continuous_const.mul (hh.comp (GlobalTheory.T.continuous_algebra_norm F E))
  have key := GlobalTheory.T.continuous_eq_of_schwartz_pairing E (muE E χ) _ _ hP hQ (fun Φ hΦ => by
    simp only [Function.comp_apply]
    rw [← GlobalTheory.T.weil_gauss_constant_square F E χ hχ hχ1 σ Φ hΦ g hg]
    have e2 : ∫ z, Φ z * (γ * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z)) ∂muE E χ =
        γ * ∫ z, Φ z * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) ∂muE E χ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only
      ring
    rw [e2, ← GlobalTheory.T.weil_gauss_constant_norm_one F E χ hχ hχ1 η hcη hη Φ hΦ g hg g0, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    by_cases ha : a = 0
    · subst ha
      simp [g0]
    · have := hγ (Units.mk0 a ha) Φ hΦ
      simp only [Units.val_mk0] at this
      rw [this]
      ring)
  have h1 := congrFun key (σ w)
  simp only [Function.comp_apply, AlgEquiv.symm_apply_apply] at h1
  rw [h1, Algebra.norm_eq_of_algEquiv]

theorem zeta_fe {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K] {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {μ : Kˣ →* ℂˣ} (hμ : IsUnit1 μ) {f : K → ℂ} (hf : f ∈ schwartzBruhat K) :
    localZeta (localFourier (selfDualMeasure ψ) ψ f) μ⁻¹ (1 / 2) = gam ψ μ (1 / 2) * localZeta f μ (1 / 2) := by
  have he : quasiCharExponent μ = 0 := by simp [quasiCharExponent, hμ.2]
  have hs1 : -quasiCharExponent μ < ((1 / 2 : ℂ)).re := by rw [he]; norm_num
  have hs2 : ((1 / 2 : ℂ)).re < 1 - quasiCharExponent μ := by rw [he]; norm_num
  have hs' : -quasiCharExponent μ⁻¹ < ((1 : ℂ) - 1 / 2).re := by
    rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]
    linarith
  have hL1 := localLFactor_ne_zero hμ.1 hs1
  have hL2 := localLFactor_ne_zero (continuous_quasiChar_inv hμ.1) hs'
  have hfe := localZeta_functionalEquation hψ hψ1 hμ.1 hf hs1 hs2
  have h12 : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
  unfold gam
  rw [h12] at hfe hL2 ⊢
  field_simp at hfe ⊢
  linear_combination hfe

theorem isUnit1_one {K : Type} [Field K] [TopologicalSpace K] : IsUnit1 (1 : Kˣ →* ℂˣ) :=
  ⟨continuous_const, fun x => by simp⟩

theorem wGaussLam : Ad3.K.GL2LocalData.WGaussLam := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη γ hγ
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.NormModulus.valuativeExtension_of_continuous hc
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hd
  haveI : Fact (Module.finrank F E = 2) := ⟨hd⟩
  haveI : Algebra.IsSeparable F E := inferInstance
  have hex : ∀ a : Fˣ, (∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)) ↔
      a ∈ (normUnits F E).range := by
    refine fun a => ⟨fun ⟨t, ht⟩ => ⟨t, Units.ext ((coe_normUnits t).trans ht)⟩, ?_⟩
    rintro ⟨t, rfl⟩
    exact ⟨t, (coe_normUnits t).symm⟩
  have hq : η = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar F E := by
    ext a
    rw [hη a]
    unfold Ad3.K.GL2LocalData.nsg
    by_cases ha : a ∈ (normUnits F E).range
    · rw [if_pos ((hex a).2 ha), GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ha, Units.val_one]
    · rw [if_neg (fun h => ha ((hex a).1 h)), GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_notMem ha]
      simp
  have hcη : Continuous η := by
    refine continuous_of_continuousAt_one η ?_
    have hker : IsOpen (η.ker : Set Fˣ) := by
      rw [hq]
      exact GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.isOpen_ker_quadChar
    have hev : (fun _ : Fˣ => (1 : ℂˣ)) =ᶠ[nhds 1] η := by
      filter_upwards [hker.mem_nhds (one_mem η.ker)] with x hx
      exact (MonoidHom.mem_ker.1 hx).symm
    have h0 : ContinuousAt (fun _ : Fˣ => (1 : ℂˣ)) 1 := continuousAt_const
    exact h0.congr hev
  have hu : IsUnit1 η := ⟨hcη, fun a => by
    rw [hη]
    unfold Ad3.K.GL2LocalData.nsg
    split_ifs <;> simp⟩
  obtain ⟨t, ht⟩ : ∃ t : Fˣ, η t = -1 := by
    by_contra hno
    apply GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_ne_one (K := F) (E := E)
    ext a
    by_cases ha : a ∈ (normUnits F E).range
    · rw [GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ha]; simp
    · exact absurd ⟨a, by rw [hq, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_notMem ha]⟩ hno
  have hcE : Continuous (chE E χ) := GroundTheory.LocalField.continuous_traceChar hχ hχ1
  have hnE : chE E χ ≠ 1 := GroundTheory.LocalField.traceChar_ne_one hχ hχ1
  obtain ⟨κ, hκ, hfib⟩ := GlobalTheory.CompanionTheory.NormFib.wFib F χ hχ hχ1 E hd hc σ hσ η hη
  obtain ⟨g, hg, g0, hA, hB⟩ := GlobalTheory.T.exists_schwartz_zeta_separating_character F η hcη t ht
  obtain ⟨hgt, hZ⟩ := GlobalTheory.T.quadratic_character_norm_group F E η hcη hη g hg g0
  have hf := localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hg
  have hft := localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hgt

  have hpt := ptw F E χ hχ hχ1 σ hσ η hcη hη γ hγ g hg g0
  have hΨ := GlobalTheory.T.schwartz_norm_form_pullback F E _ hf

  have hE := zeta_fe hcE hnE (isUnit1_one (K := E)) hΨ
  rw [inv_one, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul] at hE
  have hfun : localFourier (selfDualMeasure (chE E χ)) (chE E χ)
      (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) =
      fun w => γ * localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F w) := by
    funext w
    rw [GlobalTheory.T.weil_constant_quadratic_character F E χ hχ η hcη hη g hg g0]
    exact hpt w
  rw [hfun] at hE
  have hscal : localZeta (fun w : E => γ * localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F w)) 1 (1 / 2) =
      γ * localZeta (fun w : E => localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F w)) 1 (1 / 2) := by
    unfold localZeta
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [mul_assoc]
  rw [hscal, GlobalTheory.T.norm_group_index_two F E η hcη hη κ hfib _ hf, GlobalTheory.T.norm_group_index_two F E η hcη hη κ hfib _ hft] at hE
  have e1 := zeta_fe hχ hχ1 (isUnit1_one (K := F)) hg
  have e2 := zeta_fe hχ hχ1 hu hg
  have e3 := zeta_fe hχ hχ1 (isUnit1_one (K := F)) hgt
  have e4 := zeta_fe hχ hχ1 hu hgt
  have hinv : η⁻¹ = η := by
    ext a
    have h2 := GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_sq (K := F) (E := E) a
    rw [← hq] at h2
    have : (η a)⁻¹ = η a := by
      rw [inv_eq_iff_mul_eq_one, ← sq, h2]
    simp [this]
  rw [inv_one, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul] at e1 e3
  rw [hinv] at e2 e4
  have z1 := hZ 1
  have z2 := hZ η
  simp only [inv_one, mul_one, mul_inv_cancel, map_one, MonoidHom.one_apply, Units.val_one, one_mul] at z1 z2
  rw [e1, e2, e3, e4, z1, z2, hA] at hE
  have hκ' : ((κ : ℂ) / 2) ≠ 0 := by
    have : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    exact div_ne_zero this two_ne_zero
  unfold lamE
  rw [GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul, div_one]
  have : ((κ : ℂ) / 2 * localZeta g η (1 / 2)) * (γ - gam χ η (1 / 2)) = 0 := by
    linear_combination hE
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (mul_ne_zero hκ' hB)
  · exact sub_eq_zero.1 h

end GlobalTheory.CompanionTheory.GaussLam
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_gauss_constant_hypothesis : Ad3.K.GL2LocalData.WGaussLam := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GaussLam.wGaussLam
end
