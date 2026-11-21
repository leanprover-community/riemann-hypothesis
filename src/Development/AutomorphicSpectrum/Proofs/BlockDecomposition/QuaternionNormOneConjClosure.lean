import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionNeighbourhood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import GroundTheory.AutomorphicForms.HermitianNormLocal
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitNormFormAtOddPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRegularDenseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegralStatement
import GroundTheory.AutomorphicForms.HermitianBinaryValues
import GroundTheory.AutomorphicForms.Anisotropic

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_quaternion_neighbourhood : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (a : Q d β (AF F)), ∀ V ∈ 𝓝 a,
  ∃ T : Finset (Pl F), ∃ U : (u : Pl F) → Set (Q d β (Kp u)),
    (∀ u, U u ∈ 𝓝 (qmap (proj u) a)) ∧ (∀ w : InfinitePlace F, (Sum.inl w : Pl F) ∈ T) ∧
    ∀ b : Q d β (AF F), (∀ u ∈ T, qmap (proj u) b ∈ U u) →
      (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → IntQ v (qmap (proj (Sum.inr v)) b)) → b ∈ V := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.Box.basic_nhd | exact GlobalTheory.CompanionTheory.PlaneSA.Box.basic_nhd | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.Box.basic_nhd <;> assumption)
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem exists_isotropic_of_sq_sub_mul_sq {F K : Type} [Field F] [Field K] [Algebra F K] {d β : F} {x y : K}
    (h : x ^ 2 - algebraMap F K d * y ^ 2 = algebraMap F K β) :
    ∃ q : Q d β K, qn q = 0 ∧ q ≠ 0 := by
  refine ⟨⟨x, y, 1, 0⟩, ?_, fun hq => ?_⟩
  · simp only [qn]
    rw [← h]
    ring
  · exact one_ne_zero (congrArg QuaternionAlgebra.imJ hq : (1 : K) = 0)

theorem finite_anisotropic_places {F : Type} [Field F] [NumberField F] (d β : F)
    (hd : ∀ r : F, r ^ 2 ≠ d) (hβ : β ≠ 0) :
    {u : Pl F | ∀ x : Q d β (Kp u), qn x = 0 → x = 0}.Finite := by
  have hB := GroundTheory.Automorphic.eventually_exists_sq_sub_mul_sq hd hβ
  rw [Filter.eventually_cofinite] at hB
  refine ((Set.finite_univ (α := InfinitePlace F)).image Sum.inl |>.union (hB.image Sum.inr)).subset ?_
  rintro (w | v) hu
  · exact Or.inl ⟨w, Set.mem_univ _, rfl⟩
  · refine Or.inr ⟨v, ?_, rfl⟩
    rintro ⟨x, y, hxy⟩
    obtain ⟨q, hq0, hq⟩ := exists_isotropic_of_sq_sub_mul_sq (F := F) (K := Kp (Sum.inr v : Pl F))
      (d := d) (β := β) (x := x) (y := y) hxy
    exact hq (hu q hq0)

end GlobalTheory.CompanionTheory.PlaneSA
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_ramified_places_finite : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ r : F, r ^ 2 ≠ d) → β ≠ 0 →
  {u : Pl F | ∀ x : Q d β (Kp u), qn x = 0 → x = 0}.Finite := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.finite_anisotropic_places
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem eventually_valued_eq_one {F : Type} [Field F] [NumberField F] {x : F} (hx : x ≠ 0) :
    ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)),
      Valued.v (algebraMap F (v.adicCompletion F) x) = 1 := by
  refine Filter.eventually_cofinite.2 (((HeightOneSpectrum.Support.finite (𝓞 F) x).union
    (HeightOneSpectrum.Support.finite (𝓞 F) x⁻¹)).subset fun v hv => ?_)
  by_contra hc
  simp only [HeightOneSpectrum.Support, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, map_inv₀] at hc
  have h0 : 0 < v.valuation F x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx)
  have h1 : v.valuation F x = 1 := le_antisymm hc.1 ((inv_le_one₀ h0).1 hc.2)
  exact hv ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans h1)

theorem norm_one_coords {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {d β x y : K} (hd : d ≠ 0) (hβ : β ≠ 0)
    (hxy : β = x ^ 2 - d * y ^ 2) (t : K) :
    let m := ((t * 2⁻¹) ^ 2 - 1) * d⁻¹
    let r := (1 + m) * 2⁻¹
    let c := (m - 1) * 2⁻¹
    (t * 2⁻¹) ^ 2 - d * r ^ 2 - β * (-(c * y * d * β⁻¹)) ^ 2 + d * β * (c * x * β⁻¹) ^ 2 = 1 := by
  intro m r c
  have hm : d * m = (t * 2⁻¹) ^ 2 - 1 := by simp only [m]; field_simp
  have e : - β * (-(c * y * d * β⁻¹)) ^ 2 + d * β * (c * x * β⁻¹) ^ 2 = c ^ 2 * d := by
    have : - β * (-(c * y * d * β⁻¹)) ^ 2 + d * β * (c * x * β⁻¹) ^ 2
        = c ^ 2 * d * (x ^ 2 - d * y ^ 2) * β⁻¹ := by field_simp; ring
    rw [this, ← hxy]; field_simp
  have e2 : d * r ^ 2 - c ^ 2 * d = d * m := by
    simp only [r, c]; field_simp; ring
  linear_combination e - e2 - hm

theorem exists_integral_coords {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {D B t : v.adicCompletion F} (h2 : Valued.v (2 : v.adicCompletion F) = 1) (hD : Valued.v D = 1)
    (hB : Valued.v B = 1) (ht : t ∈ v.adicCompletionIntegers F) :
    ∃ a₀ ∈ v.adicCompletionIntegers F, ∃ a₁ ∈ v.adicCompletionIntegers F,
      ∃ a₂ ∈ v.adicCompletionIntegers F, ∃ a₃ ∈ v.adicCompletionIntegers F,
        2 * a₀ = t ∧ a₀ ^ 2 - D * a₁ ^ 2 - B * a₂ ^ 2 + D * B * a₃ ^ 2 = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit F v D B h2 hD hB
  have ne0 : ∀ {z : v.adicCompletion F}, Valued.v z = 1 → z ≠ 0 := fun hz h0 => by
    rw [h0, map_zero] at hz; exact zero_ne_one hz
  have inv_mem : ∀ {z : v.adicCompletion F}, Valued.v z = 1 → z⁻¹ ∈ v.adicCompletionIntegers F :=
    fun hz => by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hz, inv_one]
  have hDm : D ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hD]
  have hi2 := inv_mem h2
  have hk := norm_one_coords (ne0 h2) (ne0 hD) (ne0 hB) hxy t
  have h0 : t * 2⁻¹ ∈ v.adicCompletionIntegers F := mul_mem ht hi2
  have hm : ((t * 2⁻¹) ^ 2 - 1) * D⁻¹ ∈ v.adicCompletionIntegers F :=
    mul_mem (sub_mem (pow_mem h0 2) (one_mem _)) (inv_mem hD)
  have hc := mul_mem (sub_mem hm (one_mem _)) hi2
  exact ⟨_, h0, _, mul_mem (add_mem (one_mem _) hm) hi2, _,
    neg_mem (mul_mem (mul_mem (mul_mem hc hy) hDm) (inv_mem hB)), _,
    mul_mem (mul_mem hc hx) (inv_mem hB), by rw [mul_comm t, ← mul_assoc,
      mul_inv_cancel₀ (ne0 h2), one_mul], hk⟩

theorem exists_integral_norm_one_trace :
    ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 →
      ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)), ∀ t ∈ Ov v,
        ∃ b : Q d β (Kp (Sum.inr v : Pl F)), qn b = 1 ∧ 2 * b.re = t ∧ IntQ v b := by
  intro F _ _ d β hd hβ
  filter_upwards [eventually_valued_eq_one hd, eventually_valued_eq_one hβ,
    eventually_valued_eq_one (two_ne_zero : (2 : F) ≠ 0)] with v hdv hβv h2v t ht
  rw [map_ofNat] at h2v
  obtain ⟨a₀, h₀, a₁, h₁, a₂, h₂, a₃, h₃, htr, hn⟩ := exists_integral_coords v h2v hdv hβv ht
  exact ⟨⟨a₀, a₁, a₂, a₃⟩, hn, htr, h₀, h₁, h₂, h₃⟩

end GlobalTheory.CompanionTheory.PlaneSA
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_integral_trace_almost_all : ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 →
  ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)), ∀ t ∈ Ov v,
    ∃ b : Q d β (Kp (Sum.inr v : Pl F)), qn b = 1 ∧ 2 * b.re = t ∧ IntQ v b := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.exists_integral_norm_one_trace
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem re_normOne_open_of_sq_ne_one {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] (d β : F)
    (a : Q d β K) (ha : qn a = 1) (hp : a.re ^ 2 ≠ 1)
    (hsq : ∀ V ∈ 𝓝 (1 : K), ∀ᶠ x in 𝓝 (1 : K), ∃ μ ∈ V, μ ^ 2 = x) :
    ∀ U ∈ 𝓝 a, ∀ᶠ r in 𝓝 a.re, ∃ b ∈ U, qn b = 1 ∧ b.re = r := by
  intro U hU
  have hc : 1 - a.re ^ 2 ≠ 0 := fun h => hp (sub_eq_zero.1 h).symm
  let g : K × K → Q d β K := fun z => ⟨z.1, z.2 * a.imI, z.2 * a.imJ, z.2 * a.imK⟩
  have hg : Continuous g := by
    rw [continuous_q_iff]
    refine ⟨continuous_fst, ?_, ?_, ?_⟩ <;> exact continuous_snd.mul continuous_const
  have hg1 : g (a.re, 1) = a := by
    ext <;> simp [g]
  have hpre : g ⁻¹' U ∈ 𝓝 ((a.re, 1) : K × K) :=
    hg.continuousAt.preimage_mem_nhds (by rwa [hg1])
  obtain ⟨A, hA, V, hV, hAV⟩ := mem_nhds_prod_iff.1 hpre
  have hx : Filter.Tendsto (fun r : K => (1 - r ^ 2) / (1 - a.re ^ 2)) (𝓝 a.re) (𝓝 1) := by
    have hcont : Continuous fun r : K => (1 - r ^ 2) / (1 - a.re ^ 2) := by
      simp only [div_eq_mul_inv]
      exact (continuous_const.sub (continuous_id.pow 2)).mul continuous_const
    have := hcont.tendsto a.re
    simpa [div_self hc] using this
  filter_upwards [hA, hx.eventually (hsq V hV)] with r hrA hr
  obtain ⟨μ, hμV, hμ⟩ := hr
  refine ⟨g (r, μ), hAV (Set.mk_mem_prod hrA hμV), ?_, rfl⟩
  have hy : algebraMap F K d * a.imI ^ 2 + algebraMap F K β * a.imJ ^ 2
      - algebraMap F K d * algebraMap F K β * a.imK ^ 2 = a.re ^ 2 - 1 := by
    have : qn a = 1 := ha
    simp only [qn] at this
    linear_combination -this
  have hμ' : μ ^ 2 * (1 - a.re ^ 2) = 1 - r ^ 2 := by
    rw [hμ]; field_simp
  simp only [qn, g]
  linear_combination -(μ ^ 2) * hy + hμ'

end GlobalTheory.CompanionTheory.PlaneSA
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_trace_open : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalDivisionRing K] (d β : F)
  (a : Q d β K), qn a = 1 → a.re ^ 2 ≠ 1 →
  (∀ V ∈ 𝓝 (1 : K), ∀ᶠ x in 𝓝 (1 : K), ∃ μ ∈ V, μ ^ 2 = x) →
  ∀ U ∈ 𝓝 a, ∀ᶠ r in 𝓝 a.re, ∃ b ∈ U, qn b = 1 ∧ b.re = r := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.re_normOne_open_of_sq_ne_one
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem map_sq_nhds_one_of_normed {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) : Filter.map (fun x : K => x ^ 2) (𝓝 1) = 𝓝 1 := by
  have hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1 := by
    simpa using hasStrictDerivAt_pow 2 (1 : K)
  simpa using hd.map_nhds_eq h2

theorem sq_fills_of_map {K : Type*} [Monoid K] [TopologicalSpace K]
    (h : Filter.map (fun x : K => x ^ 2) (𝓝 1) = 𝓝 1) (V : Set K) (hV : V ∈ 𝓝 (1 : K)) :
    ∀ᶠ x in 𝓝 (1 : K), ∃ μ ∈ V, μ ^ 2 = x := by
  have : (fun x : K => x ^ 2) '' V ∈ 𝓝 (1 : K) := by
    rw [← h]; exact Filter.image_mem_map hV
  filter_upwards [this] with x hx
  obtain ⟨μ, hμ, rfl⟩ := hx
  exact ⟨μ, hμ, rfl⟩

theorem sq_fills_nhds_one {F : Type} [Field F] [NumberField F] (u : Pl F) :
    ∀ V ∈ 𝓝 (1 : Kp u), ∀ᶠ x in 𝓝 (1 : Kp u), ∃ μ ∈ V, μ ^ 2 = x := by
  intro V hV
  cases u with
  | inl w =>
    have h2 : (2 : w.Completion) ≠ 0 := by
      have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F w.Completion).injective
      exact two_ne_zero
    have hn : ‖(2 : w.Completion)‖ ≠ 1 := by
      have e : ‖(2 : w.Completion)‖ = ‖InfinitePlace.Completion.extensionEmbedding w 2‖ :=
        ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) 2).symm
      rw [e, map_ofNat]
      norm_num
    letI : NontriviallyNormedField w.Completion :=
      NontriviallyNormedField.ofNormNeOne ⟨2, h2, hn⟩
    exact sq_fills_of_map (K := w.Completion) (map_sq_nhds_one_of_normed h2) V hV
  | inr v =>
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    have h2 : (2 : v.adicCompletion F) ≠ 0 := by
      have : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
      exact two_ne_zero
    exact sq_fills_of_map (K := v.adicCompletion F) (map_sq_nhds_one_of_normed h2) V hV

end GlobalTheory.CompanionTheory.PlaneSA
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_square_roots_near_one : ∀ {F : Type} [Field F] [NumberField F] (u : Pl F), ∀ V ∈ 𝓝 (1 : Kp u), ∀ᶠ x in 𝓝 (1 : Kp u), ∃ μ ∈ V, μ ^ 2 = x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.sq_fills_nhds_one
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem anis_trace_sq_sub_four_ne_sq :
    ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 →
      (∀ x : Q d β K, qn x = 0 → x = 0) → ∀ b : Q d β K, qn b = 1 → b.re ^ 2 ≠ 1 →
      ∀ r : K, r ^ 2 ≠ (2 * b.re) ^ 2 - 4 := by
  intro F K _ _ _ d β h2 han b hb hre r hr
  have hz : qn (⟨r, 2 * b.imI, 2 * b.imJ, 2 * b.imK⟩ : Q d β K) = 0 := by
    simp only [qn] at hb ⊢
    linear_combination hr + 4 * hb
  have h0 := han _ hz
  have hI : b.imI = 0 := by
    have := congrArg QuaternionAlgebra.imI h0
    simpa [h2] using this
  have hJ : b.imJ = 0 := by
    have := congrArg QuaternionAlgebra.imJ h0
    simpa [h2] using this
  have hK : b.imK = 0 := by
    have := congrArg QuaternionAlgebra.imK h0
    simpa [h2] using this
  apply hre
  simpa [qn, hI, hJ, hK] using hb

end GlobalTheory.CompanionTheory.PlaneSA
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_anisotropic_trace : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 →
  (∀ x : Q d β K, qn x = 0 → x = 0) → ∀ b : Q d β K, qn b = 1 → b.re ^ 2 ≠ 1 →
  ∀ r : K, r ^ 2 ≠ (2 * b.re) ^ 2 - 4 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.anis_trace_sq_sub_four_ne_sq
end

section
section
set_option maxSynthPendingDepth 1

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open GroundTheory.Automorphic GroundTheory.Global
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.GlobalTrace

theorem eq_zero_of_not_sqNorm {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {d β : K} (hd0 : d ≠ 0)
    (h : ¬ SqNorm d β) {a b c e : K}
    (hz : (a ^ 2 - d * b ^ 2) - β * (c ^ 2 - d * e ^ 2) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  have hd : ∀ r : K, r ^ 2 ≠ d := by
    intro r hr
    have hr0 : r ≠ 0 := by rintro rfl; exact hd0 (by rw [← hr]; ring)
    exact h (sqNorm_of_eq_sq h2 hr.symm hr0 β)
  have hN : ∀ x y : K, x ^ 2 - d * y ^ 2 = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    have hy : y = 0 := by
      by_contra hy
      refine hd (x / y) ?_
      field_simp
      linear_combination hxy
    subst hy
    refine ⟨?_, rfl⟩
    have : x ^ 2 = 0 := by linear_combination hxy
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  by_cases hn : c ^ 2 - d * e ^ 2 = 0
  · obtain ⟨rfl, rfl⟩ := hN c e hn
    obtain ⟨rfl, rfl⟩ := hN a b (by linear_combination hz)
    exact ⟨rfl, rfl, rfl, rfl⟩
  · exfalso
    apply h
    have hA : SqNorm d (a ^ 2 - d * b ^ 2) := ⟨a, b, rfl⟩
    have hB : SqNorm d (c ^ 2 - d * e ^ 2) := ⟨c, e, rfl⟩
    have := hA.mul hB.inv
    have he : (a ^ 2 - d * b ^ 2) * (c ^ 2 - d * e ^ 2)⁻¹ = β := by
      field_simp
      linear_combination hz
    rwa [he] at this

theorem aniso_of_not_sqNorm {F : Type} [Field F] [CharZero F] {K : Type} [Field K] [Algebra F K]
    {d β : F} (hd0 : d ≠ 0) (h : ¬ SqNorm (algebraMap F K d) (algebraMap F K β)) :
    ∀ x : Q d β K, qn x = 0 → x = 0 := by
  have h2 : (2 : K) ≠ 0 := by
    have : algebraMap F K 2 ≠ 0 := (map_ne_zero _).2 two_ne_zero
    rwa [map_ofNat] at this
  intro x hx
  obtain ⟨h1, h3, h4, h5⟩ := eq_zero_of_not_sqNorm h2 ((map_ne_zero (algebraMap F K)).2 hd0) h
    (a := x.re) (b := x.imI) (c := x.imJ) (e := x.imK) (by unfold qn at hx; linear_combination hx)
  ext <;> simp [h1, h3, h4, h5]

theorem exists_qn_of_quadraticAlgebra {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {d β t : K}
    (hβ : ¬ SqNorm d β) {x y : QuadraticAlgebra K (-1) t}
    (hxy : x ^ 2 - algebraMap K _ d * y ^ 2 = algebraMap K _ β) :
    ∃ q : Q d β K, qn q = 1 ∧ 2 * q.re = t := by
  have hre := congrArg QuadraticAlgebra.re hxy
  have him := congrArg QuadraticAlgebra.im hxy
  simp only [sq, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
    at hre him
  set x0 := x.re
  set x1 := x.im
  set y0 := y.re
  set y1 := y.im
  have hn : x1 ^ 2 - d * y1 ^ 2 ≠ 0 := by
    intro hn
    exact hβ ⟨x0, y0, by linear_combination hre + hn⟩
  set n := x1 ^ 2 - d * y1 ^ 2 with hndef
  refine ⟨⟨-(x0 * x1 - d * y0 * y1) / n, -(y0 * x1 - x0 * y1) / n, x1 / n, -y1 / n⟩, ?_, ?_⟩
  · simp only [qn, Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
    rw [hndef]
    linear_combination (x1 ^ 2 - d * y1 ^ 2) * hre
  · simp only
    field_simp
    rw [hndef]
    linear_combination -him

theorem exists_qn_eq_one_two_mul_re {F : Type} [Field F] [NumberField F] (d β t : F)
    (hF : ∀ x : Q d β F, qn x = 0 → x = 0)
    (hl : ∀ u : Pl F, (∀ x : Q d β (Kp u), qn x = 0 → x = 0) →
      ∀ r : Kp u, r ^ 2 ≠ algebraMap F (Kp u) (t ^ 2 - 4)) :
    ∃ x : Q d β F, qn x = 1 ∧ 2 * x.re = t := by
  have key : ∀ a b c e : F, a ^ 2 - d * b ^ 2 - β * c ^ 2 + d * β * e ^ 2 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
    intro a b c e h
    have := hF ⟨a, b, c, e⟩ (by simpa [qn] using h)
    exact ⟨congrArg QuaternionAlgebra.re this, congrArg QuaternionAlgebra.imI this,
      congrArg QuaternionAlgebra.imJ this, congrArg QuaternionAlgebra.imK this⟩
  have hd0 : d ≠ 0 := fun h => one_ne_zero (key 0 1 0 0 (by simp [h])).2.1
  have hβ0 : β ≠ 0 := fun h => one_ne_zero (key 0 0 1 0 (by simp [h])).2.2.1
  have hd : ∀ r : F, r ^ 2 ≠ d := fun r h =>
    one_ne_zero (key r 1 0 0 (by rw [← h]; ring)).2.1
  have hβd : ¬ SqNorm d β := by
    rintro ⟨a, b, h⟩
    exact one_ne_zero (key a b 1 0 (by rw [← h]; ring)).2.2.1
  have ht1 : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ SqNorm (algebraMap F (v.adicCompletion F) d) (algebraMap F _ β) →
      ∀ r : v.adicCompletion F, r ^ 2 ≠ algebraMap F _ (t ^ 2 - 4 * 1) := by
    intro v hv r
    rw [mul_one]
    exact hl (Sum.inr v) (aniso_of_not_sqNorm (K := Kp (Sum.inr v : Pl F)) hd0 hv) r
  have ht2 : ∀ w : InfinitePlace F,
      ¬ SqNorm (algebraMap F w.Completion d) (algebraMap F _ β) →
      ∀ r : w.Completion, r ^ 2 ≠ algebraMap F _ (t ^ 2 - 4 * 1) := by
    intro w hw r
    rw [mul_one]
    exact hl (Sum.inl w) (aniso_of_not_sqNorm (K := Kp (Sum.inl w : Pl F)) hd0 hw) r
  have hbad : (∃ v : HeightOneSpectrum (𝓞 F),
        ¬ SqNorm (algebraMap F (v.adicCompletion F) d) (algebraMap F _ β)) ∨
      ∃ w : InfinitePlace F, ¬ SqNorm (algebraMap F w.Completion d) (algebraMap F _ β) := by
    by_contra H
    push Not at H
    exact hβd ((exists_sq_sub_mul_sq_iff_forall_local hd hβ0).2 ⟨H.1, H.2⟩)
  have hnsq : ∀ r : F, r ^ 2 ≠ t ^ 2 - 4 * 1 := by
    intro r hr
    rcases hbad with ⟨v, hv⟩ | ⟨w, hw⟩
    · exact ht1 v hv (algebraMap F _ r) (by rw [← map_pow, hr])
    · exact ht2 w hw (algebraMap F _ r) (by rw [← map_pow, hr])
  have hL : Fact (∀ r : F, r ^ 2 ≠ -1 + t * r) :=
    ⟨fun r hr => hnsq (2 * r - t) (by linear_combination 4 * hr)⟩
  have hex : ∃ x y : QuadraticAlgebra F (-1) t,
      x ^ 2 - algebraMap F _ d * y ^ 2 = algebraMap F _ β := by
    by_cases hdL : ∃ r : QuadraticAlgebra F (-1) t, r ^ 2 = algebraMap F _ d
    · obtain ⟨r, hr⟩ := hdL
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact (map_ne_zero (algebraMap F (QuadraticAlgebra F (-1) t))).2 hd0 (by rw [← hr]; ring)
      exact sqNorm_of_eq_sq two_ne_zero hr.symm hr0 _
    push Not at hdL
    have hβL : algebraMap F (QuadraticAlgebra F (-1) t) β ≠ 0 := (map_ne_zero _).2 hβ0
    refine (exists_sq_sub_mul_sq_iff_forall_local hdL hβL).2 ⟨fun w => ?_, fun w => ?_⟩
    · refine sqNorm_finite_quadraticAlgebra (γ := 1) hd0 hβ0 w ?_
      exact (Classical.em _).imp_right (ht1 _)
    · refine sqNorm_infinite_quadraticAlgebra (γ := 1) hd0 hβ0 w ?_
      exact (Classical.em _).imp_right (ht2 _)
  obtain ⟨x, y, hxy⟩ := hex
  exact exists_qn_of_quadraticAlgebra two_ne_zero hβd hxy

end GlobalTheory.CompanionTheory.PlaneSA.GlobalTrace
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasse_principle_norm_trace : ∀ {F : Type} [Field F] [NumberField F] (d β t : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  (∀ u : Pl F, (∀ x : Q d β (Kp u), qn x = 0 → x = 0) →
    ∀ r : Kp u, r ^ 2 ≠ algebraMap F (Kp u) (t ^ 2 - 4)) →
  ∃ x : Q d β F, qn x = 1 ∧ 2 * x.re = t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.GlobalTrace.exists_qn_eq_one_two_mul_re
end

section
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.ConjQ

section Coord

variable {F K : Type} [Field F] [Field K] [Algebra F K] {d β : F}

theorem isUnit_of_qn_ne_zero {y : Q d β K} (h : qn y ≠ 0) : IsUnit y := by
  refine isUnit_iff_exists.2 ⟨(qn y)⁻¹ • star y, ?_, ?_⟩
  · rw [mul_smul_comm, mul_star_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h, map_one]
  · rw [smul_mul_assoc, star_mul_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h, map_one]

def pureAdd (x b : Q d β K) : Q d β K := ⟨0, x.imI + b.imI, x.imJ + b.imJ, x.imK + b.imK⟩

def pureSub (x b : Q d β K) : Q d β K := ⟨0, x.imI - b.imI, x.imJ - b.imJ, x.imK - b.imK⟩

theorem pureAdd_mul (x b : Q d β K) (hre : x.re = b.re) (hq : qn x = qn b) :
    pureAdd x b * x = b * pureAdd x b := by
  unfold qn at hq
  rw [hre] at hq
  ext <;> simp only [pureAdd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, hre]
  · linear_combination -hq
  · ring
  · ring
  · ring

theorem pureSub_mul (x b : Q d β K) (hre : x.re = b.re) (hq : qn x = qn b) :
    pureSub x b * x = star b * pureSub x b := by
  unfold qn at hq
  rw [hre] at hq
  ext <;> simp only [pureSub, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, hre]
  · linear_combination -hq
  · ring
  · ring
  · ring

theorem qn_add_sub (x b : Q d β K) :
    qn (pureAdd x b) + qn (pureSub x b) = 2 * (qn x - x.re ^ 2) + 2 * (qn b - b.re ^ 2) := by
  simp only [qn, pureAdd, pureSub]
  ring

theorem mul_star_of_orth (z b : Q d β K) (hz : z.re = 0)
    (ho : algebraMap F K d * z.imI * b.imI + algebraMap F K β * z.imJ * b.imJ -
      algebraMap F K d * algebraMap F K β * z.imK * b.imK = 0) :
    z * star b = b * z := by
  ext <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, hz]
  · linear_combination -2 * ho
  · ring
  · ring
  · ring

theorem exists_orth (h2 : (2 : K) ≠ 0) (hd : algebraMap F K d ≠ 0) (hβ : algebraMap F K β ≠ 0)
    (b : Q d β K) (hb : qn b - b.re ^ 2 ≠ 0) :
    ∃ z : Q d β K, z.re = 0 ∧ qn z ≠ 0 ∧
      algebraMap F K d * z.imI * b.imI + algebraMap F K β * z.imJ * b.imJ -
        algebraMap F K d * algebraMap F K β * z.imK * b.imK = 0 := by
  set a := algebraMap F K d with ha
  set c := algebraMap F K β with hc
  by_cases hA : a * b.imI ^ 2 + c * b.imJ ^ 2 = 0
  · by_cases hB : b.imI ^ 2 - c * b.imK ^ 2 = 0
    · by_cases hC : b.imJ ^ 2 - a * b.imK ^ 2 = 0
      · exfalso
        have hk : 2 * (a * c * b.imK ^ 2) = 0 := by
          linear_combination hA - a * hB - c * hC
        have hk2 : a * c * b.imK ^ 2 = 0 := (mul_eq_zero.1 hk).resolve_left h2
        apply hb
        simp only [qn, ← ha, ← hc]
        linear_combination hk2 - hA
      · refine ⟨⟨0, 0, a * b.imK, b.imJ⟩, rfl, ?_, ?_⟩
        · simp only [qn, ← ha, ← hc]
          intro h
          have : a * c * (b.imJ ^ 2 - a * b.imK ^ 2) = 0 := by linear_combination h
          exact hC ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hd hβ))
        · simp only [← ha, ← hc]; ring
    · refine ⟨⟨0, c * b.imK, 0, b.imI⟩, rfl, ?_, ?_⟩
      · simp only [qn, ← ha, ← hc]
        intro h
        have : a * c * (b.imI ^ 2 - c * b.imK ^ 2) = 0 := by linear_combination h
        exact hB ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hd hβ))
      · simp only [← ha, ← hc]; ring
  · refine ⟨⟨0, c * b.imJ, -(a * b.imI), 0⟩, rfl, ?_, ?_⟩
    · simp only [qn, ← ha, ← hc]
      intro h
      have : a * c * (a * b.imI ^ 2 + c * b.imJ ^ 2) = 0 := by linear_combination -h
      exact hA ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hd hβ))
    · simp only [← ha, ← hc]; ring

end Coord

theorem conj_of_same_re : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 → d ≠ 0 → β ≠ 0 →
    ∀ x b : Q d β K, qn x = 1 → qn b = 1 → x.re = b.re → x.re ^ 2 ≠ 1 →
      ∃ y : (Q d β K)ˣ, (y : Q d β K) * x * ((y⁻¹ : (Q d β K)ˣ) : Q d β K) = b := by
  intro F K _ _ _ d β h2 hd hβ x b hx hb hre hp
  have hd' : algebraMap F K d ≠ 0 := by
    simpa using (map_ne_zero (algebraMap F K)).2 hd
  have hβ' : algebraMap F K β ≠ 0 := by
    simpa using (map_ne_zero (algebraMap F K)).2 hβ
  have hn : (1 : K) - b.re ^ 2 ≠ 0 := by
    rw [← hre]
    exact fun h => hp (by linear_combination -h)

  have key : ∀ y : (Q d β K)ˣ, (y : Q d β K) * x = b * y →
      ∃ y : (Q d β K)ˣ, (y : Q d β K) * x * ((y⁻¹ : (Q d β K)ˣ) : Q d β K) = b := by
    intro y hy
    exact ⟨y, by rw [hy, mul_assoc, Units.mul_inv, mul_one]⟩
  have hq : qn x = qn b := hx.trans hb.symm
  by_cases h₁ : qn (pureAdd x b) = 0
  · have h₂ : qn (pureSub x b) ≠ 0 := by
      intro h₂
      have hs := qn_add_sub x b
      rw [h₁, h₂, hx, hb, hre] at hs
      have : (2 * 2 : K) * (1 - b.re ^ 2) = 0 := by linear_combination -hs
      exact hn ((mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 h2))
    obtain ⟨z, hz, hzn, ho⟩ := exists_orth h2 hd' hβ' b (by rwa [hb])
    obtain ⟨e, he⟩ := isUnit_of_qn_ne_zero h₂
    obtain ⟨w, hw⟩ := isUnit_of_qn_ne_zero hzn
    refine key (w * e) ?_
    rw [Units.val_mul, hw, he, mul_assoc, pureSub_mul x b hre hq, ← mul_assoc,
      mul_star_of_orth z b hz ho, mul_assoc]
  · obtain ⟨y, hy⟩ := isUnit_of_qn_ne_zero h₁
    refine key y ?_
    rw [hy, pureAdd_mul x b hre hq]

end GlobalTheory.CompanionTheory.PlaneSA.ConjQ
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_norm_one_conjugate : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 → d ≠ 0 → β ≠ 0 →
  ∀ x b : Q d β K, qn x = 1 → qn b = 1 → x.re = b.re → x.re ^ 2 ≠ 1 →
    ∃ y : (Q d β K)ˣ, (y : Q d β K) * x * ((y⁻¹ : (Q d β K)ˣ) : Q d β K) = b := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.ConjQ.conj_of_same_re
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.LocalUnit

variable {F : Type} [Field F] [NumberField F] {d β : F}

open Classical in

theorem proj_sum_inc (T : Finset (Pl F)) (c : (u : Pl F) → Kp u) (u : Pl F) :
    proj u (∑ t ∈ T, inc t (c t)) = if u ∈ T then c u else 0 := by
  rw [map_sum]
  by_cases h : u ∈ T
  · rw [if_pos h, Finset.sum_eq_single_of_mem u h]
    · exact proj_inc_same u _
    · intro b _ hb
      exact proj_inc_ne (Ne.symm hb) _
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun t ht => proj_inc_ne (fun e : u = t => h (by rwa [e])) _

theorem q_ext {a b : Q d β (AF F)} (h : ∀ u : Pl F, qmap (proj u) a = qmap (proj u) b) : a = b := by
  ext
  · exact adele_ext fun u => congrArg QuaternionAlgebra.re (h u)
  · exact adele_ext fun u => congrArg QuaternionAlgebra.imI (h u)
  · exact adele_ext fun u => congrArg QuaternionAlgebra.imJ (h u)
  · exact adele_ext fun u => congrArg QuaternionAlgebra.imK (h u)

def glue (T : Finset (Pl F)) (y : (u : Pl F) → Q d β (Kp u)) : Q d β (AF F) :=
  ⟨1 + ∑ t ∈ T, inc t ((y t).re - 1), ∑ t ∈ T, inc t (y t).imI, ∑ t ∈ T, inc t (y t).imJ,
    ∑ t ∈ T, inc t (y t).imK⟩

theorem qmap_glue_mem (T : Finset (Pl F)) (y : (u : Pl F) → Q d β (Kp u)) {u : Pl F} (h : u ∈ T) :
    qmap (proj u) (glue T y) = y u := by
  classical
  ext
  · change proj u (1 + ∑ t ∈ T, inc t ((y t).re - 1)) = (y u).re
    rw [map_add, map_one, proj_sum_inc T (fun t => (y t).re - 1) u, if_pos h]
    ring
  · change proj u (∑ t ∈ T, inc t (y t).imI) = (y u).imI
    rw [proj_sum_inc T (fun t => (y t).imI) u, if_pos h]
  · change proj u (∑ t ∈ T, inc t (y t).imJ) = (y u).imJ
    rw [proj_sum_inc T (fun t => (y t).imJ) u, if_pos h]
  · change proj u (∑ t ∈ T, inc t (y t).imK) = (y u).imK
    rw [proj_sum_inc T (fun t => (y t).imK) u, if_pos h]

theorem qmap_glue_not_mem (T : Finset (Pl F)) (y : (u : Pl F) → Q d β (Kp u)) {u : Pl F}
    (h : u ∉ T) : qmap (proj u) (glue T y) = 1 := by
  classical
  ext
  · change proj u (1 + ∑ t ∈ T, inc t ((y t).re - 1)) = 1
    rw [map_add, map_one, proj_sum_inc T (fun t => (y t).re - 1) u, if_neg h, add_zero]
  · change proj u (∑ t ∈ T, inc t (y t).imI) = 0
    rw [proj_sum_inc T (fun t => (y t).imI) u, if_neg h]
  · change proj u (∑ t ∈ T, inc t (y t).imJ) = 0
    rw [proj_sum_inc T (fun t => (y t).imJ) u, if_neg h]
  · change proj u (∑ t ∈ T, inc t (y t).imK) = 0
    rw [proj_sum_inc T (fun t => (y t).imK) u, if_neg h]

theorem exists_adelic_unit : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (T : Finset (Pl F))
    (y : (u : Pl F) → (Q d β (Kp u))ˣ),
    ∃ Y : (Q d β (AF F))ˣ, (∀ u ∈ T, qmap (proj u) (Y : Q d β (AF F)) = y u) ∧
      ∀ u, u ∉ T → qmap (proj u) (Y : Q d β (AF F)) = 1 := by
  intro F _ _ d β T y
  classical
  have hl : glue T (fun u => ((y u : (Q d β (Kp u))ˣ) : Q d β (Kp u))) *
      glue T (fun u => (((y u)⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u))) = 1 := by
    refine q_ext fun u => ?_
    rw [map_mul, map_one]
    by_cases h : u ∈ T
    · rw [qmap_glue_mem T _ h, qmap_glue_mem T _ h]
      exact (y u).mul_inv
    · rw [qmap_glue_not_mem T _ h, qmap_glue_not_mem T _ h, one_mul]
  have hr : glue T (fun u => (((y u)⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u))) *
      glue T (fun u => ((y u : (Q d β (Kp u))ˣ) : Q d β (Kp u))) = 1 := by
    refine q_ext fun u => ?_
    rw [map_mul, map_one]
    by_cases h : u ∈ T
    · rw [qmap_glue_mem T _ h, qmap_glue_mem T _ h]
      exact (y u).inv_mul
    · rw [qmap_glue_not_mem T _ h, qmap_glue_not_mem T _ h, one_mul]
  exact ⟨⟨_, _, hl, hr⟩, fun u h => qmap_glue_mem T _ h, fun u h => qmap_glue_not_mem T _ h⟩

end GlobalTheory.CompanionTheory.PlaneSA.LocalUnit
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_quaternion_local_units : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (T : Finset (Pl F)) (y : (u : Pl F) → (Q d β (Kp u))ˣ),
  ∃ Y : (Q d β (AF F))ˣ, (∀ u ∈ T, qmap (proj u) (Y : Q d β (AF F)) = y u) ∧
    ∀ u, u ∉ T → qmap (proj u) (Y : Q d β (AF F)) = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.LocalUnit.exists_adelic_unit
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.KeyApprox

variable {F : Type} [Field F] [NumberField F]

theorem two_ne_zero_Kp (u : Pl F) : (2 : Kp u) ≠ 0 := by
  have : CharZero (Kp u) := charZero_of_injective_algebraMap (algebraMap F (Kp u)).injective
  exact two_ne_zero

theorem neBot_Kp (u : Pl F) : (𝓝[≠] (0 : Kp u)).NeBot := by
  cases u with
  | inl w =>
    letI : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := ⟨2, by
          rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
            map_ofNat]
          simp⟩ }
    exact NormedField.nhdsNE_neBot (0 : w.Completion)
  | inr v =>
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

def IntAt {d β : F} : (u : Pl F) → Q d β (Kp u) → Prop
  | .inl _, _ => True
  | .inr v, x => IntQ v x

theorem intAt_mem_nhds (d β : F) (u : Pl F) : {x : Q d β (Kp u) | IntAt u x} ∈ 𝓝 (1 : Q d β (Kp u)) := by
  cases u with
  | inl w => exact Filter.univ_mem' fun _ => trivial
  | inr v =>
    have hO : IsOpen (Ov v : Set (Kp (Sum.inr v : Pl F))) :=
      show IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) from Valued.isOpen_valuationSubring _
    have h1 : (1 : Kp (Sum.inr v : Pl F)) ∈ Ov v := one_mem (v.adicCompletionIntegers F)
    have h0 : (0 : Kp (Sum.inr v : Pl F)) ∈ Ov v := zero_mem (v.adicCompletionIntegers F)
    have m1 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.re ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F))) :=
      (hO.preimage continuous_re).mem_nhds (by simpa using h1)
    have m2 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.imI ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F))) :=
      (hO.preimage continuous_imI).mem_nhds (by simpa using h0)
    have m3 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.imJ ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F))) :=
      (hO.preimage continuous_imJ).mem_nhds (by simpa using h0)
    have m4 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.imK ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F))) :=
      (hO.preimage continuous_imK).mem_nhds (by simpa using h0)
    filter_upwards [m1, m2, m3, m4] with q q1 q2 q3 q4 using ⟨q1, q2, q3, q4⟩

theorem local_trace_open (u : Pl F) (d β : F) (hd : d ≠ 0) (hβ : β ≠ 0) (c : Q d β (Kp u)) (hc : qn c = 1)
    (W : Set (Q d β (Kp u))) (hW : W ∈ 𝓝 c) :
    ∃ O : Set (Kp u), IsOpen O ∧ O.Nonempty ∧ ∀ x ∈ O, x ^ 2 ≠ 4 ∧ ∃ b ∈ W, qn b = 1 ∧ 2 * b.re = x := by
  have h2 := two_ne_zero_Kp u
  obtain ⟨r, hr, hr1, hr2⟩ := GlobalTheory.T.quaternion_regular_dense d β h2 hd hβ (neBot_Kp u) c hc (interior W) (interior_mem_nhds.2 hW)
  have hWr : W ∈ 𝓝 r := mem_interior_iff_mem_nhds.1 hr
  have ev := GlobalTheory.T.quaternion_trace_open d β r hr1 hr2 (GlobalTheory.T.local_square_roots_near_one u) W hWr
  have ht : Filter.Tendsto (fun x : Kp u => x / 2) (𝓝 (2 * r.re)) (𝓝 r.re) := by
    have hcont : Continuous fun x : Kp u => x * 2⁻¹ := continuous_id.mul continuous_const
    have := hcont.tendsto (2 * r.re)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, h2] using this
  have ev2 := ht.eventually ev
  have ne : ∀ᶠ x in 𝓝 (2 * r.re), x ^ 2 ≠ (4 : Kp u) := by
    refine (isOpen_ne_fun (continuous_pow 2) continuous_const).mem_nhds ?_
    intro h
    apply hr2
    have h4 : (4 : Kp u) ≠ 0 := by
      have : (4 : Kp u) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    apply mul_left_cancel₀ h4
    linear_combination h
  refine ⟨interior {x | x ^ 2 ≠ (4 : Kp u) ∧ ∃ b ∈ W, qn b = 1 ∧ 2 * b.re = x}, isOpen_interior,
    ⟨2 * r.re, mem_interior_iff_mem_nhds.2 ?_⟩, fun x hx => by
      have h := interior_subset hx
      exact h⟩
  filter_upwards [ev2, ne] with x hx1 hx2
  obtain ⟨b, hb, hb1, hb2⟩ := hx1
  exact ⟨hx2, b, hb, hb1, by rw [hb2]; field_simp⟩

theorem proj_algebraMap (u : Pl F) (c : F) : proj u (algebraMap F (AF F) c) = algebraMap F (Kp u) c :=
  (proj u).commutes c

theorem rat_re {d β : F} {R : Type} [CommRing R] [Algebra F R] (x : Q d β F) :
    (rat x : Q d β R).re = algebraMap F R x.re := rfl

theorem qmap_proj_rat {d β : F} (u : Pl F) (x : Q d β F) :
    qmap (proj u) (rat x : Q d β (AF F)) = (rat x : Q d β (Kp u)) := by
  ext <;> simp [rat, qmap, Algebra.ofId_apply]

theorem qn_rat {d β : F} {R : Type} [CommRing R] [Algebra F R] (x : Q d β F) (hx : qn x = 1) :
    qn (rat x : Q d β R) = 1 := by
  have := qn_qmap (Algebra.ofId F R) x
  rw [hx, map_one] at this
  exact this

theorem eventually_int (c : F) :
    ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)),
      algebraMap F (Kp (Sum.inr v : Pl F)) c ∈ Ov v := by
  have h := (algebraMap F (AF F) c).2.2
  filter_upwards [h] with v hv
  rw [← proj_algebraMap]
  exact hv

theorem eventually_int_rat (d β : F) (x : Q d β F) :
    ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)),
      IntQ v (rat x : Q d β (Kp (Sum.inr v : Pl F))) := by
  filter_upwards [eventually_int x.re, eventually_int x.imI, eventually_int x.imJ, eventually_int x.imK]
    with v h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩

theorem map_inv_of_eq {A B : Type} [Ring A] [Ring B] (f : A →+* B) (Z : Aˣ) (z : Bˣ) (h : f Z = z) :
    f ((Z⁻¹ : Aˣ) : A) = ((z⁻¹ : Bˣ) : B) := by
  have h1 : f Z * f ((Z⁻¹ : Aˣ) : A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  rw [h] at h1
  calc f ((Z⁻¹ : Aˣ) : A) = ((z⁻¹ : Bˣ) : B) * ((z : B) * f ((Z⁻¹ : Aˣ) : A)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = ((z⁻¹ : Bˣ) : B) := by rw [h1, mul_one]

theorem assemble (d β : F) (hd : d ≠ 0) (hβ : β ≠ 0) (G : ∀ u, Set (Q d β (Kp u))) (s : Pl F)
    (h1 : (1 : Q d β (Kp s)) ∈ G s) (x : Q d β F) (hx : qn x = 1) (hreg : x.re ^ 2 ≠ 1)
    (T : Finset (Pl F)) (hs : s ∉ T) (b : ∀ u, Q d β (Kp u))
    (hb : ∀ u ∈ T, qn (b u) = 1 ∧ (b u).re = algebraMap F (Kp u) x.re ∧ b u ∈ G u)
    (hrest : ∀ u, u ∉ T → u ≠ s → (rat x : Q d β (Kp u)) ∈ G u) :
    ∃ c : Q d β (AF F), (∀ u, qmap (proj u) c ∈ G u) ∧ ∃ y : (Q d β (AF F))ˣ, ∃ h ∈ SuppAt d β {s},
      (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) = c * h := by
  classical
  have hxu : ∀ u : Pl F, qn (rat x : Q d β (Kp u)) = 1 := fun u => qn_rat x hx
  let xu : ∀ u : Pl F, (Q d β (Kp u))ˣ := fun u =>
    ⟨rat x, star (rat x), by rw [mul_star_eq, hxu, map_one], by rw [star_mul_eq, hxu, map_one]⟩
  have hconj : ∀ u, u ∈ T → ∃ y : (Q d β (Kp u))ˣ,
      (y : Q d β (Kp u)) * rat x * ((y⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u)) = b u := by
    intro u hu
    obtain ⟨q1, q2, -⟩ := hb u hu
    refine GlobalTheory.T.quaternion_norm_one_conjugate d β (two_ne_zero_Kp u) hd hβ _ _ (hxu u) q1 q2.symm ?_
    rw [rat_re]
    intro h
    apply hreg
    apply (algebraMap F (Kp u)).injective
    rw [map_pow, h, map_one]
  choose y hy using hconj
  let y' : ∀ u : Pl F, (Q d β (Kp u))ˣ := fun u => if h : u ∈ T then y u h else 1
  obtain ⟨Y, hY1, hY2⟩ := GlobalTheory.T.adelic_quaternion_local_units d β T y'
  obtain ⟨H, hH1, hH2⟩ := GlobalTheory.T.adelic_quaternion_local_units d β {s} xu
  have hHs : ∀ u, u ≠ s → qmap (proj u) (H : Q d β (AF F)) = 1 := fun u hu =>
    hH2 u (by simpa using hu)
  refine ⟨(Y : Q d β (AF F)) * rat x * ((Y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) *
      ((H⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)), ?_, Y, (H : Q d β (AF F)), ⟨?_, ?_⟩, ?_⟩
  · intro u
    simp only [map_mul, qmap_proj_rat]
    by_cases hu : u ∈ T
    · have hus : u ≠ s := fun e => hs (e ▸ hu)
      have e1 : qmap (proj u) (Y : Q d β (AF F)) = ((y u hu : (Q d β (Kp u))ˣ) : Q d β (Kp u)) := by
        rw [hY1 u hu]; simp [y', hu]
      have e2 := map_inv_of_eq (qmap (proj u)) Y (y u hu) e1
      have e3 := map_inv_of_eq (qmap (proj u)) H 1 (by simpa using hHs u hus)
      rw [e1, e2, e3, hy u hu]
      simpa using (hb u hu).2.2
    · have e1 : qmap (proj u) (Y : Q d β (AF F)) = ((1 : (Q d β (Kp u))ˣ) : Q d β (Kp u)) := by
        simpa using hY2 u hu
      have e2 := map_inv_of_eq (qmap (proj u)) Y 1 e1
      rw [e1, e2]
      by_cases hus : u = s
      · subst hus
        have e3 := map_inv_of_eq (qmap (proj u)) H (xu u) (hH1 u (by simp))
        rw [e3]
        have : (rat x : Q d β (Kp u)) * (((xu u)⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u)) = 1 :=
          Units.mul_inv (xu u)
        simpa [this] using h1
      · have e3 := map_inv_of_eq (qmap (proj u)) H 1 (by simpa using hHs u hus)
        rw [e3]
        simpa using hrest u hu hus
  · refine adele_ext fun u => ?_
    rw [map_one, ← qn_qmap]
    by_cases hus : u = s
    · subst hus
      rw [hH1 u (by simp)]
      exact hxu u
    · rw [hHs u hus, qn_one]
  · intro u hu
    exact hHs u hu
  · rw [mul_assoc _ _ (H : Q d β (AF F)), Units.inv_mul, mul_one]

theorem keyapprox : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → w ≠ s →
  ∀ a ∈ SuppAt d β {w}, (qmap (proj w) a).re ^ 2 ≠ 1 → ∀ V ∈ 𝓝 a,
    ∃ b ∈ V, ∃ y : (Q d β (AF F))ˣ, ∃ x : Q d β F, qn x = 1 ∧ ∃ h ∈ SuppAt d β {s},
      (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) = b * h := by
  classical
  intro F _ _ d β hani s w hs hws a ha hreg V hV
  have hdns : ∀ r : F, r ^ 2 ≠ d := by
    intro r hr
    have h := hani ⟨r, 1, 0, 0⟩ (by simp [qn, hr])
    have := congrArg (fun q : Q d β F => q.imI) h
    simp at this
  have hβ : β ≠ 0 := by
    intro hb
    have h := hani ⟨0, 0, 1, 0⟩ (by simp [qn, hb])
    have := congrArg (fun q : Q d β F => q.imJ) h
    simp at this
  have hd : d ≠ 0 := fun h => hdns 0 (by simp [h])
  obtain ⟨T₀, U, hU, hinf, hbox⟩ := GlobalTheory.T.adelic_quaternion_neighbourhood d β a V hV
  have hAfin := GlobalTheory.T.quaternion_ramified_places_finite d β hdns hβ
  have hE := GlobalTheory.T.quaternion_integral_trace_almost_all d β hd hβ
  have hEfin := Filter.eventually_cofinite.1 hE
  let Tp : Finset (Pl F) :=
    (T₀ ∪ {w} ∪ hAfin.toFinset ∪ hEfin.toFinset.map Function.Embedding.inr).erase s
  have mem_Tp : ∀ u, u ≠ s → (u ∈ T₀ ∨ u = w ∨ (∀ x : Q d β (Kp u), qn x = 0 → x = 0) ∨
      ∃ v ∈ hEfin.toFinset, (Sum.inr v : Pl F) = u) → u ∈ Tp := by
    intro u hus h
    refine Finset.mem_erase.2 ⟨hus, ?_⟩
    rcases h with h | h | h | ⟨v, hv, e⟩
    · simp [h]
    · simp [h]
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa using h))
    · exact Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, hv, e⟩)
  let G : ∀ u, Set (Q d β (Kp u)) := fun u => if u ∈ T₀ then U u else {x | IntAt u x}
  have hGn : ∀ u, u ∉ T₀ → G u = {x | IntAt u x} := fun u h => if_neg h
  have hGc : ∀ u, ∃ c : Q d β (Kp u), qn c = 1 ∧ G u ∈ 𝓝 c := by
    intro u
    by_cases hu : u ∈ T₀
    · refine ⟨qmap (proj u) a, ?_, ?_⟩
      · rw [qn_qmap, ha.1, map_one]
      · simpa [G, hu] using hU u
    · refine ⟨1, qn_one, ?_⟩
      simpa [G, hu] using intAt_mem_nhds d β u
  choose c hc1 hc2 using hGc
  have hO := fun u => local_trace_open u d β hd hβ (c u) (hc1 u) (G u) (hc2 u)
  choose O hOo hOn hOG using hO
  obtain ⟨t, ht, hint⟩ := GlobalTheory.T.weak_approximation_integral s Tp (by simp [Tp]) O (fun u _ => ⟨hOo u, hOn u⟩)
  have hwT : w ∈ Tp := mem_Tp w hws (Or.inr (Or.inl rfl))
  have ht4 : t ^ 2 ≠ 4 := by
    intro h
    refine (hOG w _ (ht w hwT)).1 ?_
    rw [← map_pow, h, map_ofNat]
  have hanis : ∀ u, (∀ x : Q d β (Kp u), qn x = 0 → x = 0) → u ≠ s := by
    rintro u hu rfl
    obtain ⟨x, hx0, hx⟩ := hs
    exact hx0 (hu x hx)
  have hbsq : ∀ (u : Pl F) (b : Q d β (Kp u)), 2 * b.re = algebraMap F (Kp u) t → b.re ^ 2 ≠ 1 := by
    intro u b hb h
    apply ht4
    apply (algebraMap F (Kp u)).injective
    rw [map_pow, ← hb, map_ofNat]
    linear_combination 4 * h
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.T.hasse_principle_norm_trace d β t hani (by
    intro u hu r hr
    have huT : u ∈ Tp := mem_Tp u (hanis u hu) (Or.inr (Or.inr (Or.inl hu)))
    obtain ⟨-, b, -, hb1, hb2⟩ := hOG u _ (ht u huT)
    refine GlobalTheory.T.quaternion_anisotropic_trace d β (two_ne_zero_Kp u) hu b hb1 (hbsq u b hb2) r ?_
    rw [hr, hb2, map_sub, map_pow, map_ofNat])
  have hxreg : x.re ^ 2 ≠ 1 := fun h => ht4 (by rw [← hx2]; linear_combination 4 * h)
  have hE2 := Filter.eventually_cofinite.1 (eventually_int_rat d β x)
  let T₁ : Finset (Pl F) := (Tp ∪ hE2.toFinset.map Function.Embedding.inr).erase s
  have hre : ∀ (u : Pl F) (b : Q d β (Kp u)), 2 * b.re = algebraMap F (Kp u) t →
      b.re = algebraMap F (Kp u) x.re := by
    intro u b hb
    apply mul_left_cancel₀ (two_ne_zero_Kp u)
    rw [hb, ← hx2, map_mul, map_ofNat]
  have hb : ∀ u, ∃ b : Q d β (Kp u), u ∈ T₁ →
      qn b = 1 ∧ b.re = algebraMap F (Kp u) x.re ∧ b ∈ G u := by
    intro u
    by_cases hu : u ∈ Tp
    · obtain ⟨-, b, hb0, hb1, hb2⟩ := hOG u _ (ht u hu)
      exact ⟨b, fun _ => ⟨hb1, hre u b hb2, hb0⟩⟩
    · by_cases hu1 : u ∈ T₁
      · have hus : u ≠ s := (Finset.mem_erase.1 hu1).1
        have hu2 := (Finset.mem_erase.1 hu1).2
        rcases Finset.mem_union.1 hu2 with h | h
        · exact absurd h hu
        · obtain ⟨v, -, rfl⟩ := Finset.mem_map.1 h
          have hvE : v ∉ hEfin.toFinset := fun hv => hu (mem_Tp _ hus (Or.inr (Or.inr (Or.inr ⟨v, hv, rfl⟩))))
          have hvE' : ∀ t ∈ Ov v, ∃ b : Q d β (Kp (Sum.inr v : Pl F)), qn b = 1 ∧ 2 * b.re = t ∧ IntQ v b := by
            by_contra hcon
            exact hvE (by simpa using hcon)
          have hnT : (Sum.inr v : Pl F) ∉ T₀ := fun h0 => hu (mem_Tp _ hus (Or.inl h0))
          obtain ⟨b, hb1, hb2, hb3⟩ := hvE' _ (hint v hu hus)
          refine ⟨b, fun _ => ⟨hb1, hre _ b hb2, ?_⟩⟩
          have h3 : b ∈ G (Sum.inr v) := by
            rw [hGn _ hnT]
            exact hb3
          exact h3
      · exact ⟨1, fun h => absurd h hu1⟩
  choose b hb using hb
  have hG1 : (1 : Q d β (Kp s)) ∈ G s := by
    by_cases h : s ∈ T₀
    · have e : qmap (proj s) a = 1 := ha.2 s (by simpa using fun e : s = w => hws e.symm)
      have := mem_of_mem_nhds (hU s)
      rw [e] at this
      simpa [G, h] using this
    · simpa [G, h] using mem_of_mem_nhds (intAt_mem_nhds d β s)
  have hrest : ∀ u, u ∉ T₁ → u ≠ s → (rat x : Q d β (Kp u)) ∈ G u := by
    intro u hu hus
    have hnT : u ∉ T₀ := fun h0 => hu (Finset.mem_erase.2 ⟨hus, Finset.mem_union_left _ (mem_Tp u hus (Or.inl h0))⟩)
    cases u with
    | inl w' => exact absurd (hinf w') hnT
    | inr v =>
      have hv : IntQ v (rat x : Q d β (Kp (Sum.inr v : Pl F))) := by
        by_contra hcon
        exact hu (Finset.mem_erase.2 ⟨hus, Finset.mem_union_right _
          (Finset.mem_map.2 ⟨v, by simpa using hcon, rfl⟩)⟩)
      rw [hGn _ hnT]
      exact hv
  obtain ⟨e, he, y, h, hh, hy⟩ := assemble d β hd hβ G s hG1 x hx1 hxreg T₁ (by simp [T₁]) b
    (fun u hu => hb u hu) hrest
  refine ⟨e, hbox e (fun u hu => ?_) (fun v hv => ?_), y, x, hx1, h, hh, hy⟩
  · simpa [G, hu] using he u
  · have h2 := he (Sum.inr v)
    rw [hGn _ hv] at h2
    exact h2

end GlobalTheory.CompanionTheory.PlaneSA.KeyApprox
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_conjugate_approximation : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → w ≠ s →
  ∀ a ∈ SuppAt d β {w}, (qmap (proj w) a).re ^ 2 ≠ 1 → ∀ V ∈ 𝓝 a,
    ∃ b ∈ V, ∃ y : (Q d β (AF F))ˣ, ∃ x : Q d β F, qn x = 1 ∧ ∃ h ∈ SuppAt d β {s},
      (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) = b * h := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.KeyApprox.keyapprox
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.Compact

section General

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open scoped NumberField.AdeleRing

attribute [local instance] adeleTensorTopology isModuleTopology_adeleTensor
  isTopologicalRing_adeleTensor t2Space_adeleTensor

set_option maxSynthPendingDepth 1 in

theorem exists_compact_transport {K D B : Type*} [Field K] [NumberField K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] [Ring B] [Algebra 𝔸[K] B] [TopologicalSpace B] [IsTopologicalRing B]
    [ContinuousSMul 𝔸[K] B] (Φ : 𝔸[K] ⊗[K] D ≃ₐ[𝔸[K]] B) :
    ∃ C : Set Bˣ, IsCompact C ∧ ∀ y : Bˣ, ∃ c ∈ C, ∃ δ : Dˣ, ∃ z : (𝔸[K])ˣ,
      y = c * Units.map (Φ : 𝔸[K] ⊗[K] D →* B) (rationalUnits K D δ) *
        Units.map (Φ : 𝔸[K] ⊗[K] D →* B) (scalarUnits K D z) := by
  obtain ⟨Ω, hΩ, hdec⟩ := exists_isCompact_normOneUnits (K := K) (D := D) (Module.finBasis K D)
  let f : (𝔸[K] ⊗[K] D)ˣ →* Bˣ := Units.map (Φ : 𝔸[K] ⊗[K] D →* B)
  have hΦ : Continuous (Φ : 𝔸[K] ⊗[K] D →* B) :=
    IsModuleTopology.continuous_of_linearMap Φ.toLinearEquiv.toLinearMap
  have hf : Continuous f := Continuous.units_map _ hΦ
  refine ⟨(fun w => (f w)⁻¹) '' Ω, hΩ.image hf.inv, fun y => ?_⟩
  let g : Bˣ →* (𝔸[K] ⊗[K] D)ˣ := Units.map (Φ.symm : B →* 𝔸[K] ⊗[K] D)
  have hfg : f (g y) = y := Units.ext (by simp [f, g])
  obtain ⟨a, ha⟩ := exists_scalar_mem_normOneUnits (Module.finBasis K D) (g y)⁻¹
  obtain ⟨δ, hδ⟩ := hdec _ ha
  refine ⟨_, ⟨_, hδ, rfl⟩, δ⁻¹, a, ?_⟩
  change y = (f _)⁻¹ * f (rationalUnits K D δ⁻¹) * f (scalarUnits K D a)
  simp only [map_mul, map_inv, hfg]
  group

end General

section Quat

variable {F : Type} [Field F] {d β : F} {R : Type} [CommRing R] [Algebra F R]

@[reducible] def divRing (h : ∀ x : Q d β F, qn x = 0 → x = 0) : DivisionRing (Q d β F) :=
  { (inferInstance : Ring (Q d β F)) with
    inv := fun x => (qn x)⁻¹ • star x
    exists_pair_ne := ⟨0, 1, fun e => zero_ne_one (congrArg QuaternionAlgebra.re e)⟩
    mul_inv_cancel := fun x hx => by
      have hq : qn x ≠ 0 := fun e => hx (h x e)
      change x * ((qn x)⁻¹ • star x) = 1
      rw [mul_smul_comm, mul_star_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hq, map_one]
    inv_zero := by
      change (qn (0 : Q d β F))⁻¹ • star (0 : Q d β F) = 0
      simp
    nnqsmul := _
    qsmul := _ }

def ratA : Q d β F →ₐ[F] Q d β R :=
  { (rat : Q d β F →+* Q d β R) with
    commutes' := fun r => by
      have e : algebraMap F (Q d β R) r = ⟨algebraMap F R r, 0, 0, 0⟩ := rfl
      ext <;> simp [rat, qmap, Algebra.ofId_apply, QuaternionAlgebra.algebraMap_eq, e] }

def phi : R ⊗[F] Q d β F →ₐ[R] Q d β R :=
  Algebra.TensorProduct.lift (Algebra.ofId R (Q d β R)) ratA (fun a _ => Algebra.commutes a _)

theorem phi_tmul (a : R) (x : Q d β F) :
    phi (d := d) (β := β) (R := R) (a ⊗ₜ[F] x) = algebraMap R (Q d β R) a * rat x := by
  exact Algebra.TensorProduct.lift_tmul _ _ _ a x

def psi (x : Q d β R) : R ⊗[F] Q d β F :=
  x.re ⊗ₜ[F] (⟨1, 0, 0, 0⟩ : Q d β F) + x.imI ⊗ₜ[F] (⟨0, 1, 0, 0⟩ : Q d β F) +
    x.imJ ⊗ₜ[F] (⟨0, 0, 1, 0⟩ : Q d β F) + x.imK ⊗ₜ[F] (⟨0, 0, 0, 1⟩ : Q d β F)

theorem phi_psi (x : Q d β R) : phi (d := d) (β := β) (R := R) (psi x) = x := by
  simp only [psi, map_add, phi_tmul]
  ext <;> simp [rat, qmap, QuaternionAlgebra.algebraMap_eq]

theorem psi_add (x y : Q d β R) : psi (x + y) = psi x + psi y := by
  simp only [psi, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, TensorProduct.add_tmul]
  abel

theorem mul_algebraMap_tmul (a : R) (c : F) (y : Q d β F) :
    (a * algebraMap F R c) ⊗ₜ[F] y = a ⊗ₜ[F] (c • y) := by
  rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]

theorem psi_phi (t : R ⊗[F] Q d β F) : psi (phi (d := d) (β := β) (R := R) t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp [psi]
  | add x y hx hy => rw [map_add, psi_add, hx, hy]
  | tmul a x =>
    rw [phi_tmul]
    have e : x = x.re • (⟨1, 0, 0, 0⟩ : Q d β F) + x.imI • (⟨0, 1, 0, 0⟩ : Q d β F) +
        x.imJ • (⟨0, 0, 1, 0⟩ : Q d β F) + x.imK • (⟨0, 0, 0, 1⟩ : Q d β F) := by
      ext <;> simp
    have key : psi (algebraMap R (Q d β R) a * rat x) =
        (a * algebraMap F R x.re) ⊗ₜ[F] (⟨1, 0, 0, 0⟩ : Q d β F) +
          (a * algebraMap F R x.imI) ⊗ₜ[F] (⟨0, 1, 0, 0⟩ : Q d β F) +
          (a * algebraMap F R x.imJ) ⊗ₜ[F] (⟨0, 0, 1, 0⟩ : Q d β F) +
          (a * algebraMap F R x.imK) ⊗ₜ[F] (⟨0, 0, 0, 1⟩ : Q d β F) := by
      simp [psi, rat, qmap, QuaternionAlgebra.algebraMap_eq, Algebra.ofId_apply]
    rw [key]
    simp only [mul_algebraMap_tmul]
    rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← e]

def phiEquiv : R ⊗[F] Q d β F ≃ₐ[R] Q d β R :=
  AlgEquiv.ofBijective (phi (d := d) (β := β) (R := R))
    ⟨Function.LeftInverse.injective psi_phi, Function.RightInverse.surjective phi_psi⟩

theorem continuousSMul_q [TopologicalSpace R] [IsTopologicalRing R] : ContinuousSMul R (Q d β R) := by
  constructor
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  exact ⟨continuous_fst.mul (continuous_re.comp continuous_snd),
    continuous_fst.mul (continuous_imI.comp continuous_snd),
    continuous_fst.mul (continuous_imJ.comp continuous_snd),
    continuous_fst.mul (continuous_imK.comp continuous_snd)⟩

end Quat

theorem exists_isCompact_units :
    ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∃ C : Set (Q d β (AF F))ˣ, IsCompact C ∧ ∀ y : (Q d β (AF F))ˣ, ∃ c ∈ C, ∃ δ : (Q d β F)ˣ, ∃ z : (AF F)ˣ,
    y = c * Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ *
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z := by
  intro F _ _ d β h
  letI : DivisionRing (Q d β F) := divRing h
  haveI : ContinuousSMul (AF F) (Q d β (AF F)) := continuousSMul_q
  obtain ⟨C, hC, hdec⟩ := exists_compact_transport (K := F) (D := Q d β F) (B := Q d β (AF F)) phiEquiv
  refine ⟨C, hC, fun y => ?_⟩
  obtain ⟨c, hc, δ, z, e⟩ := hdec y
  refine ⟨c, hc, δ, z, ?_⟩
  have h1 : Units.map (phiEquiv (d := d) (β := β) (R := AF F) : AF F ⊗[F] Q d β F →* Q d β (AF F))
      (GroundTheory.Automorphic.Anisotropic.rationalUnits F (Q d β F) δ) =
      Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ := by
    refine Units.ext ?_
    change phi (d := d) (β := β) (R := AF F) ((1 : AF F) ⊗ₜ[F] (δ : Q d β F)) = rat (δ : Q d β F)
    rw [phi_tmul, map_one, one_mul]
  have h2 : Units.map (phiEquiv (d := d) (β := β) (R := AF F) : AF F ⊗[F] Q d β F →* Q d β (AF F))
      (GroundTheory.Automorphic.Anisotropic.scalarUnits F (Q d β F) z) =
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z :=
    Units.ext ((phiEquiv (d := d) (β := β) (R := AF F)).commutes (z : AF F))
  rw [e, h1, h2]

end GlobalTheory.CompanionTheory.PlaneSA.Compact
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_class_number_finite : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∃ C : Set (Q d β (AF F))ˣ, IsCompact C ∧ ∀ y : (Q d β (AF F))ˣ, ∃ c ∈ C, ∃ δ : (Q d β F)ˣ, ∃ z : (AF F)ˣ,
    y = c * Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ *
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.Compact.exists_isCompact_units
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.ConjStep

variable {F : Type} [Field F] [NumberField F] {d β : F}

theorem conj_mem_suppAt {T : Set (Pl F)} (c : (Q d β (AF F))ˣ) {g : Q d β (AF F)}
    (hg : g ∈ SuppAt d β T) :
    ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * g * (c : Q d β (AF F)) ∈ SuppAt d β T := by
  have hcc : ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * (c : Q d β (AF F)) = 1 := c.inv_mul
  refine ⟨?_, fun u hu => ?_⟩
  · rw [qn_mul, qn_mul, hg.1, mul_one, ← qn_mul, hcc, qn_one]
  · rw [map_mul, map_mul, hg.2 u hu, mul_one, ← map_mul, hcc, map_one]

theorem star_mem_suppAt {T : Set (Pl F)} {g : Q d β (AF F)} (hg : g ∈ SuppAt d β T) :
    star g ∈ SuppAt d β T := by
  have h1 : star g * g = 1 := by rw [star_mul_eq, hg.1, map_one]
  refine ⟨by rw [qn_star, hg.1], fun u hu => ?_⟩
  have h2 := congrArg (qmap (proj u)) h1
  rwa [map_mul, hg.2 u hu, mul_one, map_one] at h2

theorem conj_central {A : Type*} [Ring A] (c ci D Di Z Zi X : A) (hZ : Z * X = X * Z)
    (hZZ : Z * Zi = 1) : (c * D * Z) * X * (Zi * Di * ci) = c * (D * X * Di) * ci := by
  calc (c * D * Z) * X * (Zi * Di * ci) = c * D * (Z * X) * Zi * Di * ci := by
        simp only [mul_assoc]
    _ = c * D * X * (Z * Zi) * Di * ci := by rw [hZ]; simp only [mul_assoc]
    _ = c * (D * X * Di) * ci := by rw [hZZ]; simp only [mul_assoc, mul_one]

theorem conj_mem_SAQ {s : Pl F} {b : Q d β (AF F)} {y c : (Q d β (AF F))ˣ} {δ : (Q d β F)ˣ} {z : (AF F)ˣ}
    {x : Q d β F} (hx : qn x = 1) {h : Q d β (AF F)} (hh : h ∈ SuppAt d β {s})
    (hy : y = c * Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ *
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z)
    (e : (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) = b * h) :
    ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * b * (c : Q d β (AF F)) ∈ SAQ d β s := by
  set ci : Q d β (AF F) := ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) with hci
  have hcc : ci * (c : Q d β (AF F)) = 1 := c.inv_mul
  have hsh : h * star h = 1 := by rw [mul_star_eq, hh.1, map_one]
  let ρ : Q d β F := (δ : Q d β F) * x * ((δ⁻¹ : (Q d β F)ˣ) : Q d β F)
  have hρ : qn ρ = 1 := by
    have h1 : ((δ⁻¹ : (Q d β F)ˣ) : Q d β F) * (δ : Q d β F) = 1 := δ.inv_mul
    have h2 : qn ((δ⁻¹ : (Q d β F)ˣ) : Q d β F) * qn (δ : Q d β F) = 1 := by
      rw [← qn_mul, h1, qn_one]
    simp only [ρ, qn_mul, hx, mul_one]
    rw [mul_comm]; exact h2
  have hconj : (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) =
      (c : Q d β (AF F)) * rat ρ * ci := by
    subst hy
    have hZZ : algebraMap (AF F) (Q d β (AF F)) (z : AF F) *
        algebraMap (AF F) (Q d β (AF F)) ((z⁻¹ : (AF F)ˣ) : AF F) = 1 := by
      rw [← map_mul, z.mul_inv, map_one]
    have := conj_central (c : Q d β (AF F)) ci (rat (δ : Q d β F))
      (rat ((δ⁻¹ : (Q d β F)ˣ) : Q d β F)) (algebraMap (AF F) (Q d β (AF F)) (z : AF F))
      (algebraMap (AF F) (Q d β (AF F)) ((z⁻¹ : (AF F)ˣ) : AF F)) (rat x)
      (Algebra.commutes _ _) hZZ
    simp only [ρ, map_mul]
    rw [← this]
    simp [mul_inv_rev, hci, mul_assoc]
  have hb : b = (c : Q d β (AF F)) * rat ρ * ci * star h := by
    rw [← hconj, e, mul_assoc, hsh, mul_one]
  refine ⟨ρ, hρ, ci * star h * (c : Q d β (AF F)), conj_mem_suppAt c (star_mem_suppAt hh), ?_⟩
  rw [hb]
  calc ci * ((c : Q d β (AF F)) * rat ρ * ci * star h) * (c : Q d β (AF F))
      = (ci * (c : Q d β (AF F))) * rat ρ * (ci * star h * (c : Q d β (AF F))) := by
        simp only [mul_assoc]
    _ = rat ρ * (ci * star h * (c : Q d β (AF F))) := by rw [hcc, one_mul]

theorem exists_conj_mem_closure : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → w ≠ s →
  ∀ a ∈ SuppAt d β {w}, (qmap (proj w) a).re ^ 2 ≠ 1 →
    ∃ c : (Q d β (AF F))ˣ, ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) := by
  intro F _ _ d β hdiv s w hs hws a ha hre
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.T.quaternion_class_number_finite d β hdiv
  by_contra hne
  push_neg at hne
  let f : (Q d β (AF F))ˣ × Q d β (AF F) → Q d β (AF F) := fun p =>
    ((p.1⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * p.2 * (p.1 : Q d β (AF F))
  have hf : Continuous f :=
    ((Units.continuous_val.comp (continuous_inv.comp continuous_fst)).mul continuous_snd).mul
      (Units.continuous_val.comp continuous_fst)
  have hopen : IsOpen (f ⁻¹' (closure (SAQ d β s))ᶜ) := isClosed_closure.isOpen_compl.preimage hf
  have hsub : C ×ˢ ({a} : Set (Q d β (AF F))) ⊆ f ⁻¹' (closure (SAQ d β s))ᶜ := by
    rintro ⟨c, b⟩ ⟨-, hb⟩
    obtain rfl : b = a := hb
    exact hne c
  obtain ⟨u, v, -, hv, hCu, hav, huv⟩ := generalized_tube_lemma hC isCompact_singleton hopen hsub
  obtain ⟨b, hb, y, x, hx, h, hh, e⟩ :=
    GlobalTheory.T.quaternion_conjugate_approximation d β hdiv s w hs hws a ha hre v (hv.mem_nhds (hav rfl))
  obtain ⟨c, hc, δ, z, hy⟩ := hcov y
  exact huv (Set.mk_mem_prod (hCu hc) hb) (subset_closure (conj_mem_SAQ hx hh hy e))

end GlobalTheory.CompanionTheory.PlaneSA.ConjStep
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_norm_one_conj_closure : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → w ≠ s →
  ∀ a ∈ SuppAt d β {w}, (qmap (proj w) a).re ^ 2 ≠ 1 →
    ∃ c : (Q d β (AF F))ˣ, ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.ConjStep.exists_conj_mem_closure
end
