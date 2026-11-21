import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSecGeneric
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsModelAtIntegralIffMemLieLat
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeOfIsLocalModelAtPrime
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDvrModelLieBasisAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationLeIffExistsSmulMem
import BuildAid.ForwardExisting
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyPBId
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosKeyArchAt

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLattice_of_isLocalModel_at_prime : HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth) (𝔭 : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), KeyPow.IsLocalModel (F.key hg rig hr th hth) 𝔭 a M → (∀ i, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i) := by
  first | exact @GlobalTheory.CM.lieLat_of_isLocalModel | exact GlobalTheory.CM.lieLat_of_isLocalModel | (intros; apply GlobalTheory.CM.lieLat_of_isLocalModel <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.L2.LamCM
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

theorem exists_fractionalIdeal_isLocGen_of_valuation : ∀ (K : Type) [Field K] [NumberField K]
    (oa : HeightOneSpectrum (𝓞 K) → ℤ), (Function.support oa).Finite →
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)) (a : K), p.valuation K a = WithZero.exp (-oa p) → IsLocGen p a I := by
  intro K _ _ oa hfin
  refine ⟨∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ oa v, ?_, fun p a ha => ?_⟩
  · refine finprod_induction (fun L : FractionalIdeal (𝓞 K)⁰ K => L ≠ 0) one_ne_zero
      (fun _ _ h h' => mul_ne_zero h h') fun v => ?_
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  · rw [isLocGen_iff_valuation_eq, FractionalIdeal.count_finprod K p oa, ha]
    exact hfin

end GlobalTheory.LamF
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fractionalIdeal_localGen_of_valuation : ∀ (K : Type) [Field K] [NumberField K] (oa : HeightOneSpectrum (𝓞 K) → ℤ), (Function.support oa).Finite → ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧ ∀ (p : HeightOneSpectrum (𝓞 K)) (a : K), p.valuation K a = WithZero.exp (-oa p) → IsLocGen p a I := by
  atlas_forward_decl GlobalTheory.LamF.exists_fractionalIdeal_isLocGen_of_valuation
end

section
section
open NumberField IsDedekindDomain Formalism.L2.LamCM WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

section

variable {K : Type} [Field K] [NumberField K]

theorem det_of_smul_rows {n : ℕ} (s : Fin n → 𝓞 K) (x : Fin n → Fin n → K) :
    (Matrix.of fun i => s i • x i).det = (∏ i, s i) • (Matrix.of x).det := by
  have h : (Matrix.of fun i => s i • x i) =
      Matrix.of fun i j => algebraMap (𝓞 K) K (s i) * (Matrix.of x) i j := by
    ext i j
    simp [Algebra.smul_def]
  rw [h, Matrix.det_mul_column, Algebra.smul_def, map_prod]

omit [NumberField K] in

theorem prod_notMem_asIdeal {n : ℕ} (p : HeightOneSpectrum (𝓞 K)) (s : Fin n → 𝓞 K)
    (hs : ∀ i, s i ∉ p.asIdeal) : ∏ i, s i ∉ p.asIdeal := by
  haveI := p.isPrime
  exact prod_mem (S := p.asIdeal.primeCompl) fun i _ => hs i

theorem valuation_smul_of_notMem (p : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ p.asIdeal) (c : K) :
    p.valuation K (s • c) = p.valuation K c := by
  have h1 : p.valuation K (algebraMap (𝓞 K) K s) = 1 := by
    refine le_antisymm (p.valuation_le_one s) (not_lt.1 fun hlt => hs ?_)
    exact (p.valuation_lt_one_iff_mem s).1 hlt
  rw [Algebra.smul_def, map_mul, h1, one_mul]

theorem valuation_smul_le (p : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (c : K) :
    p.valuation K (s • c) ≤ p.valuation K c := by
  rw [Algebra.smul_def, map_mul]
  exact mul_le_of_le_one_left' (p.valuation_le_one s)

end

theorem exists_detIdeal_isLocGen : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    (Λ : Submodule (𝓞 K) (Fin n → K)), Λ.FG → Submodule.span K (Λ : Set (Fin n → K)) = ⊤ →
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin n) (Fin n) K),
        (∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • M i ∈ Λ) →
        (∀ c ∈ Λ, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i)) →
        IsLocGen p M.det I := by
  intro K _ _ n Λ hfg hspan
  let L : MLat K n := MLat.mk Λ (fun _ => 0)
  have hcoe : (L.detIdeal : Submodule (𝓞 K) K) = L.detSub :=
    A2.detIdeal_coe L (A2.detSub_isFractional L hfg)
  have hmem : ∀ y : K, y ∈ L.detIdeal ↔ y ∈ L.detSub := fun y => by
    rw [← hcoe]; rfl
  have hI : L.detIdeal ≠ 0 := by
    obtain ⟨x, hx, hd⟩ := A2.exists_det_ne Λ hspan
    intro h0
    have h := (hmem _).2 (A2.det_mem L x hx)
    rw [h0] at h
    exact hd ((FractionalIdeal.mem_zero_iff _).1 h)
  refine ⟨L.detIdeal, hI, fun p M h1 h2 => ?_⟩
  refine (isLocGen_iff_valuation_eq p _ _).2 (le_antisymm ?_ ?_)
  · choose s hs hsM using h1
    refine (valuation_le_iff_exists_smul_mem p hI _).2 ⟨∏ i, s i, prod_notMem_asIdeal p s hs, ?_⟩
    have h := A2.det_mem L (fun i => s i • M i) hsM
    rw [det_of_smul_rows s (fun i => M i)] at h
    exact (hmem _).2 h
  · obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    rw [← hv]
    have hy' := (hmem y).1 hy
    clear hv hy
    induction hy' using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨x, hx, rfl⟩ := hd
      choose s hs hsx using fun i => h2 (x i) (hx i)
      let L' : MLat K n := MLat.mk (Submodule.span (𝓞 K) (Set.range fun i => M i)) (fun _ => 0)
      have h := A2.det_mem L' (fun i => s i • x i) hsx
      rw [A2.detSub_free L' (fun i => M i) rfl, det_of_smul_rows, Submodule.mem_span_singleton] at h
      obtain ⟨r, hr⟩ := h
      rw [← valuation_smul_of_notMem p (prod_notMem_asIdeal p s hs), ← hr]
      exact valuation_smul_le p r _
    | zero => simp
    | add a b _ _ ha hb => exact (Valuation.map_add _ a b).trans (max_le ha hb)
    | smul r a _ ha => exact (valuation_smul_le p r a).trans ha

end GlobalTheory.LamF
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_detIdeal_localGen_full_lattice : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)), Λ.FG → Submodule.span K (Λ : Set (Fin n → K)) = ⊤ → ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧ ∀ (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin n) (Fin n) K), (∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • M i ∈ Λ) → (∀ c ∈ Λ, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i)) → IsLocGen p M.det I := by
  atlas_forward_decl GlobalTheory.LamF.exists_detIdeal_isLocGen
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem mem_range_iff_valuation_le_one {R K Γ : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) {π : K} (hπ0 : v π ≠ 0) (hπ : v π < 1) (y : K) :
    y ∈ Set.range (algebraMap R K) ↔ v y ≤ 1 := by
  refine ⟨fun ⟨r, hr⟩ => hr ▸ hR r, fun hy => ?_⟩
  have hu : ∀ u : Rˣ, v (algebraMap R K u) = 1 := fun u => by
    refine le_antisymm (hR _) ?_
    have h1 : v (algebraMap R K u) * v (algebraMap R K (u⁻¹ : Rˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    calc (1 : Γ) = _ := h1.symm
      _ ≤ v (algebraMap R K u) * 1 := mul_le_mul_right (hR _) _
      _ = _ := _root_.mul_one _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hlt : v (algebraMap R K ϖ) < 1 := by
    refine lt_of_le_of_ne (hR _) fun h => ?_
    rcases ValuationRing.isInteger_or_isInteger R π with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hr0 : r ≠ 0 := by
        rintro rfl
        rw [map_zero] at hr
        exact hπ0 (by rw [← hr, map_zero])
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
      rw [← hr, map_mul, map_mul, hu, map_pow, map_pow, h, one_pow, _root_.mul_one] at hπ
      exact lt_irrefl _ hπ
    · have := hR r
      rw [hr, map_inv₀, inv_le_one₀ (zero_lt_iff.2 hπ0)] at this
      exact absurd hπ (not_lt.2 this)
  rcases ValuationRing.isInteger_or_isInteger R y with h | ⟨r, hr⟩
  · exact h
  · by_cases hy0 : y = 0
    · exact ⟨0, by rw [hy0, map_zero]⟩
    by_cases hr' : IsUnit r
    · obtain ⟨u, rfl⟩ := hr'
      refine ⟨(u⁻¹ : Rˣ), ?_⟩
      rw [← inv_inv y, ← hr]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    · exfalso
      have hm : r ∈ IsLocalRing.maximalIdeal R := hr'
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨s, rfl⟩ := hm
      have h1 : v y⁻¹ < 1 := by
        rw [← hr, map_mul, map_mul]
        calc _ ≤ v (algebraMap R K ϖ) * 1 := mul_le_mul_right (hR _) _
          _ < 1 := by rwa [_root_.mul_one]
      rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 hy0))] at h1
      exact absurd hy (not_le.2 h1)

theorem keyLocAt_of_isLocalModel : ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyPow.IsLocalModel x p a M → IsLocGen p a T.I → IsLocGen p M.det abelian₂.I → KeyLocAt x T abelian₂ p := by
  intro K _ _ x T abelian₂ p a M hM ha hd
  obtain ⟨R, _, _, _, _, _, y, th', hth', v', hv', hR, h1, h2, h3⟩ := hM
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer K
  refine ⟨K, inferInstance, inferInstance, R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    RingHom.id K, x, a, M.det, a, M.det, 1, 1, GlobalTheory.keyPB_id K x, ⟨th', hth', v', hv', M, y, h1, h2, rfl, h3⟩,
    fun z => ?_, by simp, by simp, ha, hd⟩
  refine mem_range_iff_valuation_le_one (p.valuation K) hR (π := π) (hπ ▸ WithZero.exp_ne_zero) ?_ z
  rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  decide

end GlobalTheory.LamF
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyLocAt_of_isLocalModel' : ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyPow.IsLocalModel x p a M → IsLocGen p a T.I → IsLocGen p M.det abelian₂.I → KeyLocAt x T abelian₂ p := by
  atlas_forward_decl GlobalTheory.LamF.keyLocAt_of_isLocalModel
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_keyArchAt' : ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (σ : K →+* ℂ), ∃ t n : ℝ, 0 < t ∧ 0 < n ∧ ∀ T abelian₂ : MLine K, T.n σ = t → abelian₂.n σ = n → KeyArchAt x T abelian₂ σ := by
  first | exact @GlobalTheory.LamF.KeyArch.exists_pos_keyArchAt | exact GlobalTheory.LamF.KeyArch.exists_pos_keyArchAt | (intros; apply GlobalTheory.LamF.KeyArch.exists_pos_keyArchAt <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_common_denominator_of_valuation_le_one {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (a : Fin n → K) (ha : ∀ m, p.valuation K (a m) ≤ 1) :
    ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ ∀ m, ∃ b : 𝓞 K, s • a m = algebraMap (𝓞 K) K b := by
  choose nn dd hnd using fun m => p.exists_primeCompl_mul_eq_of_integer (a m) (ha m)
  have hs : (∏ m, (dd m : 𝓞 K)) ∈ p.asIdeal.primeCompl := prod_mem fun m _ => (dd m).2
  refine ⟨∏ m, (dd m : 𝓞 K), hs, fun m => ?_⟩
  refine ⟨nn m * ∏ j ∈ Finset.univ.erase m, (dd j : 𝓞 K), ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), Algebra.smul_def]
  simp only [map_mul]
  rw [← hnd m]
  ring

theorem IsModelAt.rows_span_lieLat {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K}
    {φ : x.P.A.left ⟶ A.A.left} (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) {p : HeightOneSpectrum (𝓞 K)}
    {M : Matrix (Fin x.P.g) (Fin x.P.g) K} (hM : IsModelAt A x φ p M) :
    (∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • M i ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat) ∧
      ∀ c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧
        s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i) := by
  have hdet : M.det ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, -, h, -⟩ := hM
    exact h
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have key := isModelAt_integral_iff_mem_lieLat K A x φ hf p M hM
  refine ⟨fun i => (key (M i)).mp fun m => ?_, fun c hc => ?_⟩
  · have h1 : Matrix.vecMul (M i) M⁻¹ m = (1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i m := by
      rw [← Matrix.mul_nonsing_inv (A := M) hu]
      rfl
    rw [h1, Matrix.one_apply]
    split_ifs <;> simp
  · have hone : (1 : 𝓞 K) ∉ p.asIdeal := fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    have hv := (key c).mpr ⟨1, hone, by simpa using hc⟩
    obtain ⟨s, hs, hb⟩ := exists_common_denominator_of_valuation_le_one p (Matrix.vecMul c M⁻¹) hv
    choose b hb using hb
    refine ⟨s, hs, ?_⟩
    have hc' : c = ∑ m, Matrix.vecMul c M⁻¹ m • M m := by
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul (A := M) hu, Matrix.vecMul_one]
    rw [hc', Finset.smul_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [← smul_assoc, hb m, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

theorem exists_keyLines : Out.SecTwistSt → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∃ T abelian₂ : MLine K, T.Good ∧ abelian₂.Good ∧ (∀ p, KeyLocAt x T abelian₂ p) ∧ (∀ σ, KeyArchAt x T abelian₂ σ) ∧ ∀ p, ∃ M, IsModelAt A x φ p M ∧ IsLocGen p M.det abelian₂.I := by
  intro hT hU _hL hH K _ _ A x φ hfib
  have hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).mp hfib
  let F : GenFib A := GenFib.mk x.P φ hf x.v x.basis
  obtain ⟨hFG, hspan⟩ := GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K A F
  obtain ⟨IL, hIL0, hIL⟩ := GlobalTheory.T.exists_detIdeal_localGen_full_lattice K x.P.g F.lieLat hFG hspan
  obtain ⟨δ, oa, nth, hloc, -, hsupp, -⟩ :=
    GlobalTheory.ThetaDegree.exists_isThetaDeg hT hU K A F x.g_pos x.rig x.rig_gen x.th x.6
  obtain ⟨IT, hIT0, hIT⟩ := GlobalTheory.T.exists_fractionalIdeal_localGen_of_valuation K oa hsupp
  choose t n ht hn hArch using fun σ => GlobalTheory.T.exists_pos_keyArchAt' hU K x σ
  refine ⟨⟨IT, t⟩, ⟨IL, n⟩, And.intro hIT0 ht, And.intro hIL0 hn, fun p => ?_,
    fun σ => hArch σ _ _ rfl rfl, fun p => ?_⟩
  · obtain ⟨a, M, hM, hva⟩ := hloc p
    have hrows := GlobalTheory.T.lieLattice_of_isLocalModel_at_prime hH K A F x.g_pos x.rig x.rig_gen x.th x.6 p a M hM
    exact GlobalTheory.T.keyLocAt_of_isLocalModel' K x ⟨IT, t⟩ ⟨IL, n⟩ p a M hM (hIT p a hva) (hIL p M hrows.1 hrows.2)
  · obtain ⟨M, hM⟩ := GlobalTheory.T.exists_dvrModel_lieBasis_at_prime hT K A x φ hfib p
    have hrows := hM.rows_span_lieLat hf
    exact ⟨M, hM, hIL p M hrows.1 hrows.2⟩

end GlobalTheory.LamF
end
