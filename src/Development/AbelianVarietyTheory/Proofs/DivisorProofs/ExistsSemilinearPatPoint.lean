import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingValuationNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPointDimOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebra
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLattices
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InjectiveOfSumEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegEigLatEqOfIso
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOfLeOfISupIndep

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.FlatCM

namespace GlobalTheory.LieIndex

theorem multilinear_mem_span {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {n : ℕ} (f : MultilinearMap R (fun _ : Fin n => M) N) {S : Set M} {w : Fin n → M}
    (hw : ∀ k, w k ∈ Submodule.span R S) :
    f w ∈ Submodule.span R {z | ∃ y : Fin n → M, (∀ k, y k ∈ S) ∧ z = f y} := by
  choose c hc hs using fun k => (Finsupp.mem_span_iff_linearCombination R S (w k)).1 (hw k) |>.imp fun c h =>
    And.intro trivial h
  have : w = fun k => ∑ s ∈ (c k).support, c k s • (s : M) := funext fun k => by
    rw [← hs k, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [this, f.map_sum_finset]
  refine Submodule.sum_mem _ fun r _ => ?_
  rw [f.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun k => (r k).2, rfl⟩)

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem le_colon_smul {A B : Submodule (𝓞 K) V} (hAB : A ≤ B) (hB : B.FG) (ω : V) (hω : ∀ b ∈ B, ∃ c : K, c • ω = b) :
    A ≤ A.colon B • B := by
  by_cases h0 : B = ⊥
  · subst h0
    exact hAB.trans bot_le
  have hω0 : ω ≠ 0 := by
    rintro rfl
    refine h0 (eq_bot_iff.2 fun b hb => ?_)
    obtain ⟨c, rfl⟩ := hω b hb
    simp
  let f : K →ₗ[𝓞 K] V := (LinearMap.toSpanSingleton K V ω).restrictScalars (𝓞 K)
  have hf : ∀ c, f c = c • ω := fun _ => rfl
  have hinj : Function.Injective f := smul_left_injective K hω0
  have hmap : (B.comap f).map f = B := Submodule.map_comap_eq_self fun b hb => hω b hb
  have hfg : (B.comap f).FG := Submodule.fg_of_fg_map_injective f hinj (hmap.symm ▸ hB)
  let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := ⟨B.comap f, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI : I ≠ 0 := fun h => h0 (by
    have : B.comap f = ⊥ := (congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K =>
      (J : Submodule (𝓞 K) K)) h).trans FractionalIdeal.coe_zero
    rw [← hmap, this, Submodule.map_bot])
  have hint : ∀ b : K, b • ω ∈ B → ∀ c ∈ I⁻¹, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = b * c := fun b hb c hc => by
    have := FractionalIdeal.mul_mem_mul (show b ∈ I from hb) hc
    rw [mul_inv_cancel₀ hI] at this
    exact (FractionalIdeal.mem_one_iff _).1 this
  intro a ha
  obtain ⟨a, rfl⟩ := hω a (hAB ha)
  have h1 : (1 : K) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hI]
    exact FractionalIdeal.one_mem_one _
  rw [← one_mul a]
  refine FractionalIdeal.mul_induction_on (C := fun t => (t * a) • ω ∈ A.colon B • B) h1 (fun b hb c hc => ?_)
    fun x y hx hy => by rw [add_mul, add_smul]; exact add_mem hx hy
  obtain ⟨r, hr⟩ := hint a (hAB ha) c hc
  have e : (b * c * a) • ω = r • b • ω := by
    rw [← algebraMap_smul K r, hr, smul_smul]
    congr 1
    ring
  rw [e]
  refine Submodule.smul_mem_smul (Submodule.mem_colon.2 fun z hz => ?_) hb
  obtain ⟨z, rfl⟩ := hω z hz
  obtain ⟨s, hs⟩ := hint z hz c hc
  have e' : r • z • ω = s • a • ω := by
    rw [← algebraMap_smul K r, ← algebraMap_smul K s, hr, hs, smul_smul, smul_smul]
    congr 1
    ring
  rw [e']
  exact A.smul_mem _ ha

theorem detSpan_mono (m : ℕ) {L N : Submodule (𝓞 K) V} (h : N ≤ L) : detSpan K m N ≤ detSpan K m L :=
  Submodule.span_mono fun _ ⟨y, hy, e⟩ => ⟨y, fun k => h (hy k), e⟩

theorem fg_detSpan (m : ℕ) {L : Submodule (𝓞 K) V} (h : L.FG) : (detSpan K m L).FG := by
  obtain ⟨S, rfl⟩ := h
  have hfin : {z | ∃ y : Fin m → V, (∀ k, y k ∈ (S : Set V)) ∧ z = exteriorPower.ιMulti K m y}.Finite :=
    ((Set.Finite.pi' fun _ : Fin m => S.finite_toSet).image (exteriorPower.ιMulti K m)).subset
      fun _ ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩
  refine Submodule.fg_def.2 ⟨_, hfin, le_antisymm (Submodule.span_mono fun _ ⟨y, hy, e⟩ =>
    ⟨y, fun k => Submodule.subset_span (hy k), e⟩) (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨y, hy, rfl⟩
  exact multilinear_mem_span ((exteriorPower.ιMulti K m).toMultilinearMap.restrictScalars (𝓞 K)) hy

theorem detSpan_le_idx_smul (m : ℕ) {L N : Submodule (𝓞 K) V} (h : N ≤ L) (hL : L.FG)
    (hr : Module.finrank K (Submodule.span K (L : Set V)) ≤ m) : detSpan K m N ≤ idx K m L N • detSpan K m L := by
  haveI : Module.Finite K (Submodule.span K (L : Set V)) := by
    obtain ⟨S, rfl⟩ := hL
    rw [Submodule.span_span_of_tower]
    exact Module.Finite.span_of_finite K S.finite_toSet
  obtain ⟨ω, hω⟩ := (finrank_le_one_iff (K := K) (V := ⋀[K]^m (Submodule.span K (L : Set V)))).1 (by
    rw [exteriorPower.finrank_eq]
    rcases hr.eq_or_lt with e | e
    · rw [e, Nat.choose_self]
    · rw [Nat.choose_eq_zero_of_lt e]
      exact zero_le_one)
  refine le_colon_smul (detSpan_mono m h) (fg_detSpan m hL)
    (exteriorPower.map m (Submodule.span K (L : Set V)).subtype ω) fun b hb => ?_
  have : detSpan K m L ≤ (LinearMap.range (exteriorPower.map m (Submodule.span K (L : Set V)).subtype)).restrictScalars
      (𝓞 K) := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨exteriorPower.ιMulti K m fun k => ⟨y k, Submodule.subset_span (hy k)⟩, by
      rw [exteriorPower.map_apply_ιMulti]; rfl⟩)
  obtain ⟨z, rfl⟩ := this hb
  obtain ⟨c, rfl⟩ := hω z
  exact ⟨c, (map_smul _ _ _).symm⟩

theorem idx_ne_bot (m : ℕ) {L N : Submodule (𝓞 K) V} (hL : L.FG) (h : (L : Set V) ⊆ Submodule.span K (N : Set V)) :
    idx K m L N ≠ ⊥ := by
  obtain ⟨S, rfl⟩ := hL
  have h1 : ∀ s ∈ S, ∃ r : nonZeroDivisors (𝓞 K), r • s ∈ N := fun s hs => by
    simpa using multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (N : Set V) s
      (h (Submodule.subset_span hs))
  choose! r hr using h1
  have h2 : ∀ y ∈ Submodule.span (𝓞 K) (S : Set V), (∏ s ∈ S, (r s : 𝓞 K)) • y ∈ N := fun y hy => by
    classical
    have : Submodule.span (𝓞 K) (S : Set V) ≤ N.comap (LinearMap.lsmul (𝓞 K) V (∏ s ∈ S, (r s : 𝓞 K))) :=
      Submodule.span_le.2 fun s hs => by
        change (∏ s ∈ S, (r s : 𝓞 K)) • s ∈ N
        rw [← Finset.prod_erase_mul _ _ hs, mul_smul]
        exact N.smul_mem _ (hr s hs)
    exact this hy
  refine (Submodule.ne_bot_iff _).2 ⟨(∏ s ∈ S, (r s : 𝓞 K)) ^ m, Submodule.mem_colon.2 fun z hz => ?_,
    pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun s _ => nonZeroDivisors.coe_ne_zero _)⟩
  have : detSpan K m (Submodule.span (𝓞 K) (S : Set V)) ≤
      (detSpan K m N).comap (LinearMap.lsmul (𝓞 K) _ ((∏ s ∈ S, (r s : 𝓞 K)) ^ m)) := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    refine Submodule.subset_span ⟨_, fun k => h2 _ (hy k), ?_⟩
    have := ((exteriorPower.ιMulti K m).toMultilinearMap.restrictScalars (𝓞 K)).map_smul_univ
      (fun _ => ∏ s ∈ S, (r s : 𝓞 K)) y
    simpa using this.symm)
  exact this hz

variable {C O W : Type} [Field C] [CommRing O] [Algebra O C] [AddCommGroup W] [Module C W] [Module O W]
  [IsScalarTower O C W]

theorem map_idx_eq (hO : Function.Injective (algebraMap O C)) {i : K →+* C} {j : 𝓞 K →+* O}
    (hj : ∀ a, algebraMap O C (j a) = i a) (γ : V →ₛₗ[i] W) {n : ℕ} {L N : Submodule (𝓞 K) V} (h : N ≤ L) (hL : L.FG)
    (hr : Module.finrank K (Submodule.span K (L : Set V)) ≤ n) {y : Fin n → W} (hy : LinearIndependent C y)
    (hyL : Submodule.span O (Set.range y) = Submodule.span O (γ '' L)) (m : Matrix (Fin n) (Fin n) C)
    (hN : Submodule.span O (Set.range fun a => ∑ b, m a b • y b) = Submodule.span O (γ '' N)) :
    ∃ d : O, algebraMap O C d = m.det ∧ (idx K n L N).map j = Ideal.span {d} := by
  obtain ⟨π, hπ⟩ := (Fintype.linearCombination C y).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 hy))
  replace hπ : ∀ c : Fin n → C, π (∑ b, c b • y b) = c := fun c => LinearMap.congr_fun hπ c
  let D : W [⋀^Fin n]→ₗ[C] C := Matrix.detRowAlternating.compLinearMap π
  have hD : ∀ w, D w = Matrix.det (Matrix.of fun a => π (w a)) := fun _ => rfl
  have hle : ∀ z w : Fin n → W, (∀ a, w a ∈ Submodule.span O (Set.range z)) → ∃ c : O, D w = c • D z := fun z w hw => by
    choose c hc using fun a => (Submodule.mem_span_range_iff_exists_fun O).1 (hw a)
    refine ⟨(Matrix.of c).det, ?_⟩
    rw [hD, hD, Algebra.smul_def, RingHom.map_det, ← Matrix.det_mul]
    congr 1
    ext a t
    rw [Matrix.of_apply, ← hc, map_sum, Finset.sum_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← algebraMap_smul C (c a b), map_smul]
    rfl
  have hDy : D y = 1 := by
    rw [hD, ← Matrix.det_one (n := Fin n)]
    congr 1
    ext a t
    have := hπ (Pi.single a 1)
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simp [this, Pi.single_apply, Matrix.one_apply, eq_comm]
  have hDm : D (fun a => ∑ b, m a b • y b) = m.det := by
    rw [hD]
    congr 1
    ext a t
    simp only [Matrix.of_apply, hπ]
  letI : Algebra K C := i.toAlgebra
  let g : V →ₗ[K] (Fin n → C) := ⟨⟨fun x => π (γ x), fun _ _ => by simp⟩, fun c x => by
    change π (γ (c • x)) = i c • π (γ x)
    rw [γ.map_smulₛₗ, map_smul]⟩
  let δ : (Fin n → C) [⋀^Fin n]→ₗ[K] C :=
    ⟨Matrix.detRowAlternating.toMultilinearMap.restrictScalars K, Matrix.detRowAlternating.map_eq_zero_of_eq'⟩
  let Δ : ⋀[K]^n V →ₗ[K] C := exteriorPower.alternatingMapLinearEquiv (δ.compLinearMap g)
  have hΔ : ∀ x, Δ (exteriorPower.ιMulti K n x) = D fun a => γ (x a) := fun x =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
  have hΔs : ∀ (r : 𝓞 K) (z : ⋀[K]^n V), Δ (r • z) = j r • Δ z := fun r z => by
    rw [show r • z = (r : K) • z from (algebraMap_smul K r z).symm, map_smul, Algebra.smul_def, Algebra.smul_def, hj]
    rfl
  have up : ∀ (M : Submodule (𝓞 K) V) (z : Fin n → W), Submodule.span O (Set.range z) = Submodule.span O (γ '' M) →
      Submodule.span O (Δ '' detSpan K n M) = Submodule.span O {D z} := fun M z hz => by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨t, ht, rfl⟩
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨x, hx, rfl⟩ := ht
        obtain ⟨c, hc⟩ := hle z (fun a => γ (x a)) fun a => hz.ge (Submodule.subset_span ⟨_, hx a, rfl⟩)
        exact Submodule.mem_span_singleton.2 ⟨c, by rw [hΔ, hc]⟩
      | zero => simp
      | add _ _ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
      | smul r _ _ h₁ => exact Set.mem_of_eq_of_mem (hΔs _ _) (Submodule.smul_mem _ _ h₁)
    · rintro _ rfl
      refine Submodule.span_mono ?_ (multilinear_mem_span (D.toMultilinearMap.restrictScalars O)
        fun a => hz.le (Submodule.subset_span ⟨a, rfl⟩))
      rintro _ ⟨w, hw, rfl⟩
      choose x hx e using hw
      exact ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩, by rw [hΔ, funext e]; rfl⟩
  have hL' := up L y hyL
  have hN' := up N _ hN
  rw [hDy] at hL'
  rw [hDm] at hN'
  have hone : ∀ t ∈ detSpan K n L, ∃ c : O, algebraMap O C c = Δ t := fun t ht => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hL'.le (Submodule.subset_span ⟨t, ht, rfl⟩))
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩
  have hm : m.det ∈ Submodule.map (Algebra.linearMap O C) ((idx K n L N).map j) := by
    refine (hN'.ge.trans (Submodule.span_le.2 ?_)) (Submodule.mem_span_singleton_self _)
    rintro _ ⟨t, ht, rfl⟩
    refine Submodule.smul_induction_on (p := fun t => Δ t ∈ Submodule.map (Algebra.linearMap O C) ((idx K n L N).map j))
      (detSpan_le_idx_smul n h hL hr ht) (fun r hr t ht => ?_) fun _ _ h₁ h₂ => by rw [map_add]; exact add_mem h₁ h₂
    obtain ⟨c, hc⟩ := hone t ht
    exact ⟨j r * c, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem j hr), by
      refine Eq.trans ?_ (hΔs _ _).symm
      rw [← hc, Algebra.smul_def, Algebra.linearMap_apply, map_mul]⟩
  obtain ⟨d, hd, e⟩ := hm
  refine ⟨d, e, le_antisymm (Ideal.map_le_iff_le_comap.2 fun r hr => ?_) ((Ideal.span_singleton_le_iff_mem _).2 hd)⟩
  have : Submodule.span O (Δ '' detSpan K n L) ≤ (Submodule.span O {m.det}).comap (LinearMap.lsmul O C (j r)) :=
    Submodule.span_le.2 (by
      rintro _ ⟨t, ht, rfl⟩
      exact hN'.le (Submodule.subset_span ⟨_, Submodule.mem_colon.1 hr t ht, hΔs r t⟩))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (this (hL'.ge (Submodule.mem_span_singleton_self _)))
  refine Ideal.mem_span_singleton'.2 ⟨c, hO ?_⟩
  rw [map_mul, show algebraMap O C d = m.det from e, ← Algebra.smul_def, hc]
  simp [Algebra.smul_def]

end Index

theorem mem_span_solutions {K C O : Type} [Field K] [NumberField K] [Field C] [CommRing O] [Algebra O C]
    (hO : Function.Injective (algebraMap O C)) {i : K →+* C} {j : 𝓞 K →+* O} (hj : ∀ a, algebraMap O C (j a) = i a)
    {n : ℕ} (Λ : Submodule (𝓞 K) (Fin n → K)) {ι : Type} (A : ι → Matrix (Fin n) (Fin n) K) {w : Fin n → C}
    (hw : w ∈ Submodule.span O ((fun c => i ∘ c) '' (Λ : Set (Fin n → K)))) (hA : ∀ α, ((A α).map i).mulVec w = 0) :
    w ∈ Submodule.span O ((fun c => i ∘ c) '' {c | c ∈ Λ ∧ ∀ α, (A α).mulVec c = 0}) := by
  letI : Algebra (𝓞 K) O := j.toAlgebra
  haveI : IsDomain O := hO.isDomain (algebraMap O C)
  haveI : FaithfulSMul (𝓞 K) O := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h => by
    have := congrArg (algebraMap O C) h
    exact RingOfIntegers.coe_injective (i.injective ((hj a).symm.trans (this.trans (hj b))))
  obtain ⟨m, s, g, hg⟩ := Submodule.mem_span_set'.1 hw
  choose l hl hlg using fun k => (g k).2
  obtain ⟨k, a, y, h₁, h₂⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free (R := 𝓞 K) (M := O)
    (f := (LinearMap.ker (Fintype.linearCombination (𝓞 K) s)).subtype) (x := Fintype.linearCombination (𝓞 K) s)
    (LinearMap.ext fun z => z.2)
  have hs : ∀ t, algebraMap O C (s t) =
      ∑ u, i (a (Pi.single t 1) u : 𝓞 K) * algebraMap O C (y (Finsupp.single u 1)) := fun t => by
    have := LinearMap.congr_fun h₁ (Pi.single t 1)
    rw [Fintype.linearCombination_apply_single, one_smul, LinearMap.comp_apply,
      ← Finsupp.univ_sum_single (a (Pi.single t 1)), map_sum] at this
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finsupp.smul_single_one, map_smul, Algebra.smul_def, map_mul, ← hj]
    rfl
  have rel : ∀ x : Fin m → K, ∑ t, algebraMap O C (s t) * i (x t) = 0 →
      ∀ u, ∑ t, ((a (Pi.single t 1) u : 𝓞 K) : K) * x t = 0 := fun x hx u => by
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) x
    choose z hz using hd
    replace hz : ∀ t, (z t : K) = ((d : 𝓞 K) : K) * x t := fun t => (hz t).trans (Algebra.smul_def _ _)
    have h₃ : a z = 0 := LinearMap.congr_fun h₂ ⟨z, hO (by
      rw [Fintype.linearCombination_apply, map_sum, map_zero, ← mul_zero (i (d : 𝓞 K)), ← hx, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Algebra.smul_def, map_mul, show algebraMap O C (algebraMap (𝓞 K) O (z t)) = i (z t) from hj _, hz, map_mul]
      ring)⟩
    rw [← Finset.univ_sum_single z, map_sum] at h₃
    have h₄ := congrArg (fun f : Fin k →₀ 𝓞 K => algebraMap (𝓞 K) K (f u)) h₃
    simp only [Finsupp.finset_sum_apply, map_sum, Finsupp.zero_apply, map_zero] at h₄
    refine mul_left_cancel₀ (a := ((d : 𝓞 K) : K))
      (RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.coe_ne_zero d)) ?_
    rw [mul_zero, Finset.mul_sum, ← h₄]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show Pi.single t (z t) = z t • (Pi.single t 1 : Fin m → 𝓞 K) by rw [← Pi.single_smul, smul_eq_mul, mul_one],
      map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, show algebraMap (𝓞 K) K (z t) = _ from hz t]
    change _ = _ * ((a (Pi.single t 1) u : 𝓞 K) : K)
    ring
  have hc : ∀ b, w b = ∑ t, algebraMap O C (s t) * i (l t b) := fun b => by
    rw [← hg, Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ => by rw [← hlg t, Pi.smul_apply, Algebra.smul_def]; rfl
  have hsum : ∀ u b, (∑ t, a (Pi.single t 1) u • l t) b = ∑ t, ((a (Pi.single t 1) u : 𝓞 K) : K) * l t b := fun u b => by
    rw [Finset.sum_apply]
    rfl
  have e : w = ∑ u, y (Finsupp.single u 1) • (i ∘ (∑ t, a (Pi.single t 1) u • l t)) := funext fun b => by
    rw [hc, Finset.sum_apply]
    simp only [hs, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Pi.smul_apply, Function.comp_apply, hsum, Algebra.smul_def, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [map_mul]; ring
  rw [e]
  refine Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨_, ⟨Λ.sum_mem fun t _ => Λ.smul_mem _ (hl t), fun α => funext fun b => ?_⟩, rfl⟩)
  have h₅ := rel (fun t => (A α).mulVec (l t) b) (by
    have h₆ := congrFun (hA α) b
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hc, Finset.mul_sum, map_sum, map_mul, Pi.zero_apply] at h₆ ⊢
    rw [← h₆, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring) u
  simp only [Matrix.mulVec, dotProduct, hsum, Finset.mul_sum, Pi.zero_apply] at h₅ ⊢
  rw [← h₅, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem norm_of_map_eq_span {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime] {𝔭 : HeightOneSpectrum (𝓞 K)}
    {i : K →+* ℂ_[ℓ]} (he : 0 < Formalism.BasicNotions.vAdd 𝔭 (ℓ : K))
    (hi : ∀ z : K, z ≠ 0 → ‖i z‖ = (ℓ : ℝ) ^ (-((Formalism.BasicNotions.vAdd 𝔭 z : ℝ) / (Formalism.BasicNotions.vAdd 𝔭 (ℓ : K) : ℝ))))
    {j : 𝓞 K →+* 𝓞_ℂ_[ℓ]} (hj : ∀ a, algebraMap 𝓞_ℂ_[ℓ] ℂ_[ℓ] (j a) = i a) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    {d : 𝓞_ℂ_[ℓ]} (h : I.map j = Ideal.span {d}) :
    ‖algebraMap 𝓞_ℂ_[ℓ] ℂ_[ℓ] d‖ =
      (ℓ : ℝ) ^ (-((multiplicity 𝔭.asIdeal I : ℝ) / (Formalism.BasicNotions.vAdd 𝔭 (ℓ : K) : ℝ))) := by
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have he' : (0 : ℝ) < Formalism.BasicNotions.vAdd 𝔭 (ℓ : K) := by exact_mod_cast he
  have hO : ∀ c : 𝓞_ℂ_[ℓ], ‖algebraMap 𝓞_ℂ_[ℓ] ℂ_[ℓ] c‖ ≤ 1 := fun c => (GlobalTheory.PadicComplexHost.mem_iff_norm _ _).1 c.2
  have hv : ∀ (z : 𝓞 K) (n : ℕ), z ≠ 0 → (z ∈ 𝔭.asIdeal ^ n ↔ (n : ℤ) ≤ Formalism.BasicNotions.vAdd 𝔭 (z : K)) := fun z n hz => by
    rw [← 𝔭.intValuation_le_pow_iff_mem, ← 𝔭.valuation_of_algebraMap (K := K),
      GlobalTheory.PrimeEmbedding.valuation_eq_exp 𝔭 (z := algebraMap (𝓞 K) K z) (RingOfIntegers.coe_ne_zero_iff.2 hz),
      WithZero.exp_le_exp, neg_le_neg_iff]
  have hfin : FiniteMultiplicity 𝔭.asIdeal I :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact 𝔭.isPrime.ne_top) hI
  refine le_antisymm ?_ ?_
  · have hd : d ∈ Submodule.span 𝓞_ℂ_[ℓ] (j '' I) := h.ge (Ideal.mem_span_singleton_self d)
    clear h
    induction hd using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      by_cases h0 : z = 0
      · rw [h0, map_zero, map_zero, norm_zero]
        positivity
      rw [hj, hi _ (RingOfIntegers.coe_ne_zero_iff.2 h0)]
      refine Real.rpow_le_rpow_of_exponent_le hℓ.le (neg_le_neg (div_le_div_of_nonneg_right ?_ he'.le))
      exact_mod_cast (hv z _ h0).1 (Ideal.le_of_dvd (pow_multiplicity_dvd _ _) hz)
    | zero =>
      rw [map_zero, norm_zero]
      positivity
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    | smul c x _ hx =>
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hO c)).trans hx
  · obtain ⟨z, hz, hz'⟩ := SetLike.not_le_iff_exists.1 fun hle =>
      hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _) (Ideal.dvd_iff_le.2 hle)
    have h0 : z ≠ 0 := fun e => hz' (e ▸ zero_mem _)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h.le (Ideal.mem_map_of_mem j hz))
    have h1 : ‖i z‖ ≤ ‖algebraMap 𝓞_ℂ_[ℓ] ℂ_[ℓ] d‖ := by
      rw [← hj, ← hc, map_mul, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hO c)
    refine le_trans ?_ h1
    rw [hi _ (RingOfIntegers.coe_ne_zero_iff.2 h0)]
    refine Real.rpow_le_rpow_of_exponent_le hℓ.le (neg_le_neg (div_le_div_of_nonneg_right ?_ he'.le))
    have := (hv z _ h0).not.1 hz'
    exact_mod_cast (by omega : Formalism.BasicNotions.vAdd 𝔭 (z : K) ≤ (multiplicity 𝔭.asIdeal I : ℤ))

end GlobalTheory.LieIndex
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.PointMap GlobalTheory.FlatCM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieIndex

section Lie

variable {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G] [IsCommMonObj G]

omit [IsCommMonObj G] in
theorem isTangent_iff (w : epsR O ⟶ G) :
    ptMap (TrivSqZeroExt.fstHom O O O) ≫ w = toUnit (specO O O) ≫ η[G] ↔ IsTangent w := Chart.isTan_iff w

theorem exists_coord {n : ℕ} {e : Fin n → (epsR O ⟶ G)} (he : IsLieBasis e) :
    ∃ co : LieG G ≃ (Fin n → O), (∀ x y, co (lieAdd x y) = co x + co y) ∧
      (∀ c x, co (AvDefs.lieScale G c x) = c • co x) ∧ ∀ x a, IsLieComb a e x.1 → co x = a := by
  obtain ⟨h₁, h₂, h₃, -⟩ := LieComb.lieComb_algebra O G n e he.1
  choose co hco hu using fun x : LieG G => he.2 x.1 ((isTangent_iff _).1 x.2)
  have hb : Function.Bijective co := ⟨fun x y h => Subtype.ext ((h₁ _).unique (hco x) (h ▸ hco y)), fun a => by
    obtain ⟨w, hw, -⟩ := h₁ a
    exact ⟨⟨w, (isTangent_iff _).2 (h₂ _ _ hw)⟩, (hu _ _ hw).symm⟩⟩
  refine ⟨Equiv.ofBijective co hb, fun x y => ?_, fun c x => ?_, fun x a h => (hu x a h).symm⟩
  · have := h₃ 2 ![co x, co y] ![x.1, y.1] ![1, 1] _ (fun i => by fin_cases i; exacts [hco x, hco y])
      (IntCoord.isLieComb_mul x.1 y.1)
    simpa using (hu (lieAdd x y) _ this).symm
  · have := h₃ 1 ![co x] ![x.1] ![c] _ (fun i => by fin_cases i; exact hco x)
      ((IntCoord.isLieComb_one_iff c x.1 _).2 rfl)
    simpa using (hu (AvDefs.lieScale G c x) _ this).symm

variable {K : Type} [Field K] [NumberField K] {C : Type} [Field C] [Algebra O C] {i : K →+* C} {j : 𝓞 K →+* O}
  {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) {φ : G.left ⟶ P.A.left}

theorem exists_basis [IsLocalRing O] (hj : ∀ a, algebraMap O C (j a) = i a) (hφ : IsGrpPullback G P.A (spMap j) φ) :
    ∃ (e : Fin F.P₀.g → (epsR O ⟶ G)) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), IsLieBasis e ∧ M.det ≠ 0 ∧
      (∀ k, i ∘ M k ∈ Submodule.span O ((fun c => i ∘ c) '' (F.lieLat : Set (Fin F.P₀.g → K)))) ∧
      ∀ u c x, F.IsCoord u c → IsVecOver j φ u x →
        ∃ a, IsLieComb a e x ∧ i ∘ c = ∑ k, a k • (i ∘ M k) := by
  obtain ⟨N, r, M, hr, hM, -, hloc⟩ := LieGlue.exists_cover_lieLat K P F
  obtain ⟨t, ht⟩ : ∃ t, IsUnit (j (r t)) := by
    by_contra h
    refine Ideal.comap_ne_top j (IsLocalRing.maximalIdeal.isMaximal O).ne_top ?_
    rw [eq_top_iff, ← hr]
    exact Ideal.span_le.2 (by rintro _ ⟨t, rfl⟩; exact fun hu => h ⟨t, hu⟩)
  let R := Localization.subalgebra.ofField K (Submonoid.powers (r t))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (hM t).1)
  have e₁ : (algebraMap R K).comp (algebraMap (𝓞 K) R) = algebraMap (𝓞 K) K :=
    (IsScalarTower.algebraMap_eq _ _ _).symm
  let ψ : R →+* O := IsLocalization.Away.lift (r t) ht
  have hρ : ψ.comp (algebraMap (𝓞 K) R) = j := IsLocalization.Away.lift_comp _ ht
  have hψi : (algebraMap O C).comp ψ = i.comp (algebraMap R K) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (r t)) ?_
    rw [RingHom.comp_assoc, hρ, RingHom.comp_assoc, e₁]
    exact RingHom.ext hj
  let GR := (Over.pullback (spMap (algebraMap (𝓞 K) R))).obj P.A
  have hp : IsGrpPullback GR P.A (spMap (algebraMap (𝓞 K) R)) (pullback.fst _ _) := isGrpPullback_pullback _ _
  have es₁ : spMap (algebraMap (𝓞 K) K) = spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [spMap_comp_spMap, e₁]
  have hF : IsGrpPullback F.P₀.A P.A (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  have w₁ : F.φ ≫ P.A.hom = (F.P₀.A.hom ≫ spMap (algebraMap R K)) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [hF.1.w, es₁, Category.assoc]
  have f₁ := hp.1.lift_fst _ _ w₁
  have hζ : IsGrpPullback F.P₀.A GR (spMap (algebraMap R K)) (hp.1.lift _ _ w₁) :=
    IsGrpPullback.cancel hp (hF.congr es₁ f₁.symm) (hp.1.lift_snd _ _ w₁)
  obtain ⟨e, he, hx⟩ := hloc t R GR (pullback.fst _ _) (hp.1.lift _ _ w₁)
    (IsLocalization.map_units R (⟨r t, Submonoid.mem_powers _⟩ : Submonoid.powers (r t))) hp hζ f₁
  choose e₀ he₀ hM₀ using hx
  have hin := (LieLoc.lieLat_localization K P F R (Submonoid.powers (r t)) GR (pullback.fst _ _) (hp.1.lift _ _ w₁) e e₀
    (M t) hp hζ f₁ he fun k => ⟨he₀ k, hM₀ k⟩).1
  have es₂ : spMap j = spMap ψ ≫ spMap (algebraMap (𝓞 K) R) := by rw [spMap_comp_spMap, hρ]
  have w₂ : φ ≫ P.A.hom = (G.hom ≫ spMap ψ) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [hφ.1.w, es₂, Category.assoc]
  have f₂ := hp.1.lift_fst _ _ w₂
  have hq : IsGrpPullback G GR (spMap ψ) (hp.1.lift _ _ w₂) :=
    IsGrpPullback.cancel hp (hφ.congr es₂ f₂.symm) (hp.1.lift_snd _ _ w₂)
  haveI := P.isAb.comm
  haveI := F.P₀.isAb.comm
  have hsm : Smooth GR.hom := by
    haveI := P.smoothDim
    haveI : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
    exact MorphismProperty.of_isPullback (P := @Smooth) hp.1 inferInstance
  obtain ⟨e', hb, he'⟩ := GlobalTheory.exists_isLieBasis_baseChange R O ψ GR G _ hq hsm _ e he
  refine ⟨e', M t, hb, (hM t).2, fun k => ?_, fun u c x ⟨hu, w, hw, hc⟩ hx => ?_⟩
  · obtain ⟨_, ⟨m, rfl⟩, hs⟩ := hin k
    obtain ⟨s, hs'⟩ := (ht.pow m).exists_left_inv
    have eq : i ∘ M t k = s • i ∘ (r t ^ m • M t k) := funext fun l => by
      have := congrArg (algebraMap O C) hs'
      rw [map_mul, ← map_pow, hj, map_one] at this
      rw [Pi.smul_apply, Function.comp_apply, Function.comp_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def,
        map_mul, ← _root_.mul_assoc]
      exact ((congrArg (· * _) this).trans (_root_.one_mul _)).symm
    rw [eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hs, rfl⟩)
  · obtain ⟨u', hu', -⟩ := existsUnique_isVecOver (f := algebraMap (𝓞 K) R) (A' := GR) hp.1 u
    obtain ⟨a, ha, -⟩ := he.2 u' (hu'.isTangent hp hu)
    have h₃ := Chart.comb_baseChange _ hζ ha he₀ (EllComp.isVecOver_cancel hp.1 hζ.1 hu' (by rw [e₁, f₁]; exact hw))
    have h₄ := Chart.comb_baseChange _ hq ha he' (EllComp.isVecOver_cancel hp.1 hq.1 hu' (by rw [hρ, f₂]; exact hx))
    obtain ⟨-, ht', hcomp, -⟩ := LieComb.lieComb_algebra K F.P₀.A _ F.v F.basis.1
    refine ⟨_, h₄, funext fun l => ?_⟩
    rw [(F.basis.2 w (ht' _ _ hc)).unique hc (hcomp _ (M t) e₀ _ w hM₀ h₃)]
    rw [Function.comp_apply, Finset.sum_apply, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
    exact congrArg (· * i (M t k l)) (RingHom.congr_fun hψi (a k)).symm

theorem exists_semilinear [IsLocalRing O] (hO : Function.Injective (algebraMap O C))
    (hj : ∀ a, algebraMap O C (j a) = i a) (hφ : IsGrpPullback G P.A (spMap j) φ) {W : Type} [AddCommGroup W]
    [Module C W] [Module O W] [IsScalarTower O C W] (b : LieG G → W) (hadd : ∀ x y, b (lieAdd x y) = b x + b y)
    (hsmul : ∀ c x, b (AvDefs.lieScale G c x) = c • b x) :
    ∃ θ : (Fin F.P₀.g → K) →ₛₗ[i] W, (∀ u c (x : LieG G), F.IsCoord u c → IsVecOver j φ u x.1 → b x = θ c) ∧
      ∀ {Λ : Type} [CommRing Λ] (act : OAct Λ P.A) (α : Out.RingAct G Λ),
        (∀ a, (α.act a).left ≫ φ = φ ≫ (act.act a).left) → ∀ (τ : Λ →+* 𝓞 K) (w : W),
        (∃ x : AvDefs.LieTau G α (j.comp τ), b x.1 = w) ↔ w ∈ Submodule.span O (θ '' F.eigLat act τ) := by
  obtain ⟨e, M, he, hM, hML, hover⟩ := exists_basis F hj hφ
  obtain ⟨co, c₁, c₂, c₃⟩ := exists_coord he
  have hd : IsUnit (M.map i).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((map_ne_zero i).2 hM).isUnit
  let ν : (Fin F.P₀.g → O) →ₗ[O] (Fin F.P₀.g → C) := Fintype.linearCombination O fun k => i ∘ M k
  have hν : ∀ a, ν a = Matrix.vecMul (algebraMap O C ∘ a) (M.map i) := fun a => funext fun l => by
    simp [ν, Fintype.linearCombination_apply, Matrix.vecMul, dotProduct, Algebra.smul_def]
  have hν' : ∀ a, Matrix.vecMul (ν a) (M.map i)⁻¹ = algebraMap O C ∘ a := fun a => by
    rw [hν, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hd, Matrix.vecMul_one]
  have hinj : ∀ x y, ν (co x) = ν (co y) → x = y := fun x y h =>
    co.injective (funext fun k => hO (congrFun ((hν' (co x)).symm.trans
      ((congrArg (Matrix.vecMul · (M.map i)⁻¹) h).trans (hν' (co y)))) k))
  have hκ : ∀ u c (x : LieG G), F.IsCoord u c → IsVecOver j φ u x.1 → ν (co x) = i ∘ c := fun u c x hc hx => by
    obtain ⟨a, ha, e⟩ := hover u c x.1 hc hx
    rw [c₃ x a ha, e, Fintype.linearCombination_apply]
  let bl : (Fin F.P₀.g → O) →ₗ[O] W :=
    { toFun := fun a => b (co.symm a)
      map_add' := fun a a' => by
        rw [← hadd]
        exact congrArg b (co.symm_apply_eq.2 (by rw [c₁, co.apply_symm_apply, co.apply_symm_apply]))
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← hsmul]
        exact congrArg b (co.symm_apply_eq.2 (by rw [c₂, co.apply_symm_apply])) }
  let β : (Fin F.P₀.g → C) →ₗ[C] W :=
    Fintype.linearCombination C (fun k => bl (Pi.single k 1)) ∘ₗ Matrix.vecMulLinear (M.map i)⁻¹
  have hβ : ∀ x, β (ν (co x)) = b x := fun x => by
    have : b x = bl (co x) := congrArg b (co.symm_apply_apply x).symm
    rw [this, LinearMap.comp_apply, Matrix.vecMulLinear_apply, hν', Fintype.linearCombination_apply,
      LinearMap.pi_apply_eq_sum_univ bl]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Function.comp_apply, algebraMap_smul]
    congr 2
    funext l
    simp [Pi.single_apply, eq_comm]
  let θ : (Fin F.P₀.g → K) →ₛₗ[i] W :=
    { toFun := fun c => β (i ∘ c)
      map_add' := fun c c' => by rw [← map_add]; exact congrArg β (funext fun l => map_add i _ _)
      map_smul' := fun s c => by rw [← map_smul]; exact congrArg β (funext fun l => map_mul i _ _) }
  refine ⟨θ, fun u c x hc hx => by rw [← hβ, hκ u c x hc hx]; rfl, fun {Λ} _ act α hα τ w => ?_⟩
  obtain ⟨r, hr, hre⟩ := GenFib.exists_lieRep_eigLat K P F Λ act
  have lift : ∀ c ∈ F.lieLat, ∃ x, ν (co x) = i ∘ c ∧ ∀ a, ν (co (AvDefs.lieAct G α a x)) = i ∘ r a c := fun c hc => by
    obtain ⟨u, hu⟩ := ((integral_tangent_coordinates K P F).2.2.2.2.1 c).1 hc
    obtain ⟨x, hx, -⟩ := existsUnique_isVecOver hφ.1 u
    refine ⟨⟨x, (isTangent_iff _).2 (hx.isTangent hφ hu.1)⟩, hκ u c _ hu hx, fun a => hκ _ _ _ (hr a u c hu) ?_⟩
    change (x ≫ α.act a).left ≫ φ = _
    rw [Over.comp_left, Over.comp_left, Category.assoc, hα, ← Category.assoc, hx, Category.assoc]
  have hmv : ∀ (A : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K) c, (A.map i).mulVec (i ∘ c) = i ∘ A.mulVec c := fun A c =>
    funext fun l => (RingHom.map_mulVec i A c l).symm
  have hlin : ∀ a, ∀ z ∈ Submodule.span O ((fun c => i ∘ c) '' (F.lieLat : Set (Fin F.P₀.g → K))), ∃ x, ν (co x) = z ∧
      ν (co (AvDefs.lieAct G α a x)) = ((LinearMap.toMatrix' (r a)).map i).mulVec z := fun a z hz => by
    haveI := α.hom a
    induction hz using Submodule.span_induction with
    | mem _ hc =>
      obtain ⟨c, hc, rfl⟩ := hc
      obtain ⟨x, h₁, h₂⟩ := lift c hc
      exact ⟨x, h₁, by rw [h₂, hmv, LinearMap.toMatrix'_mulVec]⟩
    | zero =>
      refine ⟨AvDefs.lieScale G 0 (lieZero G), by rw [c₂, zero_smul, map_zero], ?_⟩
      rw [show AvDefs.lieAct G α a (AvDefs.lieScale G 0 (lieZero G)) = AvDefs.lieScale G 0 (AvDefs.lieAct G α a (lieZero G))
        from Subtype.ext (Category.assoc _ _ _), c₂, zero_smul, map_zero, Matrix.mulVec_zero]
    | add _ _ _ _ hx hy =>
      obtain ⟨x, rfl, hx⟩ := hx
      obtain ⟨y, rfl, hy⟩ := hy
      refine ⟨lieAdd x y, by rw [c₁, map_add], ?_⟩
      rw [show AvDefs.lieAct G α a (lieAdd x y) = lieAdd (AvDefs.lieAct G α a x) (AvDefs.lieAct G α a y) from
        Subtype.ext (MonObj.mul_comp _ _ _), c₁, map_add, hx, hy, Matrix.mulVec_add]
    | smul s _ _ hx =>
      obtain ⟨x, rfl, hx⟩ := hx
      refine ⟨AvDefs.lieScale G s x, by rw [c₂, map_smul], ?_⟩
      rw [show AvDefs.lieAct G α a (AvDefs.lieScale G s x) = AvDefs.lieScale G s (AvDefs.lieAct G α a x) from
        Subtype.ext (Category.assoc _ _ _), c₂, map_smul, hx, Matrix.mulVec_smul]
  have hτ : ∀ a (z : Fin F.P₀.g → C), j (τ a) • z = i (τ a : 𝓞 K) • z := fun a z => by
    rw [← hj, algebraMap_smul]
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    have h₀ : ν (co x) ∈ Submodule.span O ((fun c => i ∘ c) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
      rw [Fintype.linearCombination_apply]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hML k)
    have h₁ := mem_span_solutions hO hj F.lieLat
      (fun a => LinearMap.toMatrix' (r a) - ((τ a : 𝓞 K) : K) • (1 : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K)) h₀ fun a => by
      obtain ⟨y, h₂, h₃⟩ := hlin a _ h₀
      rw [hinj _ _ h₂, hx a, c₂, map_smul, RingHom.comp_apply, hτ] at h₃
      have : (((τ a : 𝓞 K) : K) • (1 : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K)).map i = i (τ a : 𝓞 K) • 1 := by
        ext k l
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, Matrix.one_apply,
          Matrix.one_apply, apply_ite i, map_one, map_zero]
      rw [Matrix.map_sub _ (map_sub i), Matrix.sub_mulVec, ← h₃, this, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    have h₄ := Submodule.mem_map_of_mem (f := β.restrictScalars O) h₁
    rw [Submodule.map_span, LinearMap.restrictScalars_apply, hβ] at h₄
    refine Submodule.span_mono ?_ h₄
    rintro _ ⟨_, ⟨c, ⟨hc, hc'⟩, rfl⟩, rfl⟩
    refine ⟨c, (hre τ c).1.2 ⟨hc, fun a => ?_⟩, rfl⟩
    have := hc' a
    rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, LinearMap.toMatrix'_mulVec, sub_eq_zero] at this
  · intro hw
    induction hw using Submodule.span_induction with
    | mem _ hc =>
      obtain ⟨c, hc, rfl⟩ := hc
      obtain ⟨h₁, h₂⟩ := (hre τ c).1.1 hc
      obtain ⟨x, h₃, h₄⟩ := lift c h₁
      refine ⟨⟨x, fun a => hinj _ _ ?_⟩, by rw [← hβ, h₃]; rfl⟩
      rw [h₄, h₂, c₂, map_smul, h₃, RingHom.comp_apply, hτ]
      exact funext fun l => map_mul i _ _
    | zero => exact ⟨⟨_, isEig_lieScale α 0 (isEig_lieZero α _)⟩, by rw [hsmul, zero_smul]⟩
    | add _ _ _ _ hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨⟨_, isEig_lieAdd α x.2 y.2⟩, hadd _ _⟩
    | smul s _ _ hx =>
      obtain ⟨x, rfl⟩ := hx
      exact ⟨⟨_, isEig_lieScale α s x.2⟩, hsmul _ _⟩

end Lie

theorem span_range_eq {K C O V V' W W' J : Type} [Field K] [NumberField K] [Field C] [CommRing O] [Algebra O C]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
    [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] [AddCommGroup W] [Module C W] [Module O W] [IsScalarTower O C W]
    [AddCommGroup W'] [Module C W'] [Module O W'] [IsScalarTower O C W'] {i : K →+* C} (θ : V →ₛₗ[i] W)
    (θ' : V' →ₛₗ[i] W') (M : J → V' →ₗ[K] V) (ψ : J → W' →ₗ[C] W) (S : Submodule (𝓞 K) V')
    (h : ∀ a, ∀ c ∈ S, ψ a (θ' c) = θ (M a c)) (y : J → W')
    (hy : ∀ a, Submodule.span O {y a} = Submodule.span O (θ' '' S)) :
    Submodule.span O (Set.range fun a => ψ a (y a)) =
      Submodule.span O (θ '' (⨆ a, S.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V)) := by
  have key : ∀ a, Submodule.span O {ψ a (y a)} = Submodule.span O (θ '' S.map ((M a).restrictScalars (𝓞 K))) := fun a => by
    have := congrArg (Submodule.map ((ψ a).restrictScalars O)) (hy a)
    rw [Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_image] at this
    refine this.trans ?_
    rw [Submodule.map_coe, Set.image_image]
    exact congrArg _ (Set.image_congr (h a))
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨a, rfl⟩
    exact Submodule.span_mono (Set.image_mono (le_iSup (fun a => S.map ((M a).restrictScalars (𝓞 K))) a))
      ((key a).le (Submodule.mem_span_singleton_self _))
  · rintro _ ⟨c, hc, rfl⟩
    refine Submodule.iSup_induction _ (motive := fun c => θ c ∈ Submodule.span O (Set.range fun a => ψ a (y a))) hc
      (fun a c hc => ?_) (by simp) fun _ _ h₁ h₂ => by rw [map_add]; exact add_mem h₁ h₂
    exact Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (f := fun a => ψ a (y a)) a))
      ((key a).ge (Submodule.subset_span ⟨c, hc, rfl⟩))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

theorem fg_eigLat {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) {Λ : Type} [CommRing Λ] (act : OAct Λ P.A)
    (τ : Λ →+* 𝓞 K) : (F.eigLat act τ).FG :=
  (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).1.of_le (Submodule.span_mono fun _ ⟨u, h, _⟩ => ⟨u, h⟩)

section Generic

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

theorem exists_semilinear_patPoint (T : PAT H (Sp (𝓞 K))) (F : GenFib T.pol) : letI := H.starRing
    ∃ θ : (Fin F.P₀.g → K) →ₛₗ[i] (patPoint hv ε i T).V,
      (∀ u c (x : LieG (patPoint hv ε i T).Gt), F.IsCoord u c →
        x.1.left ≫ pullback.fst T.t.G.hom (spMap (embO hv i)) = spMap (Chart.dualMapR (embO hv i)) ≫ u.left →
        (patPoint hv ε i T).bLie x = θ c) ∧
      ∀ τ : 𝓞 E →+* 𝓞 K,
        (patPoint hv ε i T).wRec ((embO hv i).comp τ) = Submodule.span O (θ '' F.eigLat T.t.act τ) := by
  letI := H.starRing
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨θ, h₁, h₂⟩ := @exists_semilinear O _ (patPoint hv ε i T).Gt _ (patPoint hv ε i T).commGt K _ _ C _ _ i _ _ F _ _
    hv.hom_inj (algebraMap_embO hv i)
    (isGrpPullback_pullback T.t.G (spMap (embO hv i))) _ _ _ _ _ (patPoint hv ε i T).bLie (patPoint hv ε i T).bLie_add
    (patPoint hv ε i T).bLie_scale
  refine ⟨θ, h₁, fun τ => Submodule.ext fun w => h₂ T.t.act (patPoint hv ε i T).oGt (fun a => ?_) τ w⟩
  rw [goodPoint_oGt]
  exact pullback.lift_fst _ _ _

theorem map_idx_pat {T B : PAT H (Sp (𝓞 K))} {n : ℕ} {f : Fin n → (T.t.G ⟶ B.t.G)}
    (hf : ∀ a, Serre.IsLinearHom T.t.act B.t.act (f a)) (FT : GenFib T.pol) (FB : GenFib B.pol)
    (M : Fin n → ((Fin FT.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (hM : ∀ a, FT.IsDiffOf FB (f a) (M a))
    (τ : 𝓞 E →+* 𝓞 K) (hr : latRank K (FB.eigLat B.t.act τ) ≤ n) {χ : 𝓞 E →+* O} (hχ : χ = (embO hv i).comp τ) :
    letI := H.starRing
    ∀ (x : Fin n → LieG (patPoint hv ε i B).Gt) (y : Fin n → LieG (patPoint hv ε i T).Gt) (m : Matrix (Fin n) (Fin n) C),
      LinearIndependent C (fun k => (patPoint hv ε i B).bLie (x k)) →
      Submodule.span O (Set.range fun k => (patPoint hv ε i B).bLie (x k)) = (patPoint hv ε i B).wRec χ →
      (∀ a, Submodule.span O {(patPoint hv ε i T).bLie (y a)} = (patPoint hv ε i T).wRec χ) →
      (∀ a, (patPoint hv ε i B).bLie (patLie hv ε i (hf a) (y a)) = ∑ k, m a k • (patPoint hv ε i B).bLie (x k)) →
      ∃ d : O, algebraMap O C d = m.det ∧
        (idx K n (FB.eigLat B.t.act τ) (⨆ a, (FT.eigLat T.t.act τ).map ((M a).restrictScalars (𝓞 K)))).map (embO hv i) =
          Ideal.span {d} := by
  letI := H.starRing
  subst hχ
  intro x y m hx hxs hy hm
  obtain ⟨θ, h₁, h₂⟩ := exists_semilinear_patPoint hv ε i B FB
  obtain ⟨θ', h₁', h₂'⟩ := exists_semilinear_patPoint hv ε i T FT
  refine map_idx_eq hv.hom_inj (algebraMap_embO hv i) θ (iSup_le fun a => ?_) (fg_eigLat _ _ _) hr hx
    (hxs.trans (h₂ τ)) m ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact LamF.diff_mem_eigLat (hf a).comm (hM a) τ hc
  refine Eq.trans ?_ (span_range_eq θ θ' M (fun a => patV hv ε i (hf a)) _ (fun a c hc => ?_) _
    fun a => (hy a).trans (h₂' τ))
  · exact congrArg (fun z => Submodule.span O (Set.range z))
      (funext fun a => ((patV_bLie hv ε i (hf a) (y a)).trans (hm a)).symm)
  · obtain ⟨u, hu, -⟩ := ((integral_tangent_coordinates K _ FT).2.2.2.2.2 _ _ τ c).1 hc
    have hφ := isGrpPullback_pullback T.t.G (spMap (embO hv i))
    obtain ⟨z, hz, -⟩ := existsUnique_isVecOver (f := embO hv i) (A' := (patPoint hv ε i T).Gt) hφ.1 u
    let z' : LieG (patPoint hv ε i T).Gt := ⟨z, (isTangent_iff _).2 (hz.isTangent hφ hu.1)⟩
    refine (congrArg _ (h₁' u c z' hu hz).symm).trans ((patV_bLie hv ε i (hf a) z').trans (h₁ _ _ _ (hM a u c hu) ?_))
    have e : ((Over.pullback (spMap (embO hv i))).map (f a)).left ≫ pullback.fst B.t.G.hom (spMap (embO hv i)) =
        pullback.fst T.t.G.hom (spMap (embO hv i)) ≫ (f a).left := pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg (z.left ≫ ·) e).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (f a).left) hz).trans (Category.assoc _ _ _))))

end Generic

variable {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} {X : CMObj H K ρ σ₁ p q} {FP : GenFib (X.A true).pol}
  {FQ : GenFib (X.A false).pol} {FB : GenFib X.B.pol}
  {MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))} {MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))}
  {τ : 𝓞 E →+* 𝓞 K}

theorem neg_ne (X : CMObj H K ρ σ₁ p q) : -ρ ≠ ρ := fun h =>
  H.d_prime.ne_zero (by simpa [neg_eq_self.1 h] using X.ρ_sq)

theorem comp_bar_rt (hτ : τ H.rt = ρ) : τ.comp (H.bar : 𝓞 E →+* 𝓞 E) H.rt = -ρ := by
  rw [← hτ, ← map_neg, ← EigDec.bar_rt]
  rfl

theorem latRank_eigLat (FB : GenFib X.B.pol) (hτ : τ H.rt = ρ) : latRank K (FB.eigLat X.B.t.act τ) = p ∧
    latRank K (FB.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = q := by
  have h := (EigDec.eigen_decomposition E H K ρ X.B FB p q X.split X.typeB X.ρ_sq).1
  exact ⟨(h _).trans (if_pos hτ), (h _).trans (if_neg (by rw [comp_bar_rt hτ]; exact neg_ne X))⟩

theorem eq_zero_of_latRank {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)} (h : latRank K L = 0) {c : Fin n → K} (hc : c ∈ L) :
    c = 0 :=
  (Submodule.finrank_eq_zero.1 h).le (Submodule.subset_span hc)

theorem idx_sub_ne_bot (hD : IsDiffs FP FQ FB MP MQ) (hτ : τ H.rt = ρ) :
    idx K p (FB.eigLat X.B.t.act τ) (subP FP FB MP τ) ≠ ⊥ ∧
    idx K q (FB.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) ≠ ⊥ := by
  let FA : ∀ b, GenFib (X.A b).pol := fun b => match b with
    | true => FP
    | false => FQ
  let M : ∀ k : Fin p ⊕ Fin q, (Fin (FA k.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K) := fun k => match k with
    | .inl a => MP a
    | .inr a => MQ a
  have h := (NumCompare.ind_concl_iff X FA FB M).1 (Indep.letters_independent thetaUnifAV_all abelianSchemeLaws_all.1
    E H K ρ σ₁ p q X FA FB M fun k => match k with
      | .inl a => hD.1 a
      | .inr a => hD.2 a)
  refine ⟨idx_ne_bot _ (fg_eigLat _ _ _) ((h _).2.trans (Submodule.span_le.2 ?_)),
    idx_ne_bot _ (fg_eigLat _ _ _) ((h _).2.trans (Submodule.span_le.2 ?_))⟩
  · rintro _ ⟨a | a, c, hc, rfl⟩
    · exact Submodule.subset_span (Submodule.mem_iSup_of_mem a ⟨c, hc, rfl⟩)
    · rw [eq_zero_of_latRank (((NumCompare.pure_decomposition X false FQ).1 τ).trans
        (if_neg (by rw [hτ]; exact (neg_ne X).symm))) hc]
      exact Set.mem_of_eq_of_mem (map_zero (MQ a)) (zero_mem _)
  · rintro _ ⟨a | a, c, hc, rfl⟩
    · rw [eq_zero_of_latRank (((NumCompare.pure_decomposition X true FP).1 _).trans
        (if_neg (by rw [comp_bar_rt hτ]; exact neg_ne X))) hc]
      exact Set.mem_of_eq_of_mem (map_zero (MP a)) (zero_mem _)
    · exact Submodule.subset_span (Submodule.mem_iSup_of_mem a ⟨c, hc, rfl⟩)

section Main

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

theorem lie_index (hD : IsDiffs FP FQ FB MP MQ) (hτ : τ H.rt = ρ) : letI := H.starRing
    (idx K p (FB.eigLat X.B.t.act τ) (subP FP FB MP τ) ≠ ⊥ ∧
      idx K q (FB.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) ≠ ⊥) ∧
    (∀ χ : 𝓞 E →+* O, χ = (embO hv i).comp τ →
      ∀ (x : Fin p → LieG (pointB hv ε i X).Gt) (y : Fin p → LieG (pointA hv ε i X true).Gt)
        (m : Matrix (Fin p) (Fin p) C), LinearIndependent C (fun k => (pointB hv ε i X).bLie (x k)) →
        Submodule.span O (Set.range fun k => (pointB hv ε i X).bLie (x k)) = (pointB hv ε i X).wRec χ →
        (∀ a, Submodule.span O {(pointA hv ε i X true).bLie (y a)} = (pointA hv ε i X true).wRec χ) →
        (∀ a, phiVP hv ε i X a ((pointA hv ε i X true).bLie (y a)) = ∑ k, m a k • (pointB hv ε i X).bLie (x k)) →
        ∃ d : O, algebraMap O C d = m.det ∧
          (idx K p (FB.eigLat X.B.t.act τ) (subP FP FB MP τ)).map (embO hv i) = Ideal.span {d}) ∧
    ∀ χ : 𝓞 E →+* O, χ = (embO hv i).comp (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)) →
      ∀ (x : Fin q → LieG (pointB hv ε i X).Gt) (y : Fin q → LieG (pointA hv ε i X false).Gt)
        (m : Matrix (Fin q) (Fin q) C), LinearIndependent C (fun k => (pointB hv ε i X).bLie (x k)) →
        Submodule.span O (Set.range fun k => (pointB hv ε i X).bLie (x k)) = (pointB hv ε i X).wRec χ →
        (∀ a, Submodule.span O {(pointA hv ε i X false).bLie (y a)} = (pointA hv ε i X false).wRec χ) →
        (∀ a, phiVQ hv ε i X a ((pointA hv ε i X false).bLie (y a)) = ∑ k, m a k • (pointB hv ε i X).bLie (x k)) →
        ∃ d : O, algebraMap O C d = m.det ∧
          (idx K q (FB.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))
            (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))).map (embO hv i) = Ideal.span {d} :=
  ⟨idx_sub_ne_bot hD hτ,
    fun _ hχ x y m h₁ h₂ h₃ h₄ => map_idx_pat hv ε i (T := X.A true) (f := phiP X) (fun a => X.lin (Sum.inl a)) FP FB MP hD.1 τ
      (latRank_eigLat FB hτ).1.le hχ x y m h₁ h₂ h₃ fun a => (patV_bLie hv ε i _ (y a)).symm.trans (h₄ a),
    fun _ hχ x y m h₁ h₂ h₃ h₄ => map_idx_pat hv ε i (T := X.A false) (f := phiQ X) (fun a => X.lin (Sum.inr a)) FQ FB MQ hD.2 _
      (latRank_eigLat FB hτ).2.le hχ x y m h₁ h₂ h₃ fun a => (patV_bLie hv ε i _ (y a)).symm.trans (h₄ a)⟩

end Main

end GlobalTheory.LieIndex
end
end
