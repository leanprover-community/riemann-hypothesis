import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentSupportPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm

section
noncomputable section

namespace GlobalTheory.Mem.IdxFin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

theorem exists_unif {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V] (A B : Submodule R V)
    (hA : A.FG) (h : ∀ x ∈ A, ∃ s : R, s ≠ 0 ∧ s • x ∈ B) : ∃ s : R, s ≠ 0 ∧ ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! f hf using h
  refine ⟨∏ y ∈ S, f y, Finset.prod_ne_zero_iff.2 fun y hy => (hf y (Submodule.subset_span hy)).1, fun x hx => ?_⟩
  have : Submodule.span R (S : Set V) ≤ B.comap ((∏ y ∈ S, f y) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    show (∏ y ∈ S, f y) • y ∈ B
    rw [← Finset.prod_erase_mul S f hy, mul_smul]
    exact B.smul_mem _ (hf y (Submodule.subset_span hy)).2
  exact this hx

theorem locLen_finite {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A C : Submodule (𝓞 K) V) (hA : A.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.locLen w.asIdeal A C ≠ 0}.Finite := by
  by_cases h : ∀ x ∈ A, ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ C
  · obtain ⟨s, hs, hC⟩ := exists_unif A C hA h
    have hf := Ideal.finite_factors (I := Ideal.span {s}) (by simpa using hs)
    refine hf.subset fun w hw => ?_
    by_contra hn
    have hsw : s ∉ w.asIdeal := fun h => hn (Ideal.dvd_span_singleton.2 h)
    have : (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨x, t, ht, hx⟩ -
      exact ⟨s * t, Submonoid.mul_mem _ hsw ht, by rw [mul_smul]; exact hC _ hx⟩
    apply hw
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [this]
    simp [Module.length_eq_zero]
  · push Not at h
    obtain ⟨x, hx, hxC⟩ := h
    refine Set.Finite.subset Set.finite_empty fun w hw => hw ?_
    unfold Formalism.HermitianLatticesTheory.locLen
    have hxA : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A := ⟨1, Submonoid.one_mem _, by simpa using hx⟩
    let φ : 𝓞 K →ₗ[𝓞 K] ((Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A) ⧸
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype) :=
      LinearMap.toSpanSingleton _ _ (Submodule.Quotient.mk ⟨x, hxA⟩)
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro r hr
      by_contra hr0
      have h1 : Submodule.Quotient.mk (p := (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype)
          (r • (⟨x, hxA⟩ : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A)) = 0 := hr
      rw [Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨t, ht, h2⟩ := h1
      refine hxC (t * r) (mul_ne_zero (fun h0 => ht (h0 ▸ w.asIdeal.zero_mem)) hr0) ?_
      rw [mul_smul]
      exact h2
    have hle := Module.length_le_of_injective φ hφ
    have htop : Module.length (𝓞 K) (𝓞 K) = ⊤ := by
      by_contra hne
      have hfl := Module.length_ne_top_iff.1 hne
      have hart : IsArtinianRing (𝓞 K) := (isFiniteLength_iff_isNoetherian_isArtinian.1 hfl).2
      exact RingOfIntegers.not_isField K (IsArtinianRing.isField_of_isDomain _)
    rw [htop, top_le_iff] at hle
    rw [hle]
    rfl

theorem lidx_finite {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V) (hA : A.FG) (hB : B.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.lidx w.asIdeal A B ≠ 0}.Finite := by
  refine ((locLen_finite A (A ⊓ B) hA).union (locLen_finite B (A ⊓ B) hB)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
  apply hw
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [hn.1, hn.2]
  simp

theorem jMt_inj (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis _ _)).1
  have := hli.finite
  have := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  exact inj_of_li D.what₂.embLL (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _) hli





end GlobalTheory.Mem.IdxFin

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

theorem conjPl_injective {K : Type} [Field K] [StarRing K] :
    Function.Injective (Formalism.DivisionValues.conjPl (K := K)) := by
  intro v w h
  have h1 : Ideal.map (Formalism.DivisionValues.cO K) v.asIdeal = Ideal.map (Formalism.DivisionValues.cO K) w.asIdeal :=
    congrArg HeightOneSpectrum.asIdeal h
  have hb : Function.Bijective (Formalism.DivisionValues.cO K) := (Formalism.DivisionValues.cO K).bijective
  have h2 := congrArg (Ideal.comap (Formalism.DivisionValues.cO K)) h1
  rw [Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb] at h2
  exact HeightOneSpectrum.ext h2

theorem dual_fg {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (hH : IsUnit H.det) (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsLattice K A) :
    (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A).FG := by
  classical
  obtain ⟨S, hS⟩ := hA.fg
  have hSm : ∀ a ∈ S, a ∈ A := fun a ha => hS ▸ Submodule.subset_span ha
  have mem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A ↔
      ∀ y ∈ A, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Formalism.DivisionValues.hform H y x := by
    intro x
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]
  choose g hg using fun (x : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A) (a : S) => (mem x).1 x.2 a (hSm a a.2)
  have inj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective (𝓞 K) K
  let φ : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A →ₗ[𝓞 K] (S → 𝓞 K) :=
    { toFun := g
      map_add' := fun x y => funext fun a => inj (by
        rw [hg, Submodule.coe_add, map_add, Pi.add_apply, map_add, hg, hg])
      map_smul' := fun s x => funext fun a => inj (by
        rw [hg, Submodule.coe_smul, ← algebraMap_smul K s (x : Fin d → K), map_smul]
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hg]) }
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : ∀ a ∈ S, Formalism.DivisionValues.hform H a x = 0 := by
      intro a ha
      rw [← hg x ⟨a, ha⟩, show g x ⟨a, ha⟩ = 0 from congrFun hx ⟨a, ha⟩, map_zero]
    have hL : ∀ a ∈ A, Formalism.DivisionValues.hform H a x = 0 := by
      intro a ha
      rw [← hS] at ha
      induction ha using Submodule.span_induction with
      | mem a ha => exact h0 a ha
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      | smul s a _ ha => rw [← algebraMap_smul K s a, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
    have hV : ∀ a, Formalism.DivisionValues.hform H a x = 0 := by
      intro a
      have ha : a ∈ Submodule.span K (A : Set (Fin d → K)) := by rw [hA.span_eq_top]; trivial
      induction ha using Submodule.span_induction with
      | mem a ha => exact hL a ha
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      | smul s a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
    have hM : Matrix.mulVec H (x : Fin d → K) = 0 := by
      funext i
      have := hV (Pi.single i 1)
      simpa [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Pi.single_apply, mul_comm] using this
    exact Subtype.ext (Matrix.eq_zero_of_mulVec_eq_zero hH.ne_zero hM)
  exact Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jw_finite_of_lat {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (hH : IsUnit H.det) (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsLattice K A) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.jw H w A ≠ 0}.Finite :=
  GlobalTheory.Mem.IdxFin.lidx_finite A _ hA.fg (dual_fg H hH A hA)

theorem idx_finite_of_fg {K : Type} [Field K] [NumberField K] {d d' : ℕ} (M : Submodule (𝓞 K) (Fin d' → K))
    (θ : Matrix (Fin d') (Fin d) K) (L : Submodule (𝓞 K) (Fin d → K)) (hM : M.FG) (hL : L.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.idx w M (Formalism.DivisionValues.matLat θ L) ≠ 0}.Finite :=
  GlobalTheory.Mem.IdxFin.lidx_finite M _ hM (hL.map _)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

end
end
