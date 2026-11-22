module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmallTracesSubgroupGaloisTowerTopStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantsFromFiniteLevel

@[expose] public section

open GlobalTheory.K5

namespace GlobalTheory.K5.GeoLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isAlgZp_zeta (T : Tower p Ω) (n : ℕ) : IsAlgZp p (T.ζ n) := by
  refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) 1
  · simp [(T.prim n).pow_eq_one]

def ggens (T : Tower p Ω) (N : ℕ) : Set Ω :=
  Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x} ∪ T.qq '' Set.Iic N

theorem ggens_mono (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : ggens T m ⊆ ggens T n := by
  unfold ggens
  gcongr

theorem fixes_ggens (T : Tower p Ω) (N : ℕ) (g : Gal p Ω)
    (hg : g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N)) :
    ∀ a ∈ ggens T N, g a = a := by
  have hgeo : ∀ x : Ω, IsAlgZp p x → g x = x := (Subgroup.mem_inf.mp hg).1
  have hq : g (T.qq N) = T.qq N := (Subgroup.mem_inf.mp hg).2
  rintro a ((⟨r, rfl⟩ | ha) | ⟨i, hi, rfl⟩)
  · exact g.commutes r
  · exact hgeo a ha
  · have hi' : i + (N - i) = N := Nat.add_sub_cancel' hi
    rw [GlobalTheory.K5.FinLevel.qq_eq_pow T i (N - i), hi', map_pow, hq]

theorem exists_level_of_fixed (hClo : IsClo p Ω) (T : Tower p Ω) (y : Ω)
    (hy : ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, h y = y) :
    ∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y := by
  haveI := GlobalTheory.K5.FinLevel.charZero_of_tower T
  let L : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (⋃ n, ggens T n)
  have hmemL : ∀ a ∈ ⋃ n, ggens T n, a ∈ L := fun a ha => IntermediateField.subset_adjoin ℚ _ ha
  have hO : ∀ r : O0 p, algebraMap (O0 p) Ω r ∈ L := fun r =>
    hmemL _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inl ⟨r, rfl⟩)⟩)
  let φ : O0 p →+* L := (algebraMap (O0 p) Ω).codRestrict L hO
  have hφ : ∀ r, algebraMap L Ω (φ r) = algebraMap (O0 p) Ω r := fun r => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hClo.inj
    rw [← hφ a, ← hφ b, hab]
  haveI halg : Algebra.IsAlgebraic L Ω := by
    constructor
    intro z
    obtain ⟨P, hP0, hPz⟩ := hClo.alg.isAlgebraic z
    refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφinj).mpr hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hPz
    convert hPz using 2
    exact RingHom.ext hφ
  haveI : IsAlgClosure L Ω := ⟨hClo.clo, halg⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  have hyL : y ∈ L := by
    have : y ∈ Set.range (algebraMap L Ω) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro f
      let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r => f.commutes (φ r))
      have hfix : ∀ a ∈ ⋃ n, ggens T n, g a = a := fun a ha => f.commutes ⟨a, hmemL a ha⟩
      have hg : g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n := by
        refine Subgroup.mem_inf.mpr ⟨fun x hx => hfix x (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr hx)⟩),
          Subgroup.mem_iInf.mpr fun n => Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
        · exact hfix _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr (isAlgZp_zeta T n))⟩)
        · exact hfix _ (Set.mem_iUnion.mpr ⟨n, Or.inr ⟨n, Set.mem_Iic.mpr le_rfl, rfl⟩⟩)
      exact hy g hg
    obtain ⟨l, rfl⟩ := this
    exact l.2
  obtain ⟨S, hS, hyS⟩ := IntermediateField.exists_finset_of_mem_adjoin hyL
  have hex : ∀ t ∈ S, ∃ m, t ∈ ggens T m := fun t ht => Set.mem_iUnion.mp (hS ht)
  choose! m hm using hex
  refine ⟨S.sup m, fun g hg => ?_⟩
  have hSN : (S : Set Ω) ⊆ ggens T (S.sup m) := fun t ht =>
    ggens_mono T (Finset.le_sup (f := m) ht) (hm t ht)
  have hyN : y ∈ IntermediateField.adjoin ℚ (ggens T (S.sup m)) :=
    IntermediateField.adjoin.mono ℚ _ _ hSN hyS
  let gq : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun q => by simp)
  have hle : Algebra.adjoin ℚ (ggens T (S.sup m)) ≤ AlgHom.equalizer (gq : Ω →ₐ[ℚ] Ω) (AlgHom.id ℚ Ω) :=
    Algebra.adjoin_le fun a ha => fixes_ggens T _ g hg a ha
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hyN
  have hr' : g r = r := hle hr
  have hs' : g s = s := hle hs
  rw [map_div₀, hr', hs']

end GlobalTheory.K5.GeoLevel

