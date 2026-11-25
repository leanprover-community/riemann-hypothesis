module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.AutomorphismsOfLiftTransitivity
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MemSupIsotropicOfDualPairing
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.Style

section
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped nonZeroDivisors

section Lat

variable {D : D7} {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u) (Λ : LatV D)
  (hΛ : Submodule.IsLattice D.host.E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) (hzΛ : F0.z ∈ Λ)
  (hprim : ∀ c : D.host.E, c • F0.z ∈ Lsub Λ (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c)
  (hT : Tu D u ≠ 0)

theorem z_mem_orth_isotropic : F0.z ∈ orth (hS D) (Xsp (lf D F0)) := a_orth_of_frame F0.e F0.z F0.z_orth


include he hΛ hu hzΛ hprim hT in
theorem exists_lattice_vector_inner_z_one : ∃ m ∈ Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))), (hS D).hT F0.z m = 1 := by
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    classical
    refine { toIsLattice := hΛ, span_eq_top := ?_ }
    rw [eq_top_iff]
    intro v _
    obtain ⟨S, hSgen⟩ := hΛ.fg
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors (𝓞 D.host.E)) (S.image (fun m => (hS D).hT m v))
    have hd0 : (algebraMap (𝓞 D.host.E) D.host.E d) ≠ 0 :=
      (IsFractionRing.injective (𝓞 D.host.E) D.host.E).ne (nonZeroDivisors.ne_zero hd)
    have hv : d • v ∈ Λ := by
      rw [← hu]
      apply (i_mem_dual _ _).2
      intro m hm
      rw [← hSgen] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha⟩ := hint ((hS D).hT x v) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
        apply Submodule.mem_one.2
        refine ⟨a, ?_⟩
        rw [← algebraMap_smul D.host.E, map_smul, smul_eq_mul]
        exact ha
      | zero => simp
      | add x y hx hy ihx ihy =>
        rw [map_add (f := _), LinearMap.add_apply]
        exact Submodule.add_mem _ ihx ihy
      | smul a x hx ih =>
        have ea : a • x = (algebraMap (𝓞 D.host.E) D.host.E a) • x := (algebraMap_smul D.host.E a x).symm
        rw [ea]
        rw [LinearMap.map_smulₛₗ₂]
        simp only [smul_eq_mul, starRingEnd_apply]
        exact mul_mem_one_submodule (star_mem_one_submodule (Submodule.mem_one.2 ⟨a, rfl⟩)) ih
    have : v = (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul D.host.E d v, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
  set M : LatV D := Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))) with hM
  set I : Ideal (𝓞 D.host.E) :=
    (M.map (((hS D).hT F0.z).restrictScalars (𝓞 D.host.E))).comap (Algebra.linearMap (𝓞 D.host.E) D.host.E) with hI
  have memI : ∀ o : 𝓞 D.host.E, o ∈ I ↔ ∃ m ∈ M, (hS D).hT F0.z m = algebraMap (𝓞 D.host.E) D.host.E o := by
    intro o
    rw [hI, Submodule.mem_comap, Submodule.mem_map]
    rfl
  have hzM : F0.z ∈ M := ⟨hzΛ, z_mem_orth_isotropic F0⟩
  have hI0 : I ≠ ⊥ := by
    intro h0
    have h1 : (-(Tu D u : 𝓞 D.host.E)) ∈ I := (memI _).2 ⟨F0.z, hzM, by rw [F0.z_norm]; simp⟩
    rw [h0, Ideal.mem_bot, neg_eq_zero] at h1
    exact hT (by exact_mod_cast h1)
  have hFI0 : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI0
  have hinv : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ ≤ 1 := by
    intro c hc
    rw [FractionalIdeal.mem_inv_iff hFI0] at hc
    have hy : star c • F0.z ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) := by
      refine mem_sup_isotropic_of_dual_pairing F0 he Λ hfull hu _ fun m hm => ?_
      obtain ⟨i, hi⟩ := Submodule.mem_one.1 (i_int Λ hu hzΛ hm.1)
      have hiI : i ∈ I := (memI i).2 ⟨m, hm, hi.symm⟩
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1
        (hc _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨i, hiI, rfl⟩))
      rw [map_smul, smul_eq_mul, ← c_herm F0.z m, ← star_mul', ← hi, ← ho]
      exact star_mem_one_submodule (Submodule.mem_one.2 ⟨o, rfl⟩)
    obtain ⟨o, ho⟩ := hprim (star c) ((mem_Lsub_iff_sup_and_orth F0 Λ).2
      ⟨hy, (orth (hS D) (Xsp (lf D F0))).smul_mem _ (z_mem_orth_isotropic F0)⟩)
    obtain ⟨o', ho'⟩ := i_star_int o
    refine (FractionalIdeal.mem_one_iff _).2 ⟨o', ?_⟩
    rw [ho']
    show star (o : D.host.E) = c
    rw [ho, star_star]
  have h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = I * (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ :=
          (mul_inv_cancel₀ hFI0).symm
      _ ≤ I * 1 := by gcongr
      _ = I := mul_one _
  obtain ⟨x, hx, hx1⟩ := (FractionalIdeal.mem_coeIdeal _).1 (h1 (FractionalIdeal.one_mem_one _))
  obtain ⟨m, hm, e⟩ := (memI x).1 hx
  exact ⟨m, hm, by rw [e, hx1]⟩


include he hz hT in
theorem exists_decomp_orth_plus {v : (hS D).V} (hv : v ∈ orth (hS D) (Xsp (lf D F0))) (hvz : (hS D).hT F0.z v = 0) :
    ∃ w : (D.sp.X 0).V, ∃ ξ ∈ Xsp (lf D F0), v = D.sp.iXY 0 w + ξ := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hv' : v ∈ orth (hS D) (Xplus (lf D F0)) := by
    have h : Xplus (lf D F0) ≤ LinearMap.ker ((hS D).hT.flip v) := by
      refine sup_le (fun x hx => c_mem_orth.1 hv x hx) (Submodule.span_le.2 ?_)
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hvz
    exact c_mem_orth.2 fun x hx => h hx
  rw [← hW] at hv'
  obtain ⟨a, ⟨w, rfl⟩, ξ, hξ, e⟩ := Submodule.mem_sup.1 hv'
  exact ⟨w, ξ, hξ, e.symm⟩


include he hz hT in
theorem inner_mem_one_of_mem_dual_orthLattice {m : (hS D).V} (hmΛ : m ∈ Λ) (hm : m ∈ orth (hS D) (Xsp (lf D F0)))
    (hmz : (hS D).hT F0.z m = 0) {w : (D.sp.X 0).V}
    (hw : w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0))) :
    (hS D).hT m (D.sp.iXY 0 w) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  obtain ⟨x, ξ, hξ, e⟩ := exists_decomp_orth_plus F0 he hz hT hm hmz
  have hx : x ∈ L0X D Λ (lf D F0) := by
    refine (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_
    have : D.sp.iXY 0 x = m + (-ξ) := by rw [e]; abel
    rw [this]
    exact Submodule.add_mem_sup hmΛ ((toO (hS D) (Xsp (lf D F0))).neg_mem hξ)
  rw [e, map_add (f := _), LinearMap.add_apply, orth_embedding_isometry, c_mem_orth.1 (orth_embedding_mem_orth_isotropic F0 he hz w) ξ hξ, add_zero]
  exact (i_mem_dual _ _).1 hw x hx


include he hz hΛ hu hzΛ hprim hT in
theorem dual_orthLattice_quotient_cyclic : ∃ w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)),
    (∀ w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)), ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ L0X D Λ (lf D F0)) ∧
    ∀ a : 𝓞 D.host.E, a • w₁ ∈ L0X D Λ (lf D F0) ↔ ((Tu D u : ℕ) : 𝓞 D.host.E) ∣ a := by
  obtain ⟨m₁, hm₁, hzm⟩ := exists_lattice_vector_inner_z_one F0 he Λ hΛ hu hzΛ hprim hT
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    classical
    refine { toIsLattice := hΛ, span_eq_top := ?_ }
    rw [eq_top_iff]
    intro v _
    obtain ⟨S, hSgen⟩ := hΛ.fg
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors (𝓞 D.host.E)) (S.image (fun m => (hS D).hT m v))
    have hd0 : (algebraMap (𝓞 D.host.E) D.host.E d) ≠ 0 :=
      (IsFractionRing.injective (𝓞 D.host.E) D.host.E).ne (nonZeroDivisors.ne_zero hd)
    have hv : d • v ∈ Λ := by
      rw [← hu]
      apply (i_mem_dual _ _).2
      intro m hm
      rw [← hSgen] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha⟩ := hint ((hS D).hT x v) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
        apply Submodule.mem_one.2
        refine ⟨a, ?_⟩
        rw [← algebraMap_smul D.host.E, map_smul, smul_eq_mul]
        exact ha
      | zero => simp
      | add x y hx hy ihx ihy =>
        rw [map_add (f := _), LinearMap.add_apply]
        exact Submodule.add_mem _ ihx ihy
      | smul a x hx ih =>
        have ea : a • x = (algebraMap (𝓞 D.host.E) D.host.E a) • x := (algebraMap_smul D.host.E a x).symm
        rw [ea]
        rw [LinearMap.map_smulₛₗ₂]
        simp only [smul_eq_mul, starRingEnd_apply]
        exact mul_mem_one_submodule (star_mem_one_submodule (Submodule.mem_one.2 ⟨a, rfl⟩)) ih
    have : v = (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul D.host.E d v, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
  let t : D.host.E := (Tu D u : ℕ)
  have hTE : t ≠ 0 := Nat.cast_ne_zero.2 hT
  set B : LatV D := Λ ⊔ toO (hS D) (Xsp (lf D F0)) with hB
  have hstar : star t = t := by simp [t]
  have hzo := z_mem_orth_isotropic F0

  have hv1 : m₁ + t⁻¹ • F0.z ∈ orth (hS D) (Xsp (lf D F0)) :=
    (orth (hS D) (Xsp (lf D F0))).add_mem hm₁.2 ((orth (hS D) (Xsp (lf D F0))).smul_mem _ hzo)
  have hv2 : (hS D).hT F0.z (m₁ + t⁻¹ • F0.z) = 0 := by
    rw [map_add (f := _), map_smul, hzm, F0.z_norm, smul_eq_mul]
    field_simp
    ring
  obtain ⟨w₁, ξ₁, hξ₁, e₁⟩ := exists_decomp_orth_plus F0 he hz hT hv1 hv2
  have hK1 : D.sp.iXY 0 w₁ - t⁻¹ • F0.z ∈ B := by
    have : D.sp.iXY 0 w₁ - t⁻¹ • F0.z = m₁ + (-ξ₁) := by
      have : D.sp.iXY 0 w₁ = m₁ + t⁻¹ • F0.z - ξ₁ := by rw [e₁]; abel
      rw [this]; abel
    rw [this]
    exact Submodule.add_mem_sup hm₁.1 ((toO (hS D) (Xsp (lf D F0))).neg_mem hξ₁)
  have hmz : (hS D).hT m₁ F0.z = 1 := by rw [← c_herm, hzm, star_one]
  have hw₁ : w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
    refine (i_mem_dual _ _).2 fun x hx => ?_
    have e2 : D.sp.iXY 0 w₁ = m₁ + t⁻¹ • F0.z - ξ₁ := by rw [e₁]; abel
    rw [← orth_embedding_isometry, e2, map_sub, map_add (f := _), map_smul, c_symm0 (inner_z_orth_embedding_eq_zero F0 he hz x), smul_zero, add_zero,
      c_symm0 (c_mem_orth.1 (orth_embedding_mem_orth_isotropic F0 he hz x) ξ₁ hξ₁), sub_zero]
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_image_mem_sup F0 he hz Λ).1 hx)
    rw [← e, map_add (f := _), LinearMap.add_apply, c_mem_orth.1 hm₁.2 ξ hξ, add_zero]
    exact i_int Λ hu hl hm₁.1
  refine ⟨w₁, hw₁, ?_, ?_⟩
  · intro w hw

    have hα : t * (hS D).hT m₁ (D.sp.iXY 0 w) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      have h1 : ((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z ∈ Λ := Λ.add_mem (Λ.smul_mem _ hm₁.1) hzΛ
      have h2 : ((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z ∈ orth (hS D) (Xsp (lf D F0)) :=
        (toO (hS D) (orth (hS D) (Xsp (lf D F0)))).add_mem
          ((toO (hS D) (orth (hS D) (Xsp (lf D F0)))).smul_mem _ hm₁.2) hzo
      have h3 : (hS D).hT F0.z (((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z) = 0 := by
        rw [map_add (f := _), ← algebraMap_smul D.host.E, map_smul, hzm, F0.z_norm]
        simp
      have h4 := inner_mem_one_of_mem_dual_orthLattice F0 he hz Λ hT h1 h2 h3 hw
      rw [map_add (f := _), LinearMap.add_apply, inner_z_orth_embedding_eq_zero F0 he hz w, add_zero, ← algebraMap_smul D.host.E,
        map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at h4
      have h5 : star (algebraMap (𝓞 D.host.E) D.host.E ((Tu D u : ℕ) : 𝓞 D.host.E)) = t := by
        rw [map_natCast]; exact hstar
      rwa [h5] at h4
    obtain ⟨α₀, hα₀⟩ := Submodule.mem_one.1 hα
    refine ⟨-α₀, (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_⟩
    have hy : D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z ∈ B := by
      refine mem_sup_isotropic_of_dual_pairing F0 he Λ hfull hu _ fun m hm => ?_
      obtain ⟨γ, hγ⟩ := Submodule.mem_one.1 (i_int Λ hu hzΛ hm.1)
      have h1 : m - γ • m₁ ∈ Λ := Λ.sub_mem hm.1 (Λ.smul_mem _ hm₁.1)
      have h2 : m - γ • m₁ ∈ orth (hS D) (Xsp (lf D F0)) :=
        (toO (hS D) (orth (hS D) (Xsp (lf D F0)))).sub_mem hm.2
          ((toO (hS D) (orth (hS D) (Xsp (lf D F0)))).smul_mem _ hm₁.2)
      have h3 : (hS D).hT F0.z (m - γ • m₁) = 0 := by
        rw [map_sub, ← algebraMap_smul D.host.E, map_smul, hzm, hγ]
        simp
      have h4 := inner_mem_one_of_mem_dual_orthLattice F0 he hz Λ hT h1 h2 h3 hw
      have h5 : (hS D).hT m (D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z) =
          (hS D).hT (m - γ • m₁) (D.sp.iXY 0 w) := by
        rw [map_add (f := _), map_smul, map_sub, LinearMap.sub_apply, ← algebraMap_smul D.host.E γ, map_smulₛₗ,
          LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply, hγ, c_herm, map_neg, hα₀]
        field_simp
        ring
      rw [h5]
      exact h4
    have e3 : D.sp.iXY 0 (w + (-α₀) • w₁) =
        (D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z) +
          (-α₀) • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) := by
      rw [map_add (f := _), LinearMap.map_smul_of_tower, smul_sub, ← algebraMap_smul D.host.E (-α₀) (t⁻¹ • F0.z), smul_smul]
      abel
    rw [e3]
    exact B.add_mem hy (B.smul_mem _ hK1)
  · intro a
    constructor
    · intro ha
      have h1 := (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).1 ha
      have h2 : (algebraMap (𝓞 D.host.E) D.host.E a * t⁻¹) • F0.z ∈ B := by
        have : (algebraMap (𝓞 D.host.E) D.host.E a * t⁻¹) • F0.z =
            D.sp.iXY 0 (a • w₁) - a • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) := by
          rw [LinearMap.map_smul_of_tower, smul_sub, ← algebraMap_smul D.host.E a (t⁻¹ • F0.z), smul_smul]
          abel
        rw [this]
        exact B.sub_mem h1 (B.smul_mem _ hK1)
      obtain ⟨o, ho⟩ := hprim _ ((mem_Lsub_iff_sup_and_orth F0 Λ).2
        ⟨h2, (orth (hS D) (Xsp (lf D F0))).smul_mem _ hzo⟩)
      refine ⟨o, ?_⟩
      apply RingOfIntegers.ext
      show algebraMap (𝓞 D.host.E) D.host.E a = algebraMap (𝓞 D.host.E) D.host.E (((Tu D u : ℕ) : 𝓞 D.host.E) * o)
      rw [map_mul, map_natCast]
      show algebraMap (𝓞 D.host.E) D.host.E a = t * (o : D.host.E)
      rw [ho]
      field_simp
    · rintro ⟨o, rfl⟩
      refine (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_
      have : D.sp.iXY 0 ((((Tu D u : ℕ) : 𝓞 D.host.E) * o) • w₁) =
          (((Tu D u : ℕ) : 𝓞 D.host.E) * o) • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) + o • F0.z := by
        rw [LinearMap.map_smul_of_tower, smul_sub,
          ← algebraMap_smul D.host.E (((Tu D u : ℕ) : 𝓞 D.host.E) * o) (t⁻¹ • F0.z), smul_smul, map_mul, map_natCast,
          ← algebraMap_smul D.host.E o F0.z]
        have : (t * algebraMap (𝓞 D.host.E) D.host.E o * t⁻¹) = algebraMap (𝓞 D.host.E) D.host.E o := by
          field_simp
        rw [this]
        abel
      rw [this]
      exact B.add_mem (B.smul_mem _ hK1) (Submodule.mem_sup_left (Λ.smul_mem _ hzΛ))

end Lat

end Formalism.MainNotions.BridgeLemma₂

end
end
end


-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LatDetSqOfCyclicDualQuotient, Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeStructureOfDet, Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MassLowerBoundOfMassFormula, Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus

-- ===== clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LatDetSqOfCyclicDualQuotient =====
-- clump-header: {"m": "Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LatDetSqOfCyclicDualQuotient", "h": "module\n\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro\nimport Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.LatticeGluingRadicals

section Loc

variable {E : Type} [Field E] [NumberField E]

theorem exists_not_mem_mul_mem_span {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {t : 𝓞 E} (ht : t ∈ P) (ht2 : t ∉ P ^ 2) :
    ∃ c : 𝓞 E, c ∉ P ∧ ∀ x ∈ P, c * x ∈ Ideal.span {t} := by
  have hle : Ideal.span {t} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 ht
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hle
  have hIP : ¬ I ≤ P := by
    intro h
    apply ht2
    have h2 : Ideal.span {t} ≤ P ^ 2 := by
      rw [hI, pow_two]
      exact Ideal.mul_mono_right h
    exact h2 (Ideal.subset_span (Set.mem_singleton t))
  obtain ⟨c, hcI, hcP⟩ := SetLike.not_le_iff_exists.mp hIP
  refine ⟨c, hcP, fun x hx => ?_⟩
  rw [hI, mul_comm c x]
  exact Ideal.mul_mem_mul hx hcI

def quotientSpanToQuotientPrime (P : Ideal (𝓞 E)) (t : 𝓞 E) (ht : t ∈ P) : (𝓞 E ⧸ Ideal.span {t}) →ₗ[𝓞 E] (𝓞 E ⧸ P) :=
  Submodule.mapQ (Ideal.span {t}) P LinearMap.id ((Ideal.span_singleton_le_iff_mem _).2 ht)

theorem isLocalizedModule_quotient_prime {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {t : 𝓞 E} (ht : t ∈ P) (ht2 : t ∉ P ^ 2) :
    haveI := hP.isPrime
    IsLocalizedModule P.primeCompl (quotientSpanToQuotientPrime P t ht) := by
  constructor
  · intro s
    have hs : (s : 𝓞 E) ∉ P := s.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro y1 y2 h
      obtain ⟨a1, rfl⟩ := Submodule.Quotient.mk_surjective P y1
      obtain ⟨a2, rfl⟩ := Submodule.Quotient.mk_surjective P y2
      simp only [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h ⊢
      rw [← smul_sub, smul_eq_mul] at h
      exact (hP.isPrime.mem_or_mem h).resolve_left hs
    · intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P y
      obtain ⟨b, i, hi, hb⟩ := hP.exists_inv hs
      refine ⟨Submodule.Quotient.mk (b * a), ?_⟩
      simp only [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]
      have e : (s : 𝓞 E) * (b * a) - a = -(i * a) := by linear_combination a * hb
      rw [e]
      exact P.neg_mem (P.mul_mem_right a hi)
  · intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P y
    exact ⟨(Submodule.Quotient.mk a, 1), by simp [quotientSpanToQuotientPrime]⟩
  · intro x1 x2 h
    obtain ⟨a1, rfl⟩ := Submodule.Quotient.mk_surjective _ x1
    obtain ⟨a2, rfl⟩ := Submodule.Quotient.mk_surjective _ x2
    simp only [quotientSpanToQuotientPrime, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq] at h
    obtain ⟨c, hcP, hc⟩ := exists_not_mem_mul_mem_span hP ht ht2
    refine ⟨⟨c, hcP⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def]
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← smul_sub, smul_eq_mul]
    exact hc _ h

end Loc

section Idx

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem localLength_cyclic_mem {A B : Submodule (𝓞 E) S.V} {t : 𝓞 E}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {t})) (P : Ideal (𝓞 E)) (hP : P.IsMaximal) (ht : t ∈ P)
    (ht2 : t ∉ P ^ 2) : haveI := hP.isPrime; Formalism.HermitianLatticesTheory.locLen P A B = 1 := by
  have := hP.isPrime
  unfold Formalism.HermitianLatticesTheory.locLen
  have := isLocalizedModule_quotient_prime hP ht ht2
  have eq := IsLocalizedModule.linearEquiv P.primeCompl (i_g P A B) (quotientSpanToQuotientPrime P t ht ∘ₗ e.toLinearMap)
  rw [eq.length_eq]
  have : IsSimpleModule (𝓞 E) (𝓞 E ⧸ P) := isSimpleModule_iff_isCoatom.2 hP.out
  rw [Module.length_eq_one]
  rfl

theorem localLength_cyclic_not_mem {A B : Submodule (𝓞 E) S.V} {t : 𝓞 E}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {t})) (P : Ideal (𝓞 E)) [P.IsPrime] (ht : t ∉ P) :
    Formalism.HermitianLatticesTheory.locLen P A B = 0 := by
  have htA : ∀ x ∈ A, t • x ∈ B := by
    intro x hx
    have h1 : e (Submodule.Quotient.mk (t • (⟨x, hx⟩ : A))) = 0 := by
      rw [Submodule.Quotient.mk_smul, map_smul]
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨x, hx⟩))
      rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self t)
    have h2 := (LinearEquiv.map_eq_zero_iff e).mp h1
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h2
    exact h2
  have hsub : Subsingleton ((Formalism.HermitianLatticesTheory.localization₂ P A) ⧸ (Formalism.HermitianLatticesTheory.localization₂ P B).comap (Formalism.HermitianLatticesTheory.localization₂ P A).subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : ∃ s ∈ P.primeCompl, s • x ∈ A := hx
    obtain ⟨s, hs, hsx⟩ := hx'
    show ∃ s ∈ P.primeCompl, s • x ∈ B
    refine ⟨t * s, Ideal.mem_primeCompl_iff.mpr fun h => ?_, ?_⟩
    · rcases ‹P.IsPrime›.mem_or_mem h with h | h
      · exact ht h
      · exact Ideal.mem_primeCompl_iff.mp hs h
    · rw [mul_smul]
      exact htA _ hsx
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [Module.length_eq_zero_iff.mpr hsub]
  rfl

theorem genIdx_cyclic_split_prime {A B : Submodule (𝓞 E) S.V} (hBA : B ≤ A) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl E T)
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)})) :
    genIdxH A B = (T : ℝ) ^ finrank ℚ E := by
  unfold genIdxH
  have h1 : ∀ P : HeightOneSpectrum (𝓞 E),
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.lidx P.asIdeal A B) =
        ∏ᶠ (_ : P ∈ plOver E T), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) := by
    intro P
    classical
    have := P.isPrime
    rw [i_lidx_of_le P.asIdeal hBA]
    by_cases hP : P ∈ plOver E T
    · have hmax := P.isPrime.isMaximal P.ne_bot
      rw [finprod_eq_if, ite_eq_left hP, localLength_cyclic_mem e P.asIdeal hmax hP (hs P.asIdeal hmax hP).2]
      simp
    · rw [finprod_eq_if, ite_eq_right hP, localLength_cyclic_not_mem e P.asIdeal hP]
      simp
  rw [finprod_congr h1]
  exact finprod_plOver E hT hs id

theorem latDet_sq_of_cyclic_dual_quotient (M : Submodule (𝓞 E) S.V) (hl : Submodule.IsLattice E M)
    (hint : M ≤ Formalism.HermitianLatticesTheory.dual S.hT M) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl E T) (w₁ : S.V)
    (hw : w₁ ∈ Formalism.HermitianLatticesTheory.dual S.hT M) (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual S.hT M, ∃ a : 𝓞 E, w + a • w₁ ∈ M)
    (hker : ∀ a : 𝓞 E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 E) ∣ a) :
    latDetH S.hT M = Real.sqrt ((T : ℝ) ^ finrank ℚ E) := by
  have hA : Formalism.HermitianLatticesTheory.dual S.hT M ⊓ Submodule.restrictScalars (𝓞 E) (Submodule.span E (M : Set S.V)) =
      Formalism.HermitianLatticesTheory.dual S.hT M := by
    apply inf_eq_left.mpr
    intro w hw'
    change w ∈ Submodule.span E (M : Set S.V)
    have hw₁ : w₁ ∈ Submodule.span E (M : Set S.V) := by
      have hm : ((T : ℕ) : 𝓞 E) • w₁ ∈ M := (hker _).2 (dvd_refl _)
      have hs : ((T : ℕ) : E) • w₁ ∈ Submodule.span E (M : Set S.V) := by
        have hm' : ((T : ℕ) : 𝓞 E) • w₁ ∈ Submodule.span E (M : Set S.V) := Submodule.subset_span hm
        simpa only [Nat.cast_smul_eq_nsmul] using hm'
      have hn : ((T : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne_zero
      simpa only [inv_smul_smul₀ hn] using
        (Submodule.span E (M : Set S.V)).smul_mem (((T : ℕ) : E)⁻¹) hs
    obtain ⟨a, ha⟩ := hgen w hw'
    have ha' : w + a • w₁ ∈ Submodule.span E (M : Set S.V) := Submodule.subset_span ha
    have hs : a • w₁ ∈ Submodule.span E (M : Set S.V) := by
      simpa only [IsScalarTower.algebraMap_smul] using
        (Submodule.span E (M : Set S.V)).smul_mem (algebraMap (𝓞 E) E a) hw₁
    simpa only [add_sub_cancel_right] using (Submodule.span E (M : Set S.V)).sub_mem ha' hs
  have hφ : ∀ a : 𝓞 E, LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩) a =
      Submodule.Quotient.mk ⟨a • w₁, (Formalism.HermitianLatticesTheory.dual S.hT M).smul_mem a hw⟩ := by
    intro a
    rw [LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul]
    rfl
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩)) := by
    intro y
    obtain ⟨⟨w, hwA⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨a, ha⟩ := hgen w hwA
    refine ⟨-a, ?_⟩
    rw [hφ, Submodule.Quotient.eq, Submodule.mem_comap, map_sub, Submodule.subtype_apply,
      Submodule.subtype_apply]
    have h1 : -a • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
    rw [h1]
    exact M.neg_mem ha
  have hK : LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩)) =
      Ideal.span {((T : ℕ) : 𝓞 E)} := by
    ext a
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Ideal.mem_span_singleton]
    exact hker a
  unfold latDetH dualInH
  rw [hA]
  congr 1
  exact genIdx_cyclic_split_prime hint hT hs
    ((Submodule.quotEquivOfEq _ _ hK).symm.trans (LinearMap.quotKerEquivOfSurjective _ hsurj)).symm

end Idx

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latDet_of_cyclic_dual_quotient (D : D7) (M : Submodule (𝓞 D.host.E) (D.sp.X 0).V) (hl : Submodule.IsLattice D.host.E M)
    (hint : M ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl D.host.E T)
    (w₁ : (D.sp.X 0).V) (hw : w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M)
    (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M, ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ M)
    (hker : ∀ a : 𝓞 D.host.E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 D.host.E) ∣ a) :
    latDetH (D.sp.X 0).hT M = ((T ^ D.R.f : ℕ) : ℝ) := by
  rw [latDet_sq_of_cyclic_dual_quotient M hl hint hT hs w₁ hw hgen hker, _root_.Formalism.MainNotions.StandardLattice.finrank_host, pow_mul',
    Real.sqrt_sq (by positivity)]
  norm_cast

end Record

end Formalism.MainNotions.BridgeLemma₂

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LatDetSqOfCyclicDualQuotient =====

-- ===== clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeStructureOfDet =====
-- clump-header: {"m": "Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeStructureOfDet", "h": "module\n\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InnerMemOneOfMemDualOrthLattice\nimport Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MemSupIsotropicOfDualPairing\nimport Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeIsIntegralOfUnimodular\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cyc

variable {D : D7} {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
  [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
  (M : Submodule (𝓞 D.host.E) V) (T : ℕ) (w₁ : V) (hw₁ : w₁ ∈ Formalism.HermitianLatticesTheory.dual h M)
  (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual h M, ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ M)
  (hann : ∀ a : 𝓞 D.host.E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 D.host.E) ∣ a)


include hw₁ hgen in
theorem discriminant_one_generator : DiscGen h M 1 := by
  refine ⟨{Submodule.Quotient.mk ⟨w₁, hw₁⟩}, by simp, ?_⟩
  rw [eq_top_iff, Finset.coe_singleton]
  intro q _
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨a, ha⟩ := hgen w hw
  refine Submodule.mem_span_singleton.2 ⟨-a, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
  show (-a) • w₁ - w ∈ M
  have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
  rw [e]
  exact M.neg_mem ha


include hw₁ hgen hann in
theorem corank_one_mod_prime_over (p : Ideal (𝓞 D.host.F)) (hp : p.IsMaximal) (hTp : ((T : ℕ) : 𝓞 D.host.F) ∈ p) :
    eP h M p = 1 := by
  set P : Ideal (𝓞 D.host.E) := pE D.host.F D.host.E p with hP
  set Md := Formalism.HermitianLatticesTheory.dual h M with hMd
  set K : Submodule (𝓞 D.host.E) Md := (M ⊔ P • Md).comap Md.subtype with hK
  have hTP : ((T : ℕ) : 𝓞 D.host.E) ∈ P := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hTp
    rw [map_natCast] at this
    exact this
  have hstep : ∀ n ∈ P • Md, ∃ b ∈ P, n - b • w₁ ∈ M := by
    intro n hn
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro r hr w hw
      obtain ⟨c, hc⟩ := hgen w hw
      refine ⟨-(r * c), P.neg_mem (P.mul_mem_right _ hr), ?_⟩
      have e : r • w - (-(r * c)) • w₁ = r • (w + c • w₁) := by
        rw [neg_smul, sub_neg_eq_add, smul_add, mul_smul]
      rw [e]
      exact M.smul_mem _ hc
    · rintro x y ⟨b, hb, hx⟩ ⟨b', hb', hy⟩
      refine ⟨b + b', P.add_mem hb hb', ?_⟩
      have e : x + y - (b + b') • w₁ = (x - b • w₁) + (y - b' • w₁) := by rw [add_smul]; abel
      rw [e]
      exact M.add_mem hx hy
  set φ : 𝓞 D.host.E →ₗ[𝓞 D.host.E] (Md ⧸ K) :=
    LinearMap.toSpanSingleton (𝓞 D.host.E) (Md ⧸ K) (Submodule.Quotient.mk ⟨w₁, hw₁⟩) with hφ
  have hφa : ∀ a, φ a = Submodule.Quotient.mk (a • (⟨w₁, hw₁⟩ : Md)) := fun a => by
    rw [hφ, LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_smul]
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha⟩ := hgen w hw
    refine ⟨-a, ?_⟩
    rw [hφa, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, Submodule.mem_comap]
    show (-a) • w₁ - w ∈ M ⊔ P • Md
    have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
    rw [e]
    exact Submodule.mem_sup_left (M.neg_mem ha)
  have hker : LinearMap.ker φ = P := by
    ext a
    rw [LinearMap.mem_ker, hφa, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_comap]
    show a • w₁ ∈ M ⊔ P • Md ↔ a ∈ P
    constructor
    · intro ha
      obtain ⟨m, hm, n, hn, e⟩ := Submodule.mem_sup.1 ha
      obtain ⟨b, hb, hnb⟩ := hstep n hn
      have h1 : (a - b) • w₁ ∈ M := by
        have : (a - b) • w₁ = m + (n - b • w₁) := by rw [sub_smul, ← e]; abel
        rw [this]
        exact M.add_mem hm hnb
      obtain ⟨o, ho⟩ := (hann _).1 h1
      have : a = ((T : ℕ) : 𝓞 D.host.E) * o + b := by rw [← ho]; ring
      rw [this]
      exact P.add_mem (P.mul_mem_right _ hTP) hb
    · intro ha
      exact Submodule.mem_sup_right (Submodule.smul_mem_smul ha hw₁)
  have hcard : Nat.card (Md ⧸ K) = Ideal.absNorm p ^ 2 := by
    rw [← Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv,
      Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv, ← Formalism.MainNotions.BridgeLemma.absNorm_pE]
    exact (Ideal.absNorm_eq_natCard P).symm
  have hq := Formalism.MainNotions.BridgeLemma.absNorm_ge_two p hp
  show Nat.log (Ideal.absNorm p ^ 2) (Nat.card (Md ⧸ K)) = 1
  rw [hcard]
  have := Nat.log_pow (b := Ideal.absNorm p ^ 2) (by nlinarith) 1
  rwa [pow_one] at this

end Cyc

theorem orthLattice_structure_of_det (D : D7) (u : D.what₂.Word)
    (hdet : ForPrimeFlagLattice D u fun F0 Λ =>
      latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ)) : BaseLatticeStructure D u := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  exact ⟨orthLattice_isLattice F0 he hz Λ hΛ hu, orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu, hdet hTp h3 hsp F0 he hz Λ hrow,
    discriminant_one_generator _ _ w₁ hw₁ hgen, fun p hp hTpp => corank_one_mod_prime_over _ _ (Tu D u) w₁ hw₁ hgen hann p hp hTpp⟩

end Formalism.MainNotions.BridgeLemma₂

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeStructureOfDet =====

-- ===== clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MassLowerBoundOfMassFormula =====
-- clump-header: {"m": "Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MassLowerBoundOfMassFormula", "h": "module\n\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InnerMemOneOfMemDualOrthLattice\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LatDetSqOfCyclicDualQuotient\nimport Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MemSupIsotropicOfDualPairing\nimport Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeIsIntegralOfUnimodular\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeStructureOfDet\nimport Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_orthLattice_eq_pow (D : D7) (u : D.what₂.Word) :
    ForPrimeFlagLattice D u fun F0 Λ => latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ) := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  refine latDet_of_cyclic_dual_quotient D _ (orthLattice_isLattice F0 he hz Λ hΛ hu) ?_ hTp hsp w₁ hw₁ hgen hann
  intro x hx
  exact (i_mem_dual _ _).2 fun y hy => orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu y hy x hx

theorem orthLattice_structure (D : D7) (u : D.what₂.Word) : BaseLatticeStructure D u := orthLattice_structure_of_det D u (det_orthLattice_eq_pow D u)

theorem orth_space_posDef (D : D7) (u : D.what₂.Word) (hT : 0 < Tu D u) : IsPosDef (D.sp.X 0).hT :=
  orth_space_posDef_every_place (Formalism.MainNotions.S.Inh.tie_flag0 D u) rfl rfl hT

end Formalism.MainNotions.BridgeLemma₂

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MassLowerBoundOfMassFormula =====

-- ===== clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus =====
-- clump-header: {"m": "Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus", "h": "module\n\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.AutomorphismsOfLiftTransitivity\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MassLowerBoundOfMassFormula\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gluing_mass_of_lift_number_genus (D : D7) (u : D.what₂.Word) (hL : LiftsConjugateUnderStabilizer D u) (h4 : GluingNumber D u)
    (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u := by
  intro hT
  exact gluing_mass_of_lift_and_number D u (orth_space_posDef D u hT.pos)
    (fun hT h3 hsp F0 he hz Λ hΛ => (orthLattice_structure D u hT h3 hsp F0 he hz Λ hΛ).1) hL h4 h5 hT

end Formalism.MainNotions.BridgeLemma₂

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus =====
