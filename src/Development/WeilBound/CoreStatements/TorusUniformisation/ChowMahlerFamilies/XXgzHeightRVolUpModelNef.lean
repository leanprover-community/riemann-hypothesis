import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight

namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ZH GlobalTheory.ZH.RatModel

theorem isNef_of_small {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (L : HermLB p) (hs : L.SemiPos D) {ι : Type} [Finite ι] (u : ι → L.B.Sec) (hu : ∀ i, u i ∈ L.smallSec)
    (hg : ⨆ i, nonzeroLocus (u i) = ⊤) : L.IsNef D where
  semiPos := hs
  vertical := GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated hX L (isGenerated_of_finite u hg)
  horizontal Z i _ _ _ hc hd := by
    have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
    have hm : i (genericPoint Z) ∈ ⨆ a, nonzeroLocus (u a) := by rw [hg]; trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.1 hm
    have hgen : genericPoint Z ∈ nonzeroLocus (GlobalTheory.secPull (u a) i) := by
      rw [GlobalTheory.nonzeroLocus_secPull]; exact ha
    have h0 : ∀ σ (y : CxPts (i ≫ p) σ), y ∈ ptsIn _ σ (nonzeroLocus (GlobalTheory.secPull (u a) i)) := fun σ y => by
      refine mem_ptsIn.2 ?_
      have key : ∀ y : Sp ℂ ⟶ Z, y (IsLocalRing.closedPoint ℂ) = genericPoint Z := fun y =>
        GlobalTheory.HtSelfInter.eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero
      rw [key]
      exact hgen
    refine ⟨_, isRatSec_ratOfSec _ hgen, ?_⟩
    rw [HermLB.curveDeg_sec i (u a) hgen h0]
    refine sub_nonneg.2 (le_trans (b := 0) ?_ ?_)
    · refine finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun σ =>
        finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun y => ?_
      refine div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos ?_ (hu a σ _)) zero_le_two
      unfold Weight.nsq
      positivity
    · exact finsum_nonneg fun z =>
        mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg z)) (Real.log_natCast_nonneg _)

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
  {M : RatModel (𝓞 K) Ω}

theorem const_val {σ : K →+* ℂ} {y : Sp ℂ ⟶ M.Z} (hy : y ≫ M.s = spMap (σ.comp (algebraMap (𝓞 K) K))) (a : K) :
    algebraMap K Ω a ∈ M.O (y (IsLocalRing.closedPoint ℂ)) ∧ M.val y (algebraMap K Ω a) = σ a := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hr := range_eq_singleton y (IsLocalRing.closedPoint ℂ)
  have hq0 : algebraMap (𝓞 K) K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hσq : σ (algebraMap (𝓞 K) K q) ≠ 0 := (map_ne_zero σ).2 hq0
  have hv := fun c => val_algebraMap hy c
  have hu : IsUnit (⟨algebraMap (𝓞 K) Ω q, Subalgebra.algebraMap_mem _ q⟩ :
      M.O (y (IsLocalRing.closedPoint ℂ))) := (val_ne_zero_iff hr _).1 (by rw [hv]; exact hσq)
  obtain ⟨h0, hi⟩ := (isUnit_O_iff _).1 hu
  dsimp only at h0 hi
  have e : algebraMap K Ω (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) =
      algebraMap (𝓞 K) Ω p * (algebraMap (𝓞 K) Ω q)⁻¹ := by
    rw [map_div₀, div_eq_mul_inv, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hm : algebraMap (𝓞 K) Ω p * (algebraMap (𝓞 K) Ω q)⁻¹ ∈ M.O (y (IsLocalRing.closedPoint ℂ)) :=
    mul_mem (Subalgebra.algebraMap_mem _ p) hi
  rw [e]
  refine ⟨hm, ?_⟩
  have h1 := val_mul (specializes_of_range_eq hr) hm (Subalgebra.algebraMap_mem _ q)
  rw [inv_mul_cancel_right₀ h0, hv, hv] at h1
  rw [map_div₀, eq_div_iff hσq]
  exact h1.symm

theorem exists_coord {σ : K →+* ℂ} {y : Sp ℂ ⟶ M.Z} (hy : y ≫ M.s = spMap (σ.comp (algebraMap (𝓞 K) K)))
    (ev : V →ₗ[K] Ω) (c : Ω) {N : ℕ} (b : Module.Basis (Fin N) K V) {S : Set V} (hS : Submodule.span K S = ⊤)
    (hc : ∀ v ∈ S, ev v / c ∈ M.O (y (IsLocalRing.closedPoint ℂ))) :
    ∃ x : Fin N → ℂ, ∀ v, M.val y (ev v / c) = ∑ j, σ (b.repr v j) * x j := by
  have hr := specializes_of_range_eq (range_eq_singleton y (IsLocalRing.closedPoint ℂ))
  have hsm : ∀ (a : K) v, ev (a • v) / c = algebraMap K Ω a * (ev v / c) := fun a v => by
    rw [map_smul, Algebra.smul_def, mul_div_assoc]
  have hall : ∀ v, ev v / c ∈ M.O (y (IsLocalRing.closedPoint ℂ)) := fun v => by
    have hv : v ∈ Submodule.span K S := hS ▸ trivial
    induction hv using Submodule.span_induction with
    | mem _ h => exact hc _ h
    | zero => rw [map_zero, zero_div]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add, add_div]; exact add_mem ha hb
    | smul a v _ hv => rw [hsm]; exact mul_mem (const_val hy a).1 hv
  let ℓ : V →+ ℂ :=
    { toFun := fun v => M.val y (ev v / c)
      map_zero' := by rw [map_zero, zero_div]; exact val_zero y
      map_add' := fun a b => by rw [map_add, add_div]; exact val_add hr (hall a) (hall b) }
  refine ⟨fun j => ℓ (b j), fun v => ?_⟩
  change ℓ v = _
  conv_lhs => rw [← b.sum_repr v, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change M.val y _ = _
  rw [hsm, val_mul hr (const_val hy _).1 (hall _), (const_val hy _).2]
  rfl

omit [NumberField K] in

theorem mem_O_of_span [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (ev : V →ₗ[K] Ω) (c : Ω) {z : M.Z} {S : Set V}
    (hc : ∀ v ∈ S, ev v / c ∈ M.O z) {v : V} (hv : v ∈ Submodule.span (𝓞 K) S) : ev v / c ∈ M.O z := by
  induction hv using Submodule.span_induction with
  | mem _ h => exact hc _ h
  | zero => rw [map_zero, zero_div]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add, add_div]; exact add_mem ha hb
  | smul a v _ hv =>
    rw [← algebraMap_smul K a v, map_smul, Algebra.smul_def, mul_div_assoc, ← IsScalarTower.algebraMap_apply]
    exact mul_mem (Subalgebra.algebraMap_mem _ a) hv

omit [NumberField K] in

theorem exists_isUnit (ev : V →ₗ[K] Ω) (c : Ω) {z : M.Z} {ι : Type} (w : ι → V)
    (hc : ∀ i, ev (w i) / c ∈ M.O z) {v : V} (hv : v ∈ Submodule.span ℤ (Set.range w)) (h : ev v / c ∈ M.O z)
    (hu : IsUnit (⟨_, h⟩ : M.O z)) : ∃ i, IsUnit (⟨_, hc i⟩ : M.O z) := by
  by_contra hn
  have key : ∃ a ∈ IsLocalRing.maximalIdeal (M.O z), (a : Ω) = ev v / c := by
    clear hu h
    induction hv using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact ⟨⟨_, hc i⟩, fun h => hn ⟨i, h⟩, rfl⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha, ea⟩ := ha
      obtain ⟨b', hb, eb⟩ := hb
      exact ⟨a' + b', add_mem ha hb, by rw [map_add, add_div, ← ea, ← eb]; rfl⟩
    | smul n a _ ha =>
      obtain ⟨a', ha, ea⟩ := ha
      refine ⟨n • a', zsmul_mem ha n, ?_⟩
      rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul, mul_div_assoc, ← ea]
      simp
  obtain ⟨a, ha, ea⟩ := key
  obtain rfl : a = ⟨_, h⟩ := Subtype.ext ea
  exact ha hu

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

