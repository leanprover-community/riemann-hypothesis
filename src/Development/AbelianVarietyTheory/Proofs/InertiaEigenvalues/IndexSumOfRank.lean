import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableAbsNormRpowHeightOneSpectrum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLatticeIndexSumLeZetaSqSubOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualSumLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasing
import ReciprocityTheory.ResidueCardinality.ArtinOntoB
import Formalism.SatakeDualWeyl.Statement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem one_sub_sum_le_prod_one_sub_range (x : ℕ → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1)
    (r : ℕ) : 1 - ∑ i ∈ Finset.range r, x i ≤ ∏ i ∈ Finset.range r, (1 - x i) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hS : 0 ≤ ∑ i ∈ Finset.range n, x i := Finset.sum_nonneg (fun i _ => h0 i)
    have hx1 : 0 ≤ 1 - x n := by linarith [h1 n]
    have := mul_le_mul_of_nonneg_right ih hx1
    nlinarith [h0 n]

theorem sum_rpow_sub_le (q : ℝ) (r : ℕ) (σ : ℝ) (hq : 2 ≤ q) (hσ : (r : ℝ) + 5 / 2 ≤ σ) :
    ∑ i ∈ Finset.range r, q ^ ((i : ℝ) - σ) ≤ 2 / q ^ 3 := by
  have hq0 : 0 < q := by linarith
  have hterm : ∀ i : ℕ, q ^ ((i : ℝ) - σ) = q ^ i / q ^ σ := by
    intro i; rw [Real.rpow_sub hq0, Real.rpow_natCast]
  simp_rw [hterm]
  rw [← Finset.sum_div, geom_sum_eq (by linarith : q ≠ 1)]
  have hqs : 0 < q ^ σ := Real.rpow_pos_of_pos hq0 σ
  have hrs : q ^ r / q ^ σ ≤ 1 / q ^ 2 := by
    have h1 : q ^ r / q ^ σ = q ^ ((r : ℝ) - σ) := by rw [Real.rpow_sub hq0, Real.rpow_natCast]
    have h2 : q ^ ((r : ℝ) - σ) ≤ q ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : q ^ (-2 : ℝ) = 1 / q ^ 2 := by
      rw [Real.rpow_neg hq0.le]; norm_num
    rw [h1]; linarith
  have hq1 : 0 < q - 1 := by linarith
  have hpr : 0 < q ^ r := pow_pos hq0 r
  calc (q ^ r - 1) / (q - 1) / q ^ σ ≤ q ^ r / (q - 1) / q ^ σ := by
        gcongr; linarith
    _ = (q ^ r / q ^ σ) / (q - 1) := by ring
    _ ≤ (1 / q ^ 2) / (q - 1) := by gcongr
    _ ≤ 2 / q ^ 3 := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos hq0 2, pow_pos hq0 3]

theorem lattice_zeta_sq_bound : ∀ (q : ℝ) (r : ℕ) (σ : ℝ), 2 ≤ q → (r : ℝ) + 5 / 2 ≤ σ →
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 < 1 ∧
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 ≤ 16 * q ^ (-(3 : ℝ)) := by
  intro q r σ hq hσ
  have hq0 : 0 < q := by linarith
  set x : ℕ → ℝ := fun i => q ^ ((i : ℝ) - σ) with hx
  have hS := sum_rpow_sub_le q r σ hq hσ
  have hq3 : 8 ≤ q ^ 3 := by nlinarith [sq_nonneg q, mul_le_mul hq hq (by norm_num) hq0.le]
  set w : ℝ := 1 / q ^ 3 with hw
  have hw0 : 0 < w := by positivity
  have hw8 : w ≤ 1 / 8 := by
    rw [hw]; exact one_div_le_one_div_of_le (by norm_num) hq3
  have h0 : ∀ i, 0 ≤ x i := fun i => (Real.rpow_pos_of_pos hq0 _).le

  have hD := one_sub_sum_le_prod_one_sub_range (fun i => min (x i) 1)
    (fun i => le_min (h0 i) zero_le_one) (fun i => min_le_right _ _) r
  have hmin : ∀ i ∈ Finset.range r, min (x i) 1 = x i := by
    intro i hi
    apply min_eq_left
    have : x i ≤ ∑ j ∈ Finset.range r, x j :=
      Finset.single_le_sum (fun j _ => h0 j) hi
    have : 2 / q ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  rw [Finset.sum_congr rfl hmin, Finset.prod_congr rfl (fun i hi => by rw [hmin i hi])] at hD
  set D := ∏ i ∈ Finset.range r, (1 - x i) with hDdef
  have h2w : 2 / q ^ 3 = 2 * w := by rw [hw]; ring
  have hDlow : 1 - 2 * w ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hP : ∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹ = D⁻¹ := by
    rw [Finset.prod_inv_distrib]
  have hrhs : 16 * q ^ (-(3 : ℝ)) = 16 * w := by
    rw [Real.rpow_neg hq0.le, hw]; norm_num
  rw [hP, hrhs]
  have ha : 0 < 1 - 2 * w := by linarith
  have hPle : D⁻¹ ≤ (1 - 2 * w)⁻¹ := inv_anti₀ ha hDlow
  have hP0 : 0 ≤ D⁻¹ := inv_nonneg.mpr hDpos.le
  have hsq : D⁻¹ ^ 2 ≤ ((1 - 2 * w)⁻¹) ^ 2 := pow_le_pow_left₀ hP0 hPle 2
  have hkey : ((1 - 2 * w)⁻¹) ^ 2 ≤ 1 + 16 * w := by
    rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  have hkey2 : ((1 - 2 * w)⁻¹) ^ 2 < 2 := by
    rw [inv_pow, inv_lt_iff_one_lt_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  constructor <;> linarith

end GlobalTheory
end

section
section
open Matrix

namespace GlobalTheory.GLintLattice

variable {K : Type} [Field K] (A : ValuationSubring K) {r : ℕ}

theorem mem_span_basisFun_iff (y : Fin r → K) :
    y ∈ Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔ ∀ i, y i ∈ A := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ i
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · intro h
    refine ⟨fun i => ⟨y i, h i⟩, ?_⟩
    ext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

theorem mulVec_maps_iff (M : Matrix (Fin r) (Fin r) K) :
    (∀ y : Fin r → K, (∀ i, y i ∈ A) → ∀ i, (M *ᵥ y) i ∈ A) ↔ ∀ i j, M i j ∈ A := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]) i
    simpa [Matrix.mulVec_single_one] using this
  · intro h y hy i
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem (fun j _ => mul_mem (h i j) (hy j))

theorem mem_GLint_iff (x : GL (Fin r) K) :
    x ∈ Formalism.UG.GLint (Fin r) A.toSubring ↔
      (∀ i j, (x : Matrix (Fin r) (Fin r) K) i j ∈ A) ∧
        (∀ i j, ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ∈ A) := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show ((u : Matrix (Fin r) (Fin r) A.toSubring) i j : K) ∈ A
      exact (u : Matrix (Fin r) (Fin r) A.toSubring) i j |>.2
    · rw [← map_inv]
      show (((u⁻¹ : GL (Fin r) A.toSubring) : Matrix (Fin r) (Fin r) A.toSubring) i j : K) ∈ A
      exact ((u⁻¹ : GL (Fin r) A.toSubring) : Matrix (Fin r) (Fin r) A.toSubring) i j |>.2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin r) (Fin r) A.toSubring := Matrix.of fun i j => ⟨_, h1 i j⟩
    let M' : Matrix (Fin r) (Fin r) A.toSubring := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map A.toSubring.subtype = (x : Matrix (Fin r) (Fin r) K) := by ext; rfl
    have hM' : M'.map A.toSubring.subtype = ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) := by
      ext; rfl
    have inj : Function.Injective fun N : Matrix (Fin r) (Fin r) A.toSubring => N.map A.toSubring.subtype :=
      Matrix.map_injective Subtype.val_injective
    have e1 : M * M' = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact x.mul_inv)
    have e2 : M' * M = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact x.inv_mul)
    refine ⟨⟨M, M', e1, e2⟩, ?_⟩
    ext i j
    rfl

theorem stdLattice_map_eq_iff_mem_GLint : ∀ (K : Type) [Field K] (A : ValuationSubring K) (r : ℕ)
    (x : GL (Fin r) K),
    (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
        ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) =
      Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔
    x ∈ Formalism.UG.GLint (Fin r) A.toSubring := by
  intro K _ A r x
  have hf : ∀ z, ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) z =
      (x : Matrix (Fin r) (Fin r) K) *ᵥ z := fun z => rfl
  have inv_x : ∀ z : Fin r → K, ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ
      ((x : Matrix (Fin r) (Fin r) K) *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have x_inv : ∀ z : Fin r → K, (x : Matrix (Fin r) (Fin r) K) *ᵥ
      (((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [mem_GLint_iff, ← mulVec_maps_iff, ← mulVec_maps_iff]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hm : (x : Matrix (Fin r) (Fin r) K) *ᵥ y ∈
          (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
            ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) :=
        ⟨y, (mem_span_basisFun_iff A y).2 hy, hf y⟩
      rw [h] at hm
      exact (mem_span_basisFun_iff A _).1 hm
    · have hm : y ∈ (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
            ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) := by
        rw [h]; exact (mem_span_basisFun_iff A y).2 hy
      obtain ⟨z, hz, hzy⟩ := hm
      rw [hf] at hzy
      rw [← hzy, inv_x]
      exact (mem_span_basisFun_iff A z).1 hz
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hf, mem_span_basisFun_iff]
      exact h1 z ((mem_span_basisFun_iff A z).1 hz)
    · intro y hy
      refine ⟨((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ y,
        (mem_span_basisFun_iff A _).2 (h2 y ((mem_span_basisFun_iff A y).1 hy)), ?_⟩
      rw [hf, x_inv]

end GlobalTheory.GLintLattice
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring : ∀ (K : Type) [Field K] (A : ValuationSubring K) (r : ℕ) (x : GL (Fin r) K), (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) = Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔ x ∈ Formalism.UG.GLint (Fin r) A.toSubring := by
  atlas_forward_decl GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint
end

section
namespace GlobalTheory

theorem index_transfer_along_projection {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (L : AddSubgroup M) (T p : M →+ M) (Φ : M →+ N) (h : N →+ N)
    (hpL : ∀ y ∈ L, p y ∈ L) (hTp : ∀ y, T (p y) = p (T y))
    (hT1 : ∀ y, T (y - p y) = y - p y) (hΦ : ∀ y, Φ y = 0 → p y = 0)
    (hΦT : ∀ y, Φ (T y) = h (Φ y)) :
    (L.map T).relIndex L = ((L.map Φ).map h).relIndex (L.map Φ) := by
  have key : ∀ y ∈ L, (y ∈ L.map T ↔ Φ y ∈ (L.map Φ).map h) := by
    intro y hy
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Φ x, ⟨x, hx, rfl⟩, (hΦT x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
      have h0 : Φ (T x - y) = 0 := by rw [map_sub, hΦT, hxy, sub_self]
      have hp : p (T x) = p y := by
        have := hΦ _ h0
        rwa [map_sub, sub_eq_zero] at this
      refine ⟨p x + (y - p y), L.add_mem (hpL x hx) (L.sub_mem hy (hpL y hy)), ?_⟩
      show T (p x + (y - p y)) = y
      rw [map_add, hT1, hTp, hp]
      abel
  let ψ : L →+ L.map Φ :=
    (Φ.comp L.subtype).codRestrict (L.map Φ) (fun x => ⟨x.1, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hc : (L.map T).addSubgroupOf L =
      (((L.map Φ).map h).addSubgroupOf (L.map Φ)).comap ψ := by
    ext ⟨y, hy⟩
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact key y hy
  unfold AddSubgroup.relIndex
  rw [hc, AddSubgroup.index_comap_of_surjective _ hψ]

end GlobalTheory
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.InertLatIndex

open GlobalTheory.InertLoc Formalism.UG

theorem finPart_surjective (D : D7) : Function.Surjective (finPart D) := by
  intro b
  obtain ⟨a, ha⟩ := Algebra.TensorProduct.map_surjective (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    (fun b => ⟨pairA D.host.F 0 b, rfl⟩) Function.surjective_id b
  exact ⟨a, ha⟩

theorem ker_finPart_le {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} {σ : LP D P →+* LP D P}
    {π : AE D →+* LP D P} (hC : Chart e σ π) : RingHom.ker (finPart D) ≤ RingHom.ker π := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  refine (hC.2.2.1 a).2 ?_
  refine GlobalTheory.LatVac.tensor_prod_eq_zero (F := D.host.F) (A := _) (B := _) _ ?_ ?_
  · show infPart D (e * a) = 0
    rw [map_mul, hC.1.2.2, zero_mul]
  · show finPart D (e * a) = 0
    rw [map_mul, ha, mul_zero]

theorem mem_span_basisFun {K : Type} [Field K] (O : ValuationSubring K) {n : Type} [Fintype n] [DecidableEq n]
    (z : n → K) : z ∈ Submodule.span O (Set.range (Pi.basisFun K n)) ↔ ∀ i, z i ∈ O := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [Pi.basisFun_apply]
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, Ne.symm hij]
    | zero => intro i; simp
    | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
    | smul a x _ hx => intro i; exact mul_mem a.2 (hx i)
  · intro hz
    have : z = ∑ i, (⟨z i, hz i⟩ : O) • Pi.basisFun K n i := by
      conv_lhs => rw [← (Pi.basisFun K n).sum_repr z]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem finMat_apply {D : D7} {W : HSp D} (x : GA D W) (i j : Fin W.rank) :
    finMat D.sp.cm.sig W.gram x i j = finPart D (Formalism.L2.Theta.mt W x i j) := rfl

theorem finMat_sub_one_eq {D : D7} {W : HSp D} {e : AE D} (x : GA D W) (hx : SuppF W e x) (i j : Fin W.rank) :
    finMat D.sp.cm.sig W.gram x i j - (1 : Matrix (Fin W.rank) (Fin W.rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j =
      finPart D e * (finMat D.sp.cm.sig W.gram x i j - (1 : Matrix (Fin W.rank) (Fin W.rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j) := by
  have h1ij : (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j =
      finPart D ((1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i j) := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [h1ij, finMat_apply, ← RingHom.map_sub, ← RingHom.map_mul, ← Matrix.sub_apply, hx i j]

theorem finMat_mulVec_fix {D : D7} {W : HSp D} {e : AE D} (x : GA D W) (hx : SuppF W e x)
    (y : Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    finMat D.sp.cm.sig W.gram x *ᵥ (y - finPart D e • y) = y - finPart D e • y := by
  funext i
  have key : ∀ j, finMat D.sp.cm.sig W.gram x i j * (y - finPart D e • y) j =
      (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j *
        (y - finPart D e • y) j := by
    intro j
    have := finMat_sub_one_eq x hx i j
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (y j) * this
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp [Matrix.one_apply]

theorem inv_mulVec_conj {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] (β g : GL n K) (w : n → K) :
    (β⁻¹).1 *ᵥ ((β.1 * g.1 * (β⁻¹).1) *ᵥ w) = g.1 *ᵥ ((β⁻¹).1 *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

set_option maxHeartbeats 1000000 in

theorem latIndex_eq_of_chart {D : D7} {W : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D}
    {σ : LP D P →+* LP D P} {π : AE D →+* LP D P} {β : GL (Fin W.rank) (LP D P)}
    (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (hα : finPart D e = α ⊗ₜ[D.host.F] (1 : D.host.E))
    (hαint : ∀ a ∈ intAf D.host.F, α * a ∈ intAf D.host.F)
    (hC : Chart e σ π) (hF : Frame W e σ π β) (x : GA D W) (hx : SuppF W e x) (g : GL (Fin W.rank) (LP D P))
    (hxg : (Formalism.L2.Theta.mt W x).map π = β.1 * g.1 * (β⁻¹).1) :
    latIndex W x = ((Submodule.span (P.adicCompletionIntegers D.host.E)
        (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).map
        ((g.1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.restrictScalars
          (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex
      (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).toAddSubgroup := by
  let πf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* LP D P :=
    (RingHom.liftOfSurjective (finPart D) (finPart_surjective D)) ⟨π, ker_finPart_le hC⟩
  have hπf : ∀ a, πf (finPart D a) = π a := fun a => RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hπe : π e = 1 := by
    have h0 : e * (e - 1) = 0 := by rw [mul_sub, hC.1.1, mul_one, sub_self]
    have := (hC.2.2.1 (e - 1)).2 h0
    rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
  let T : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finMat D.sp.cm.sig W.gram x).mulVecLin.toAddMonoidHom
  let p : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := DistribMulAction.toAddMonoidHom _ (finPart D e)
  let Φ : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin W.rank → LP D P) :=
    ((β⁻¹).1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.toAddMonoidHom.comp
      (πf.toAddMonoidHom.compLeft (Fin W.rank))
  let h : (Fin W.rank → LP D P) →+ (Fin W.rank → LP D P) :=
    ((g.1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.restrictScalars
      (P.adicCompletionIntegers D.host.E)).toAddMonoidHom
  have hΦ : ∀ y, Φ y = (β⁻¹).1 *ᵥ (fun k => πf (y k)) := fun y => rfl
  have h1 : ∀ y ∈ Formalism.L2.NTheta.LamHat W, p y ∈ Formalism.L2.NTheta.LamHat W := by
    have hle : Formalism.L2.NTheta.LamHat W ≤ (Formalism.L2.NTheta.LamHat W).comap p := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, z, hz, rfl⟩
      show p _ ∈ Formalism.L2.NTheta.LamHat W
      apply AddSubgroup.subset_closure
      refine ⟨α * a, hαint a ha, z, hz, ?_⟩
      funext i
      show finPart D e * (a ⊗ₜ[D.host.F] z i) = _
      rw [hα, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact fun y hy => hle hy
  have h2 : ∀ y, T (p y) = p (T y) := fun y => by
    show finMat D.sp.cm.sig W.gram x *ᵥ (finPart D e • y) = finPart D e • (finMat D.sp.cm.sig W.gram x *ᵥ y)
    exact Matrix.mulVec_smul _ _ _
  have h3 : ∀ y, T (y - p y) = y - p y := fun y => finMat_mulVec_fix x hx y
  have h4 : ∀ y, Φ y = 0 → p y = 0 := by
    intro y hy
    have h0 : ∀ k, πf (y k) = 0 := by
      intro k
      have := congrArg (fun w => β.1 *ᵥ w) hy
      simp only [hΦ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact congrFun this k
    funext k
    obtain ⟨a, ha⟩ := finPart_surjective D (y k)
    have hπa : π a = 0 := by rw [← hπf, ha]; exact h0 k
    show finPart D e * y k = 0
    rw [← ha, ← RingHom.map_mul, (hC.2.2.1 a).1 hπa, RingHom.map_zero]
  have h5 : ∀ y, Φ (T y) = h (Φ y) := by
    intro y
    have hmap : (finMat D.sp.cm.sig W.gram x).map πf = β.1 * g.1 * (β⁻¹).1 := by
      rw [← hxg]
      exact Matrix.ext fun i j => hπf _
    have hT : (fun k => πf ((finMat D.sp.cm.sig W.gram x *ᵥ y) k)) =
        (finMat D.sp.cm.sig W.gram x).map πf *ᵥ (fun k => πf (y k)) :=
      funext fun k => RingHom.map_mulVec πf _ y k
    show Φ (finMat D.sp.cm.sig W.gram x *ᵥ y) = g.1 *ᵥ Φ y
    rw [hΦ, hΦ, hT, hmap]
    exact inv_mulVec_conj β g _
  have hmapΦ : (Formalism.L2.NTheta.LamHat W).map Φ =
      (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).toAddSubgroup := by
    ext z
    rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    refine Iff.trans ?_ (mem_span_basisFun _ z).symm
    constructor
    · rintro ⟨y, hy, rfl⟩
      choose a ha using fun k => finPart_surjective D (y k)
      have hpy : (fun i => finPart D (e * a i)) ∈ Formalism.L2.NTheta.LamHat W := by
        have := h1 y hy
        convert this using 1
        funext i
        show finPart D (e * a i) = finPart D e * y i
        rw [RingHom.map_mul, ha]
      have hi := (hF.2 a).1 hpy
      have hz : Φ y = (β⁻¹).1 *ᵥ fun k => π (a k) := by
        rw [hΦ]
        congr 1
        funext k
        rw [← ha, hπf]
      rw [hz]
      exact hi
    · intro hz
      choose a ha using fun k => hC.2.1 ((β.1 *ᵥ z) k)
      have hb : (β⁻¹).1 *ᵥ (fun k => π (a k)) = z := by
        have : (fun k => π (a k)) = β.1 *ᵥ z := funext ha
        rw [this, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      refine ⟨fun i => finPart D (e * a i), (hF.2 a).2 ?_, ?_⟩
      · rw [hb]; exact hz
      · rw [hΦ]
        convert hb using 2
        funext k
        rw [hπf, RingHom.map_mul, hπe, one_mul]
  unfold latIndex
  rw [GlobalTheory.index_transfer_along_projection (Formalism.L2.NTheta.LamHat W) T p Φ h h1 h2 h3 h4 h5, hmapΦ,
    Submodule.map_toAddSubgroup]
  rfl

theorem latIndex_chart_eq : ∀ (D : D7) (W : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (σ : GlobalTheory.InertLoc.LP D P →+* GlobalTheory.InertLoc.LP D P) (π : AE D →+* GlobalTheory.InertLoc.LP D P) (β : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) (ι : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) →* GA D W), GlobalTheory.InertLoc.Chart (algebraMap (AF D.host.F) (AE D) ε) σ π → GlobalTheory.InertLoc.Frame W (algebraMap (AF D.host.F) (AE D) ε) σ π β → GlobalTheory.InertLoc.GrpChart W (algebraMap (AF D.host.F) (AE D) ε) σ π β ι → ∀ (g : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P))), latIndex W (ι g) = ((Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).map (((g : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)).mulVecLin.restrictScalars (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).toAddSubgroup := by
  intro D W v ε hε P σ π β ι hC hF hG g
  obtain ⟨α, hεα, hα1, hα0⟩ := hε
  have hα : finPart D (algebraMap (AF D.host.F) (AE D) ε) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by
    subst hεα; rfl
  have hαint : ∀ a ∈ intAf D.host.F, α * a ∈ intAf D.host.F := by
    intro a ha w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [hα1, one_mul]; exact ha w
    · rw [hα0 w hw, zero_mul]; exact zero_mem _
  exact latIndex_eq_of_chart α hα hαint hC hF (ι g) (hG.1 g) g.1 (hG.2.1 g)

end GlobalTheory.InertLatIndex
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLatticeIndex_eq_localUnitaryIndex_at_inert : ∀ (D : D7) (W : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (σ : GlobalTheory.InertLoc.LP D P →+* GlobalTheory.InertLoc.LP D P) (π : AE D →+* GlobalTheory.InertLoc.LP D P) (β : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) (ι : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) →* GA D W), GlobalTheory.InertLoc.Chart (algebraMap (AF D.host.F) (AE D) ε) σ π → GlobalTheory.InertLoc.Frame W (algebraMap (AF D.host.F) (AE D) ε) σ π β → GlobalTheory.InertLoc.GrpChart W (algebraMap (AF D.host.F) (AE D) ε) σ π β ι → ∀ (g : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P))), latIndex W (ι g) = ((Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).map (((g : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)).mulVecLin.restrictScalars (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).toAddSubgroup := by
  atlas_forward_decl GlobalTheory.InertLatIndex.latIndex_chart_eq
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.InertIdx

theorem indexSum_inert : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(4 : ℝ)) := by
  classical
  intro D W n hn v f hf ⟨w, hw⟩ C hC hdist
  obtain ⟨ε, hε, rfl⟩ := hf
  have hP := GlobalTheory.HeckeRowsCompare.isPrimeIdem_of_inert (P := w) hw hε
  have hc := GlobalTheory.LabChar.fixed_of_tie hP
  obtain ⟨ϖ, σ, q, π, hU, -, hCh, hV⟩ := GlobalTheory.InertLoc.exists_chart hc hP
  obtain ⟨β, ι, hFr, hGC⟩ := hV W
  obtain ⟨hσσ, hσv, -, -, ⟨x0, hx0, hx0v⟩, -, -⟩ := hU
  let K := GlobalTheory.InertLoc.LP D w
  let O := w.adicCompletionIntegers D.host.E

  have hσO : ∀ x : O, σ (x : K) ∈ O := fun x => by
    show Valued.v (σ (x : K)) ≤ 1
    rw [hσv]; exact x.2
  let cO : O ≃+* O :=
    { toFun := fun x => ⟨σ x, hσO x⟩, invFun := fun x => ⟨σ x, hσO x⟩,
      left_inv := fun x => Subtype.ext (hσσ x), right_inv := fun x => Subtype.ext (hσσ x),
      map_mul' := fun x y => Subtype.ext (map_mul σ _ _), map_add' := fun x y => Subtype.ext (map_add σ _ _) }
  let cK : K ≃+* K :=
    { toFun := σ, invFun := σ, left_inv := hσσ, right_inv := hσσ, map_mul' := map_mul σ, map_add' := map_add σ }

  let H : GA D W → Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) K) := fun g =>
    if hg : SuppF W (algebraMap (AF D.host.F) (AE D) ε) g then (hGC.2.2.1 g hg).choose else 1
  have hH : ∀ g ∈ C, ι (H g) = g := fun g hg => by
    simp only [H, dif_pos (hC g hg).1]
    exact (hGC.2.2.1 g (hC g hg).1).choose_spec
  have hinj : Set.InjOn (fun g => ((H g : GL (Fin W.rank) K))) C := fun g hg g' hg' e => by
    rw [← hH g hg, ← hH g' hg', Subtype.ext e]
  have hsum := Finset.sum_image (f := fun x : GL (Fin W.rank) K =>
      ((((Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map (((x : Matrix (Fin W.rank) (Fin W.rank) K)).mulVecLin.restrictScalars O)).toAddSubgroup.relIndex
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2)) hinj
  have hterm : ∀ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) = ((((Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((((H g : GL (Fin W.rank) K) : Matrix (Fin W.rank) (Fin W.rank) K)).mulVecLin.restrictScalars O)).toAddSubgroup.relIndex
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) := fun g hg => by
    conv_lhs => rw [← hH g hg]
    rw [GlobalTheory.T.selfDualLatticeIndex_eq_localUnitaryIndex_at_inert D W v ε hε w σ π β ι hCh hFr hGC (H g)]
  rw [Finset.sum_congr rfl hterm, ← hsum]

  have hcard : Nat.card (IsLocalRing.ResidueField O) = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue, ← GlobalTheory.LFun.InertChart.absNorm_eq
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (by
      have := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
      exact this))
  have hunit : IsUnit (cO ⟨x0, hx0⟩ - ⟨x0, hx0⟩) := by
    have hne : σ x0 - x0 ≠ 0 := fun e => by rw [e, map_zero] at hx0v; exact zero_ne_one hx0v
    refine isUnit_iff_exists_inv.2 ⟨⟨(σ x0 - x0)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · show Valued.v ((σ x0 - x0)⁻¹) ≤ 1
      rw [map_inv₀, hx0v, inv_one]
    · exact mul_inv_cancel₀ hne
  have hunitary : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      ((x : Matrix (Fin W.rank) (Fin W.rank) K).map cK)ᵀ * (1 : Matrix (Fin W.rank) (Fin W.rank) O).map (algebraMap O K) *
        (x : Matrix (Fin W.rank) (Fin W.rank) K) = (1 : Matrix (Fin W.rank) (Fin W.rank) O).map (algebraMap O K) := by
    intro x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hx
    have h1 := (H g).2
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h1
  have hnontriv : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) ≠
        Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank))) := by
    intro x hx he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    have h1 := (GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring K O W.rank _).1 he
    have h2 := (hGC.2.2.2 (H g)).2 h1
    rw [hH g hg] at h2
    exact (hC g hg).2 h2
  have hdist' : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))), ∀ x' ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x' : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) →
      x = x' := by
    intro x hx x' hx' he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hx'
    have hm : (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map
        (((((H g)⁻¹ * H g' : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) K)) : GL (Fin W.rank) K) : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
        Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank))) := by
      have hcomp : ∀ (a b : GL (Fin W.rank) K), ((((a * b : GL (Fin W.rank) K)) : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
          ((a : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O).comp ((b : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) := by
        intro a b
        ext y : 1
        simp [Matrix.mulVec_mulVec]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcomp, Submodule.map_comp, ← he, ← Submodule.map_comp, ← hcomp, inv_mul_cancel]
      ext y
      simp
    have h1 := (GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring K O W.rank _).1 hm
    have h2 := (hGC.2.2.2 _).2 h1
    rw [map_mul, map_inv, hH g hg, hH g' hg'] at h2
    rw [hdist g hg g' hg' h2]
  have key := GlobalTheory.HermNbr.selfDual_sum_le O K cO cK (fun x => Subtype.ext (hσσ x)) (fun x => rfl)
    ⟨⟨x0, hx0⟩, hunit⟩ W.rank n 1 (by simp) (by simp) hn
    (C.image fun g => ((H g : GL (Fin W.rank) K))) hunitary hnontriv hdist'
  refine key.trans (le_of_eq ?_)
  rw [hcard]
  have hv0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_nonneg _
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hv0]
  norm_num

end GlobalTheory.InertIdx

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeIndex_sum_bound : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(4 : ℝ)) := by
  atlas_forward_decl GlobalTheory.InertIdx.indexSum_inert
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.PlaceDichotomy

theorem split_or_inert_idem : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D),
    IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) ∨
      (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) := by
  intro D v f hf
  obtain ⟨ε, ⟨α, hεα, hα1, hα0⟩, rfl⟩ := hf
  haveI := v.isMaximal
  obtain ⟨⟨P, hPp, hPo⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 D.host.E)
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hPp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have hw : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPo.over.symm
  rcases GlobalTheory.LPositivity.split_or_inert D w with hs | hi
  · left
    rw [hw] at hs
    obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hs hw
    refine ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
    have hα : α = GlobalTheory.AdelicU.singleFin v 1 := by
      refine FiniteAdeleRing.ext _ fun u => ?_
      change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
      by_cases e : u = v
      · subst e; rw [hα1, GlobalTheory.AdelicU.evalV_singleFin_self]
      · rw [hα0 u e, GlobalTheory.AdelicU.evalV_singleFin_ne e]
    rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add, add_sub_cancel, hεα, hα]
    rfl
  · right
    exact ⟨w, hw ▸ hi⟩

end GlobalTheory.PlaceDichotomy
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_place_split_idempotent_or_inert : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) ∨ (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) := by
  atlas_forward_decl GlobalTheory.PlaceDichotomy.split_or_inert_idem
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.IndexCount

theorem rank_le (D : D7) (i : Fin D.R.m) : 2 * (Wc D i).rank + 5 ≤ (Vc D i).rank := by
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have := D.R.rank_add_five_le
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  omega

theorem two_le_absNorm {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

theorem indexSum_of_rank {D : D7} (W : HSp D) (n : ℕ) (hn : 2 * W.rank + 5 ≤ n) : IndexSum W n := by
  let q : HeightOneSpectrum (𝓞 D.host.F) → ℝ := fun v => (Ideal.absNorm v.asIdeal : ℝ)
  let z : HeightOneSpectrum (𝓞 D.host.F) → ℝ := fun v =>
    (∏ i ∈ Finset.range W.rank, (1 - q v ^ ((i : ℝ) - (n : ℝ) / 2))⁻¹) ^ 2 - 1
  have hq : ∀ v, 2 ≤ q v := fun v => two_le_absNorm v
  have hσ : (W.rank : ℝ) + 5 / 2 ≤ (n : ℝ) / 2 := by
    have : ((2 * W.rank + 5 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this; linarith
  have hz : ∀ v, z v < 1 ∧ z v ≤ 16 * q v ^ (-(3 : ℝ)) := fun v => GlobalTheory.lattice_zeta_sq_bound (q v) W.rank ((n : ℝ) / 2) (hq v) hσ
  have h8 : ∀ v, 8 * q v ^ (-(4 : ℝ)) ≤ 8 * q v ^ (-(3 : ℝ)) ∧ 8 * q v ^ (-(4 : ℝ)) ≤ 1 / 2 := by
    intro v
    have h1 : (1 : ℝ) ≤ q v := le_trans (by norm_num) (hq v)
    have hle : q v ^ (-(4 : ℝ)) ≤ q v ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    refine ⟨by linarith, ?_⟩
    have : q v ^ (-(4 : ℝ)) ≤ (2 : ℝ) ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (hq v) (by norm_num)
    have h2 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [h2] at this; linarith
  refine ⟨fun v => max (z v) (8 * q v ^ (-(4 : ℝ))), ?_, ?_, ?_⟩
  · have hs : Summable fun v : HeightOneSpectrum (𝓞 D.host.F) => 16 * q v ^ (-(3 : ℝ)) :=
      (GlobalTheory.summable_absNorm_rpow_heightOneSpectrum D.host.F 3 (by norm_num)).mul_left 16
    refine Summable.of_nonneg_of_le (fun v => ?_) (fun v => ?_) hs
    · exact le_trans (by positivity) (le_max_right _ _)
    · refine max_le (hz v).2 ?_
      have h3 : 0 ≤ q v ^ (-(3 : ℝ)) := by positivity
      linarith [(h8 v).1]
  · intro v
    exact max_lt (hz v).1 (by linarith [(h8 v).2])
  · intro v f hf C hC hd
    rcases GlobalTheory.T.finite_place_split_idempotent_or_inert D v f hf with hs | hi
    · exact le_trans (GlobalTheory.T.split_place_lattice_index_sum_le_zeta_sq_sub_one D W n hn v f hf hs C hC hd) (le_max_left _ _)
    · exact le_trans (GlobalTheory.T.inertPlace_latticeIndex_sum_bound D W n hn v f hf hi C hC hd) (le_max_right _ _)

theorem indexSum_holds : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i, IndexSum (Wc D i) (Vc D i).rank := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ _ i
  exact indexSum_of_rank (Wc D i) (Vc D i).rank (rank_le D i)

end GlobalTheory.IndexCount

end
end
