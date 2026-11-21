import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiagonalFormCounting
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapesTer
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscEquiv
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapes

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem jK_conjO (z : 𝓞 K) : jK (conjO K z) = star (jK z) := rfl

theorem jK_star (z : 𝓞 K) : jK (star z) = star (jK z) := rfl

theorem star_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (hF : IsFixF K F) {r : K}
    (hr : r ∈ HU.SP K 𝔭) : star r ∈ HU.SP K 𝔭 := by
  obtain ⟨t, ht, z, hz⟩ := HU.mem_SP.1 hr
  refine HU.mem_SP.2 ⟨t, ht, conjO K z, ?_⟩
  rw [jK_conjO, hz, star_mul', star_jK_ι hF, mul_comm]

theorem extP_pow (𝔭 : Ideal (𝓞 F)) (k : ℕ) : extP K 𝔭 ^ k = (𝔭 ^ k).map ι := by
  rw [extP, Ideal.map_pow]

theorem exists_sub_mul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} (hd : d ≠ 0) {z : 𝓞 K}
    (hz : haveI := h𝔭.isPrime; jK z / jK (ι d) ∈ HU.SP K 𝔭) (k : ℕ) :
    ∃ w : 𝓞 K, z - w * ι d ∈ extP K 𝔭 ^ k := by
  have := h𝔭.isPrime
  obtain ⟨t, ht, w, hw⟩ := HU.mem_SP.1 hz
  obtain ⟨u, hu⟩ := exists_inv_mod h𝔭 ht k
  refine ⟨ι u * w, ?_⟩
  have e : w * ι d = ι t * z := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [map_mul, map_mul, hw, mul_assoc, div_mul_cancel₀ _ (jK_ι_ne_zero hd)]
  have e2 : z - ι u * w * ι d = ι (1 - t * u) * z := by
    rw [mul_assoc, e, map_sub, map_one, map_mul]; ring
  rw [e2, extP_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hu)

theorem div_mem_SP_of_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} (hd : d ≠ 0) {x : 𝓞 K}
    {k : ℕ} (hk : vF 𝔭 d ≤ k) (hx : x ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK x / jK (ι d) ∈ HU.SP K 𝔭 :=
  (div_mem_SP_iff h𝔭 hd _).2 (Ideal.pow_le_pow_right hk hx)

theorem div_mul_mem_SP_of_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d d' : 𝓞 F} (hd : d ≠ 0)
    (hd' : d' ≠ 0) {x : 𝓞 K} {k : ℕ} (hk : vF 𝔭 d + vF 𝔭 d' ≤ k) (hx : x ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK x / (jK (ι d) * jK (ι d')) ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  have hx' : x ∈ extP K 𝔭 ^ vF 𝔭 d * extP K 𝔭 ^ vF 𝔭 d' := by
    rw [← pow_add]; exact Ideal.pow_le_pow_right hk hx
  refine Submodule.mul_induction_on hx' (fun y hy y' hy' => ?_) (fun u v hu hv => ?_)
  · rw [map_mul, mul_div_mul_comm]
    exact mul_mem ((div_mem_SP_iff h𝔭 hd _).2 hy) ((div_mem_SP_iff h𝔭 hd' _).2 hy')
  · rw [map_add, add_div]; exact add_mem hu hv

theorem div_mem_SP_of_sub {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} (hd : d ≠ 0) {z w : 𝓞 K}
    {k : ℕ} (hk : vF 𝔭 d ≤ k) (h : z - w * ι d ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK z / jK (ι d) ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  have e : jK z / jK (ι d) = jK (z - w * ι d) / jK (ι d) + jK w := by
    rw [map_sub, map_mul, sub_div, mul_div_cancel_right₀ _ (jK_ι_ne_zero hd)]; ring
  rw [e]
  exact add_mem (div_mem_SP_of_mem h𝔭 hd hk h) (HU.jK_mem_SP w)


end Formalism.L2.SG.Pf.fibreCountingData
end
end

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

section

variable {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsMaximal] {k : ℕ}

local notation "mk" => Ideal.Quotient.mk (extP K 𝔭 ^ k)

theorem exists_mk_iff {d : 𝓞 F} (hd : d ≠ 0) (hk : vF 𝔭 d ≤ k) (z : 𝓞 K) :
    (∃ w : 𝓞 K ⧸ extP K 𝔭 ^ k, mk z = w * mk (ι d)) ↔ jK z / jK (ι d) ∈ HU.SP K 𝔭 := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    have e : mk z = mk (w * ι d) := by rw [hw, map_mul]
    exact div_mem_SP_of_sub h𝔭 hd hk (Ideal.Quotient.eq.mp e)
  · intro h
    obtain ⟨w, hw⟩ := exists_sub_mul_mem h𝔭 hd h k
    refine ⟨mk w, ?_⟩
    have e : mk z = mk (w * ι d) := Ideal.Quotient.eq.mpr hw
    rw [e, map_mul]

theorem exists_mk_mul_iff {d d' : 𝓞 F} (hd : d ≠ 0) (hd' : d' ≠ 0) (hk : vF 𝔭 d + vF 𝔭 d' ≤ k)
    (z : 𝓞 K) :
    (∃ w : 𝓞 K ⧸ extP K 𝔭 ^ k, mk z = mk (ι d) * w * mk (ι d')) ↔
      jK z / (jK (ι d) * jK (ι d')) ∈ HU.SP K 𝔭 := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    have e : mk z = mk (ι d * w * ι d') := by rw [hw, map_mul, map_mul]
    have h1 := div_mul_mem_SP_of_mem h𝔭 hd hd' hk (Ideal.Quotient.eq.mp e)
    have h2 : jK w ∈ HU.SP K 𝔭 :=
      HU.mem_SP.mpr ⟨1, (Ideal.ne_top_iff_one _).mp h𝔭.ne_top, w, by simp⟩
    have hd0 : jK (ι d) ≠ 0 := jK_ι_ne_zero (K := K) hd
    have hd0' : jK (ι d') ≠ 0 := jK_ι_ne_zero (K := K) hd'
    have key : jK z / (jK (ι d) * jK (ι d')) =
        jK (z - ι d * w * ι d') / (jK (ι d) * jK (ι d')) + jK w := by
      simp only [map_sub, map_mul]
      rw [div_add' _ _ _ (mul_ne_zero hd0 hd0')]
      congr 1
      ring
    rw [key]
    exact add_mem h1 h2
  · intro h
    have h' : jK z / jK (ι (d * d')) ∈ HU.SP K 𝔭 := by rwa [map_mul, map_mul]
    obtain ⟨w, hw⟩ := exists_sub_mul_mem h𝔭 (mul_ne_zero hd hd') h' k
    refine ⟨mk w, ?_⟩
    have e1 : z - ι d * w * ι d' = z - w * ι (d * d') := by rw [map_mul]; ring
    have e : mk z = mk (ι d * w * ι d') := by
      rw [Ideal.Quotient.eq, e1]
      exact hw
    rw [e, map_mul, map_mul]

variable {m : ℕ} (a : Fin m → 𝓞 F)

def gramO (Y : Matrix (Fin m) (Fin m) (𝓞 K)) : Matrix (Fin m) (Fin m) (𝓞 K) :=
  Yᴴ * diagonal (fun i => ι (a i)) * Y - diagonal (fun i => ι (a i))

variable {a}

theorem diagQ_eq : diagQ K 𝔭 k a = (diagonal fun i => ι (a i)).map mk := by
  unfold diagQ
  rw [Matrix.diagonal_map (map_zero _)]

theorem condP_iff_eqP (ha : ∀ i, a i ≠ 0) (hk : ∀ i, vF 𝔭 (a i) ≤ k)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (∃ P, P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y.map mk) ↔
      ∀ i j, jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
  unfold diagQ
  constructor
  · rintro ⟨P, hP⟩ i j
    refine (exists_mk_iff (ha j) (hk j) _).mp ⟨P i j, ?_⟩
    have := congrFun (congrFun hP i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply] at this
    rw [map_mul, this]
  · intro h
    choose P hP using fun i j => (exists_mk_iff (ha j) (hk j) (ι (a i) * Y i j)).mpr (h i j)
    refine ⟨Matrix.of P, ?_⟩
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Matrix.of_apply]
    rw [← hP i j, map_mul]

theorem form_eq_map (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (Y.map mk)ᴴ * diagQ K 𝔭 k a * Y.map mk - diagQ K 𝔭 k a = (gramO a Y).map mk := by
  have hs : Function.Semiconj (Ideal.Quotient.mk (extP K 𝔭 ^ k)) star star :=
    fun x => (idealPowerSpanBounds.star_mk 𝔭 k x).symm
  have e : ∀ M : Matrix (Fin m) (Fin m) (𝓞 K),
      M.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = (Ideal.Quotient.mk (extP K 𝔭 ^ k)).mapMatrix M :=
    fun _ => rfl
  rw [e (gramO a Y)]
  unfold gramO
  rw [map_sub, map_mul, map_mul, ← e, ← e, ← e, diagQ_eq, Matrix.conjTranspose_map _ hs]

theorem condW_iff (ha : ∀ i, a i ≠ 0) (hk : ∀ i j, vF 𝔭 (a i) + vF 𝔭 (a j) ≤ k)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (∃ W, (Y.map mk)ᴴ * diagQ K 𝔭 k a * Y.map mk - diagQ K 𝔭 k a =
        diagQ K 𝔭 k a * W * diagQ K 𝔭 k a) ↔
      ∀ i j, jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) ∈ HU.SP K 𝔭 := by
  rw [form_eq_map Y]
  unfold diagQ
  constructor
  · rintro ⟨W, hW⟩ i j
    refine (exists_mk_mul_iff (ha i) (ha j) (hk i j) _).mp ⟨W i j, ?_⟩
    have := congrFun (congrFun hW i) j
    simpa only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  · intro h
    choose W hW using fun i j => (exists_mk_mul_iff (ha i) (ha j) (hk i j) (gramO a Y i j)).mpr (h i j)
    refine ⟨Matrix.of W, ?_⟩
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    exact hW i j

theorem condZ_iff (ha : ∀ i, a i ≠ 0) (hk : ∀ i, vF 𝔭 (a i) ≤ k)
    (Y Y' : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (∃ Z, Y.map mk - Y'.map mk = Z * diagQ K 𝔭 k a) ↔
      ∀ i j, jK (Y i j - Y' i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
  unfold diagQ
  constructor
  · rintro ⟨Z, hZ⟩ i j
    refine (exists_mk_iff (ha j) (hk j) _).mp ⟨Z i j, ?_⟩
    have := congrFun (congrFun hZ i) j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.mul_diagonal] at this
    rw [map_sub, this]
  · intro h
    choose Z hZ using fun i j => (exists_mk_iff (ha j) (hk j) (Y i j - Y' i j)).mpr (h i j)
    refine ⟨Matrix.of Z, ?_⟩
    ext i j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.mul_diagonal, Matrix.of_apply]
    rw [← hZ i j, map_sub]

end

end Formalism.L2.SG.Pf.fibreCountingData
end
end

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def crd (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (b : Fin m → V) (a : Fin m → 𝓞 F) (x : V) (j : Fin m) : K :=
  h (b j) x / jK (ι (a j))

def gmap (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (b : Fin m → V) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) : V →ₗ[𝓞 K] V where
  toFun x := ∑ i, (∑ j, jK (Y i j) * crd h b a x j) • b i
  map_add' x y := by
    simp only [crd, map_add, add_div, mul_add, Finset.sum_add_distrib, add_smul]
  map_smul' c x := by
    simp only [crd, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_jK c x, smul_eq_jK c, smul_smul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul]; ring

section

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

theorem crd_sub (x y : V) (j : Fin m) : crd h b a (x - y) j = crd h b a x j - crd h b a y j := by
  simp only [crd, map_sub, sub_div]

theorem crd_smul (c : 𝓞 K) (x : V) (j : Fin m) : crd h b a (c • x) j = jK c * crd h b a x j := by
  unfold crd
  rw [smul_eq_jK c x, LinearMap.map_smul, smul_eq_mul, mul_div_assoc]

variable (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
include horth hdiag ha

theorem crd_sum (c : Fin m → K) (k : Fin m) : crd h b a (∑ i, c i • b i) k = c k := by
  have e : ∀ j, jK (ι (a j)) = algebraMap F K ((a j : 𝓞 F) : F) := fun j =>
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K (a j)).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K (a j))
  unfold crd
  rw [map_sum, Finset.sum_eq_single k]
  · rw [LinearMap.map_smul, hdiag k, smul_eq_mul, ← e k, mul_div_assoc,
      div_self (jK_ι_ne_zero (K := K) (ha k)), mul_one]
  · intro i _ hik
    rw [LinearMap.map_smul, horth k i (Ne.symm hik), smul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem crd_gmap (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x : V) (k : Fin m) :
    crd h b a (gmap h b a Y x) k = ∑ j, jK (Y k j) * crd h b a x j := by
  rw [show gmap h b a Y x = ∑ i, (∑ j, jK (Y i j) * crd h b a x j) • b i from rfl]
  exact crd_sum horth hdiag ha _ k

theorem h_b (x : V) (k : Fin m) : h (b k) x = jK (ι (a k)) * crd h b a x k := by
  unfold crd
  rw [mul_div_assoc', eq_div_iff (jK_ι_ne_zero (K := K) (ha k)), mul_comm]

variable (hbX : ∀ i, b i ∈ (⊤ : Submodule K V))
  (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
include hbX hloc

theorem coordsT (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x : V) : x = ∑ i, crd h b a x i • b i := G2.coords (hbX := hbX) (hloc := hloc) (horth := horth) (hdiag := hdiag) (ha := ha)
  h𝔭 hL Submodule.mem_top

theorem h_expand (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x y : V) :
    h x y = ∑ i, star (crd h b a x i) * jK (ι (a i)) * crd h b a y i := by
  have e : ∀ j, jK (ι (a j)) = algebraMap F K ((a j : 𝓞 F) : F) := fun j =>
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K (a j)).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K (a j))
  have e1 : ∀ j, h x (b j) = star (crd h b a x j) * jK (ι (a j)) := by
    intro j
    have hx := coordsT horth hdiag ha hbX hloc h𝔭 hL x
    conv_lhs => rw [hx]
    rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
    · rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hdiag j, smul_eq_mul, starRingEnd_apply, ← e j]
    · intro i _ hij
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, horth i j hij, smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hy := coordsT horth hdiag ha hbX hloc h𝔭 hL y
  conv_lhs => rw [hy]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul, e1 j, smul_eq_mul]
  ring

theorem mem_B (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x : V) :
    x ∈ locF 𝔭 L ↔ ∀ i, crd h b a x i ∈ HU.SP K 𝔭 := by
  rw [G2.mem_B_iff (hbX := hbX) (hloc := hloc) (horth := horth) (hdiag := hdiag) (ha := ha)
    h𝔭 hL x]
  exact ⟨fun hx => hx.2, fun hx => ⟨Submodule.mem_top, hx⟩⟩

theorem mem_A (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) (hL : IsLatIn ⊤ L) (x : V) :
    x ∈ locF 𝔭 (dualIn h ⊤ L) ↔ ∀ i, jK (ι (a i)) * crd h b a x i ∈ HU.SP K 𝔭 := by
  rw [G2.mem_locF_dualIn_iff (hbX := hbX) (hloc := hloc) (horth := horth) (hdiag := hdiag) (ha := ha)
    hF h𝔭 hL x]
  refine ⟨fun hx i => ?_, fun hx => ⟨Submodule.mem_top, fun i => ?_⟩⟩
  · rw [← h_b horth hdiag ha x i]
    exact hx.2 i
  · rw [h_b horth hdiag ha x i]
    exact hx i

end

end Formalism.L2.SG.Pf.fibreCountingData
end
end

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem gramO_apply {m : ℕ} (a : Fin m → 𝓞 F) (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (i j : Fin m) :
    jK (gramO a Y i j) = (∑ l, star (jK (Y l i)) * jK (ι (a l)) * jK (Y l j)) -
      if i = j then jK (ι (a i)) else 0 := by
  rw [gramO, Matrix.sub_apply, Matrix.mul_apply, diagonal_apply]
  simp_rw [mul_diagonal, conjTranspose_apply]
  split_ifs <;> simp [jK_star, map_sum]

def endoOf (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (g : V →ₗ[𝓞 K] V)
    (hA : ∀ x ∈ locF 𝔭 (dualIn h ⊤ L), g x ∈ locF 𝔭 (dualIn h ⊤ L))
    (hB : ∀ x ∈ locF 𝔭 L, g x ∈ locF 𝔭 L) : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) :=
  Submodule.mapQ _ _ (g.restrict hA) (fun _ hx => hB _ hx)


section

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}
  (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
  (hbX : ∀ i, b i ∈ (⊤ : Submodule K V))
  (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
  (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) (hL : IsLatIn ⊤ L)
include horth hdiag ha hbX hloc hF h𝔭 hL

theorem gmap_B (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x : V) (hx : x ∈ locF 𝔭 L) :
    gmap h b a Y x ∈ locF 𝔭 L := by
  have := h𝔭.isPrime
  rw [mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL] at hx ⊢
  intro k
  rw [crd_gmap horth hdiag ha]
  exact sum_mem fun j _ => mul_mem (HU.jK_mem_SP _) (hx j)

theorem gmap_A (Y : Matrix (Fin m) (Fin m) (𝓞 K))
    (hY : ∀ i j, haveI := h𝔭.isPrime; jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭)
    (x : V) (hx : x ∈ locF 𝔭 (dualIn h ⊤ L)) : gmap h b a Y x ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := h𝔭.isPrime
  rw [mem_A horth hdiag ha hbX hloc hF h𝔭 hL] at hx ⊢
  intro k
  rw [crd_gmap horth hdiag ha, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  have e : jK (ι (a k) * Y k j) / jK (ι (a j)) * (jK (ι (a j)) * crd h b a x j) =
      jK (ι (a k)) * (jK (Y k j) * crd h b a x j) := by
    rw [map_mul, div_mul_eq_mul_div, div_eq_iff (jK_ι_ne_zero (ha j))]; ring
  rw [← e]
  exact mul_mem (hY k j) (hx j)

theorem B_le_A (x : V) (hx : x ∈ locF 𝔭 L) : x ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := h𝔭.isPrime
  rw [mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL] at hx
  rw [mem_A horth hdiag ha hbX hloc hF h𝔭 hL]
  exact fun i => mul_mem (HU.jK_mem_SP _) (hx i)

theorem h_AB (x y : V) (hx : x ∈ locF 𝔭 (dualIn h ⊤ L)) (hy : y ∈ locF 𝔭 L) :
    haveI := h𝔭.isPrime; h x y ∈ HU.SP K 𝔭 ∧ h y x ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  rw [mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL] at hy
  rw [mem_A horth hdiag ha hbX hloc hF h𝔭 hL] at hx
  rw [h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL x y,
    h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL y x]
  refine ⟨sum_mem fun i _ => ?_, sum_mem fun i _ => ?_⟩
  · have e : star (crd h b a x i) * jK (ι (a i)) * crd h b a y i =
        star (jK (ι (a i)) * crd h b a x i) * crd h b a y i := by
      rw [star_mul', star_jK_ι hF]; ring
    rw [e]
    exact mul_mem (star_mem_SP hF (hx i)) (hy i)
  · rw [mul_assoc]
    exact mul_mem (star_mem_SP hF (hy i)) (hx i)

theorem form_identity (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x y : V) :
    h (gmap h b a Y x) (gmap h b a Y y) - h x y =
      ∑ i, ∑ j, star (crd h b a x i) * jK (gramO a Y i j) * crd h b a y j := by
  rw [h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL x y,
    h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL (gmap h b a Y x) (gmap h b a Y y)]
  simp only [crd_gmap horth hdiag ha, gramO_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_comm.trans ?_
    refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans ?_
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring
  · simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end

end Formalism.L2.SG.Pf.fibreCountingData
end
end

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem div_mul_mul' {x y z : K} (hz : z ≠ 0) : x / z * (z * y) = x * y := by
  rw [div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ hz]

structure JD (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) {m : ℕ}
    (b : Fin m → V) (a : Fin m → 𝓞 F) : Prop where
  orth : ∀ i j, i ≠ j → h (b i) (b j) = 0
  diag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)
  ne : ∀ i, a i ≠ 0
  loc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L
  fix : IsFixF K F
  max : 𝔭.IsMaximal
  lat : IsLatIn ⊤ L

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

namespace JD

variable (J : JD h L 𝔭 b a)
include J

theorem bX : ∀ i, b i ∈ (⊤ : Submodule K V) := fun _ => Submodule.mem_top

theorem memB (x : V) : x ∈ locF 𝔭 L ↔ ∀ i, haveI := J.max.isPrime; crd h b a x i ∈ HU.SP K 𝔭 :=
  mem_B J.orth J.diag J.ne J.bX J.loc J.max.isPrime J.lat x

theorem memA (x : V) : x ∈ locF 𝔭 (dualIn h ⊤ L) ↔
    ∀ i, haveI := J.max.isPrime; jK (ι (a i)) * crd h b a x i ∈ HU.SP K 𝔭 :=
  mem_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat x

theorem crdG (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x : V) (k : Fin m) :
    crd h b a (gmap h b a Y x) k = ∑ j, jK (Y k j) * crd h b a x j :=
  crd_gmap J.orth J.diag J.ne Y x k

theorem h_sub_mem (x y x' y' : V) (hx : x ∈ locF 𝔭 (dualIn h ⊤ L)) (hy : y ∈ locF 𝔭 (dualIn h ⊤ L))
    (hx' : x' - x ∈ locF 𝔭 L) (hy' : y' - y ∈ locF 𝔭 L) :
    haveI := J.max.isPrime; h x' y' - h x y ∈ HU.SP K 𝔭 := by
  have := J.max.isPrime
  have hAB := h_AB J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat
  have e : h x' y' - h x y = h x (y' - y) + h (x' - x) y + h (x' - x) (y' - y) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  rw [e]
  refine add_mem (add_mem (hAB x _ hx hy').1 (hAB y _ hy hx').2) (hAB _ _ ?_ hy').1
  exact B_le_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat _ hx'

def E (Y : Matrix (Fin m) (Fin m) (𝓞 K))
    (hY : ∀ i j, haveI := J.max.isPrime; jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭) :
    Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) :=
  endoOf h L 𝔭 (gmap h b a Y) (gmap_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y hY)
    (gmap_B J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y)

theorem E_mk (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (hY) (x : ↥(locF 𝔭 (dualIn h ⊤ L))) :
    J.E Y hY (Submodule.Quotient.mk x) = Submodule.Quotient.mk
      ⟨gmap h b a Y x, gmap_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y hY x x.2⟩ := rfl

theorem E_isom (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (hY)
    (hW : ∀ i j, haveI := J.max.isPrime;
      jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) ∈ HU.SP K 𝔭) :
    ∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
      Submodule.Quotient.mk x' = J.E Y hY (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = J.E Y hY (Submodule.Quotient.mk y) →
      h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have := J.max.isPrime
  intro x y x' y' hx hy
  rw [E_mk, Submodule.Quotient.eq, Submodule.mem_comap] at hx hy
  simp only [Submodule.subtype_apply, Submodule.coe_sub] at hx hy
  have gA := gmap_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y hY
  rw [← HU.mem_SP_iff_locF]
  have e : h (x' : V) (y' : V) - h (x : V) (y : V) =
      (h (x' : V) (y' : V) - h (gmap h b a Y x) (gmap h b a Y y)) +
        (h (gmap h b a Y x) (gmap h b a Y y) - h (x : V) (y : V)) := by ring
  rw [e]
  refine add_mem (J.h_sub_mem _ _ _ _ (gA _ x.2) (gA _ y.2) hx hy) ?_
  rw [form_identity J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  have hxA := (J.memA x).1 x.2 i
  have hyA := (J.memA y).1 y.2 j
  have hne : jK (ι (a i)) * jK (ι (a j)) ≠ 0 := mul_ne_zero (jK_ι_ne_zero (J.ne i)) (jK_ι_ne_zero (J.ne j))
  have e2 : star (jK (ι (a i)) * crd h b a x i) * (jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j)))) *
      (jK (ι (a j)) * crd h b a y j) = star (crd h b a x i) * jK (gramO a Y i j) * crd h b a y j := by
    rw [star_mul', star_jK_ι J.fix,
      show jK (ι (a i)) * star (crd h b a x i) * (jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j)))) *
        (jK (ι (a j)) * crd h b a y j) = star (crd h b a x i) * jK (gramO a Y i j) * crd h b a y j *
          ((jK (ι (a i)) * jK (ι (a j))) / (jK (ι (a i)) * jK (ι (a j)))) by ring,
      div_self hne, mul_one]
  rw [← e2]
  exact mul_mem (mul_mem (star_mem_SP J.fix hxA) (hW i j)) hyA

theorem E_eq_of (Y Y' : Matrix (Fin m) (Fin m) (𝓞 K)) (hY hY')
    (hd : ∀ i j, haveI := J.max.isPrime; jK (Y i j - Y' i j) / jK (ι (a j)) ∈ HU.SP K 𝔭) :
    J.E Y hY = J.E Y' hY' := by
  have := J.max.isPrime
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, E_mk]
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]
  rw [J.memB]
  intro k
  rw [crd_sub, J.crdG, J.crdG, ← Finset.sum_sub_distrib]
  refine sum_mem fun j _ => ?_
  rw [← sub_mul, ← map_sub, ← div_mul_mul' (jK_ι_ne_zero (J.ne j))]
  exact mul_mem (hd k j) ((J.memA x).1 x.2 j)

theorem crd_u (j l : Fin m) :
    crd h b a (phi (K := K) b a (Pi.single j 1)) l = if l = j then 1 / jK (ι (a j)) else 0 := by
  rw [crd, h_phi J.orth J.diag J.ne]
  by_cases hl : l = j
  · subst hl; simp
  · simp [Pi.single_apply, hl]

theorem u_mem (j : Fin m) : phi (K := K) b a (Pi.single j 1) ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := J.max.isPrime
  rw [J.memA]
  intro i
  rw [← h_b J.orth J.diag J.ne, h_phi J.orth J.diag J.ne]
  exact HU.jK_mem_SP _

theorem sum_crd_u (f : Fin m → K) (j : Fin m) :
    ∑ l, f l * crd h b a (phi (K := K) b a (Pi.single j 1)) l = f j / jK (ι (a j)) := by
  rw [Finset.sum_eq_single j]
  · rw [J.crd_u, if_pos rfl, mul_one_div]
  · intro l _ hl; rw [J.crd_u, if_neg hl, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem entry_of_E_eq (Y Y' : Matrix (Fin m) (Fin m) (𝓞 K)) (hY hY') (he : J.E Y hY = J.E Y' hY')
    (i j : Fin m) : haveI := J.max.isPrime; jK (Y i j - Y' i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
  have := J.max.isPrime
  have h1 := congrArg (fun f => f (Submodule.Quotient.mk ⟨_, J.u_mem j⟩)) he
  simp only [E_mk] at h1
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
    J.memB] at h1
  have h2 := h1 i
  rw [crd_sub, J.crdG, J.crdG, J.sum_crd_u, J.sum_crd_u, ← sub_div, ← map_sub] at h2
  exact h2

end JD

end Formalism.L2.SG.Pf.fibreCountingData
end
end

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

namespace JD

variable (J : JD h L 𝔭 b a)
include J

theorem crd_phi (z : Fin m → 𝓞 K) (k : Fin m) : crd h b a (phi b a z) k = jK (z k) / jK (ι (a k)) := by
  rw [crd, h_phi J.orth J.diag J.ne]

theorem phi_memA (z : Fin m → 𝓞 K) : phi b a z ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := J.max.isPrime
  rw [J.memA]
  intro i
  rw [← h_b J.orth J.diag J.ne, h_phi J.orth J.diag J.ne]
  exact HU.jK_mem_SP _

def Psi : (Fin m → 𝓞 K) →ₗ[𝓞 K] DiscMod h ⊤ L 𝔭 :=
  ((locF 𝔭 L).comap (locF 𝔭 (dualIn h ⊤ L)).subtype).mkQ ∘ₗ (phi b a).codRestrict _ J.phi_memA

theorem Psi_apply (z : Fin m → 𝓞 K) :
    J.Psi z = Submodule.Quotient.mk ⟨phi b a z, J.phi_memA z⟩ := rfl

theorem Psi_surjective : Function.Surjective J.Psi := by
  have := J.max.isPrime
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx := (J.memA x).1 x.2
  choose z hz using fun i => exists_sub_div_mem_SP J.max (J.ne i) (hx i)
  refine ⟨z, ?_⟩
  rw [Psi_apply, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.coe_sub, J.memB]
  intro k
  rw [crd_sub, J.crd_phi]
  have e : jK (z k) / jK (ι (a k)) - crd h b a x k =
      -((jK (ι (a k)) * crd h b a x k - jK (z k)) / jK (ι (a k))) := by
    rw [sub_div, mul_div_cancel_left₀ _ (jK_ι_ne_zero (J.ne k))]; ring
  rw [e]
  exact neg_mem (hz k)

theorem exists_E_eq (P : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭))
    (hP : ∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
      Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
      h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    ∃ (Y : Matrix (Fin m) (Fin m) (𝓞 K))
      (hY : ∀ i j, haveI := J.max.isPrime; jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭),
      (∀ i j, haveI := J.max.isPrime;
        jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) ∈ HU.SP K 𝔭) ∧ J.E Y hY = P := by
  have := J.max.isPrime
  set u : Fin m → ↥(locF 𝔭 (dualIn h ⊤ L)) := fun j => ⟨_, J.u_mem j⟩ with hu
  choose v hv using fun j => Submodule.Quotient.mk_surjective _ (P (Submodule.Quotient.mk (u j)))

  have hav : ∀ j k, jK (ι (a j)) * crd h b a (v j) k ∈ HU.SP K 𝔭 := by
    intro j k
    have h0 : (ι (a j)) • (Submodule.Quotient.mk (u j) : DiscMod h ⊤ L 𝔭) = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.subtype_apply, Submodule.coe_smul, J.memB]
      intro l
      rw [crd_smul, J.crd_u]
      split_ifs with hl
      · subst hl; rw [mul_one_div, div_self (jK_ι_ne_zero (J.ne l))]; exact one_mem _
      · rw [mul_zero]; exact zero_mem _
    have h1 : (Submodule.Quotient.mk (ι (a j) • v j) : DiscMod h ⊤ L 𝔭) = 0 := by
      rw [Submodule.Quotient.mk_smul, hv, ← LinearMap.map_smul, h0, map_zero]
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_smul, J.memB] at h1
    have h2 := h1 k
    rwa [crd_smul] at h2
  choose z hz using fun k j => exists_sub_div_mem_SP J.max (J.ne j) (hav j k)
  set Y : Matrix (Fin m) (Fin m) (𝓞 K) := Matrix.of z with hY
  have hcg : ∀ j k, crd h b a (gmap h b a Y (u j)) k = jK (Y k j) / jK (ι (a j)) := by
    intro j k
    rw [J.crdG]
    exact J.sum_crd_u _ j

  have hgv : ∀ j, gmap h b a Y (u j) - v j ∈ locF 𝔭 L := by
    intro j
    rw [J.memB]
    intro k
    rw [crd_sub, hcg]
    have e : jK (Y k j) / jK (ι (a j)) - crd h b a (v j) k =
        -((jK (ι (a j)) * crd h b a (v j) k - jK (z k j)) / jK (ι (a j))) := by
      rw [sub_div, mul_div_cancel_left₀ _ (jK_ι_ne_zero (J.ne j)), hY, of_apply]; ring
    rw [e]
    exact neg_mem (hz k j)
  have hgA : ∀ j, gmap h b a Y (u j) ∈ locF 𝔭 (dualIn h ⊤ L) := fun j => by
    have := add_mem (B_le_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat _ (hgv j)) (v j).2
    rwa [sub_add_cancel] at this
  have hYA : ∀ i j, jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
    intro i j
    have := (J.memA _).1 (hgA j) i
    rwa [hcg, ← mul_div_assoc, ← map_mul] at this
  refine ⟨Y, hYA, ?_, ?_⟩
  · intro i j
    have hsum : ∑ p, ∑ q, star (crd h b a (u i) p) * jK (gramO a Y p q) * crd h b a (u j) q =
        jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) := by
      refine (Finset.sum_congr rfl fun p _ =>
        J.sum_crd_u (fun q => star (crd h b a (u i) p) * jK (gramO a Y p q)) j).trans ?_
      rw [Finset.sum_eq_single i]
      · simp only [hu]
        rw [J.crd_u, if_pos rfl, star_div₀, star_one, star_jK_ι J.fix, one_div_mul_eq_div, div_div]
      · intro p _ hp
        simp only [hu]
        rw [J.crd_u, if_neg hp, star_zero, zero_mul, zero_div]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [← hsum, ← form_identity J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat]
    have e : h (gmap h b a Y (u i)) (gmap h b a Y (u j)) - h (u i : V) (u j : V) =
        (h (gmap h b a Y (u i)) (gmap h b a Y (u j)) - h (v i : V) (v j : V)) +
          (h (v i : V) (v j : V) - h (u i : V) (u j : V)) := by ring
    rw [e]
    refine add_mem (J.h_sub_mem _ _ _ _ (v i).2 (v j).2 (hgv i) (hgv j)) ?_
    rw [HU.mem_SP_iff_locF]
    exact hP (u i) (u j) (v i) (v j) (hv i) (hv j)
  · have hc : J.E Y hYA ∘ₗ J.Psi = P ∘ₗ J.Psi := by
      refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, LinearMap.coe_single, Psi_apply]
      rw [E_mk]
      change _ = P (Submodule.Quotient.mk (u j))
      rw [← hv, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply,
        Submodule.coe_sub]
      exact hgv j
    refine LinearMap.ext fun q => ?_
    obtain ⟨w, rfl⟩ := J.Psi_surjective q
    exact LinearMap.congr_fun hc w

end JD

end Formalism.L2.SG.Pf.fibreCountingData
end
end

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

def liftQ {K F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    (M : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) : Matrix (Fin m) (Fin m) (𝓞 K) :=
  Matrix.of fun i j => (Ideal.Quotient.mk_surjective (M i j)).choose

theorem liftQ_map {K F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    (M : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (liftQ M).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = M := by
  ext i j
  simp only [Matrix.map_apply, liftQ, Matrix.of_apply]
  exact (Ideal.Quotient.mk_surjective (M i j)).choose_spec

end Formalism.L2.SG.Pf.fibreCountingData

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G5 Formalism.L2.SG.Pf.discriminantNormShapes Formalism.L2.SG.Pf.fibreCountingData

theorem unitary_discriminant_model : UDModel := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ _ hK h hs hd L hL hLi 𝔭 h𝔭 b a hb k hk
  obtain ⟨-, hloc, horth, hdiag, hne⟩ := hb
  have hFx : IsFixF K F := Fact.out
  letI : Setoid (udPre K 𝔭 k a) := udSetoid K 𝔭 k a
  let J : JD h L 𝔭 b a := ⟨horth, hdiag, hne, hloc, hFx, h𝔭, ⟨hL.fg, hL.span_eq_top⟩⟩
  have := h𝔭.isPrime
  have hv : ∀ i, vF 𝔭 (a i) ≤ vJof 𝔭 a := fun i =>
    Finset.single_le_sum (f := fun i => vF 𝔭 (a i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hk1 : ∀ i, vF 𝔭 (a i) ≤ k := fun i => by have := hv i; omega
  have hk2 : ∀ i j, vF 𝔭 (a i) + vF 𝔭 (a j) ≤ k := fun i j => by
    have := hv i; have := hv j; omega
  have hA : ∀ Y : udPre K 𝔭 k a, ∀ i j,
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i) * liftQ Y.1 i j) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ HU.SP K 𝔭 := fun Y =>
    (condP_iff_eqP hne hk1 (liftQ Y.1)).1 (by rw [liftQ_map]; exact Y.2.1)
  have hW : ∀ Y : udPre K 𝔭 k a, ∀ i j,
      algebraMap (𝓞 K) K (gramO a (liftQ Y.1) i j) / (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) * algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j))) ∈ HU.SP K 𝔭 := fun Y =>
    (condW_iff hne hk2 (liftQ Y.1)).1 (by rw [liftQ_map]; exact Y.2.2)
  let f0 : udPre K 𝔭 k a → {P : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) //
      ∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
        Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
        Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
        h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)} :=
    fun Y => ⟨J.E (liftQ Y.1) (hA Y), J.E_isom (liftQ Y.1) (hA Y) (hW Y)⟩
  have hresp : ∀ Y Y' : udPre K 𝔭 k a, Y ≈ Y' → f0 Y = f0 Y' := by
    rintro Y Y' ⟨Z, hZ⟩
    refine Subtype.ext (J.E_eq_of _ _ (hA Y) (hA Y') ((condZ_iff hne hk1 _ _).1 ⟨Z, ?_⟩))
    rw [liftQ_map, liftQ_map]; exact hZ
  let f : udQ K 𝔭 k a → _ := Quotient.lift (s := udSetoid K 𝔭 k a) f0 hresp
  have hinj : Function.Injective f := by
    intro q q'
    induction q using Quotient.inductionOn with | h Y => ?_
    induction q' using Quotient.inductionOn with | h Y' => ?_
    intro he
    have he' : J.E (liftQ Y.1) (hA Y) = J.E (liftQ Y'.1) (hA Y') := congrArg Subtype.val he
    apply Quotient.sound
    obtain ⟨Z, hZ⟩ := (condZ_iff hne hk1 _ _).2 (J.entry_of_E_eq _ _ (hA Y) (hA Y') he')
    rw [liftQ_map, liftQ_map] at hZ
    exact ⟨Z, hZ⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨P, hP⟩
    obtain ⟨Y, hY, hWY, hE⟩ := J.exists_E_eq P hP
    let Yq : udPre K 𝔭 k a :=
      ⟨Y.map (Ideal.Quotient.mk _), (condP_iff_eqP hne hk1 Y).2 hY, (condW_iff hne hk2 Y).2 hWY⟩
    refine ⟨Quotient.mk _ Yq, Subtype.ext ?_⟩
    refine (J.E_eq_of _ _ (hA Yq) hY fun i j => ?_).trans hE
    have e := congrFun (congrFun (liftQ_map (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))) i) j
    rw [map_apply, map_apply, Ideal.Quotient.eq] at e
    exact div_mem_SP_of_mem h𝔭 (hne j) (hk1 j) e
  rw [discAut]
  exact (Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩).symm

end Formalism.L2.SG.Pf.Cnt
end
end

section
namespace Formalism.L2.SG.Pf.Cnt

theorem alpha_discriminant_holds : AlphaDisc :=
  Formalism.L2.SG.Pf.G5.alphaDisc_of_discOnto
    (Formalism.L2.SG.Pf.discriminantNormShapes.discOnto_of_uDModel Formalism.L2.SG.Pf.Cnt.unitary_discriminant_model)

end Formalism.L2.SG.Pf.Cnt
end
