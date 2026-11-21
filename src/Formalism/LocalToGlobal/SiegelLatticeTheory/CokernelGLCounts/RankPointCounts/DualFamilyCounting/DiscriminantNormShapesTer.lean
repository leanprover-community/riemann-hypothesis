import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapes
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.HermitianLattices.Ext.L3.localValuationFiltration Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

def LiftOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ X ∈ skSet K 𝔭 k a, ∃ Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), X - Y.1 = Z * diagQ K 𝔭 k a

private theorem mul_not_mem_pow_add_succ {F : Type} [Field F] [NumberField F] {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {x y : 𝓞 F} {a b : ℕ} (hx : x ∈ 𝔭 ^ a) (hx' : x ∉ 𝔭 ^ (a + 1))
    (hy : y ∈ 𝔭 ^ b) (hy' : y ∉ 𝔭 ^ (b + 1)) : x * y ∉ 𝔭 ^ (a + b + 1) := by
  have hp0 : 𝔭 ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hpr : Prime 𝔭 := Ideal.prime_of_isPrime hp0 h𝔭.isPrime
  intro hxy
  rw [← Ideal.dvd_span_singleton] at hx hx' hy hy' hxy
  obtain ⟨I, hI⟩ := hx
  obtain ⟨J, hJ⟩ := hy
  have hI' : ¬ 𝔭 ∣ I := fun h => hx' (by rw [hI, pow_succ]; exact mul_dvd_mul_left _ h)
  have hJ' : ¬ 𝔭 ∣ J := fun h => hy' (by rw [hJ, pow_succ]; exact mul_dvd_mul_left _ h)
  rw [← Ideal.span_singleton_mul_span_singleton, hI, hJ] at hxy
  have h : 𝔭 ^ (a + b) * 𝔭 ∣ 𝔭 ^ (a + b) * (I * J) := by
    rw [← pow_succ]
    convert hxy using 1
    rw [pow_add]
    ring
  rcases hpr.dvd_or_dvd ((mul_dvd_mul_iff_left (pow_ne_zero _ hp0)).mp h) with h | h
  exacts [hI' h, hJ' h]

theorem prod_notMem {F : Type} [Field F] [NumberField F] {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {ι : Type} (s : Finset ι) (f : ι → 𝓞 F) (hf : ∀ i, f i ≠ 0) :
    ∏ i ∈ s, f i ∉ 𝔭 ^ (∑ i ∈ s, vF 𝔭 (f i) + 1) := by
  classical

  have key : ∀ t : Finset ι, ∏ i ∈ t, f i ∈ 𝔭 ^ (∑ i ∈ t, vF 𝔭 (f i)) ∧
      ∏ i ∈ t, f i ∉ 𝔭 ^ (∑ i ∈ t, vF 𝔭 (f i) + 1) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · refine ⟨by simp, ?_⟩
      simp only [Finset.prod_empty, Finset.sum_empty, zero_add, pow_one]
      exact (Ideal.ne_top_iff_one 𝔭).mp h𝔭.ne_top
    · intro j t hj ih
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      refine ⟨?_, mul_not_mem_pow_add_succ h𝔭 (mem_pow_vF h𝔭 (hf j)) (notMem_pow_vF h𝔭 (hf j)) ih.1 ih.2⟩
      rw [pow_add]
      exact Ideal.mul_mem_mul (mem_pow_vF h𝔭 (hf j)) ih.1
  exact (key s).2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

private theorem mem_extP_of_mul_mem_pow_succ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A : 𝓞 F} {e : ℕ}
    (hA : A ∈ 𝔭 ^ e) (hA' : A ∉ 𝔭 ^ (e + 1)) {w : 𝓞 K}
    (hw : ι A * w ∈ extP K 𝔭 ^ (e + 1)) : w ∈ extP K 𝔭 := by
  have hp0 : 𝔭 ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hJdef : extP K 𝔭 = 𝔭.map ι := rfl
  rw [← Ideal.dvd_span_singleton] at hA hA'
  obtain ⟨I, hI⟩ := hA

  have hI' : I ⊔ 𝔭 = ⊤ := by
    by_contra h
    apply hA'
    rw [hI, pow_succ]
    apply mul_dvd_mul_left
    rw [Ideal.dvd_iff_le]
    exact le_sup_left.trans (h𝔭.eq_of_le h le_sup_right).ge
  have hJ0 : extP K 𝔭 ≠ ⊥ := by
    intro h
    apply hp0
    rw [hJdef] at h
    exact (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))).mp h
  have hspan : Ideal.span {ι A} = extP K 𝔭 ^ e * I.map ι := by
    rw [hJdef, ← Ideal.map_pow, ← Ideal.map_mul, ← hI, Ideal.map_span, Set.image_singleton]
  have hcop : I.map ι ⊔ extP K 𝔭 = ⊤ := by
    rw [hJdef, ← Ideal.map_sup, hI', Ideal.map_top]
  rw [← Ideal.dvd_span_singleton, ← Ideal.span_singleton_mul_span_singleton, hspan, pow_succ,
    mul_assoc] at hw
  have h1 := (mul_dvd_mul_iff_left (pow_ne_zero e hJ0)).mp hw
  rw [Ideal.dvd_iff_le] at h1
  rw [← Ideal.dvd_span_singleton, Ideal.dvd_iff_le]
  calc Ideal.span {w} = (I.map ι ⊔ extP K 𝔭) * Ideal.span {w} := by rw [hcop, Ideal.top_mul]
    _ = I.map ι * Ideal.span {w} ⊔ extP K 𝔭 * Ideal.span {w} := Ideal.sup_mul _ _ _
    _ ≤ extP K 𝔭 := sup_le h1 (Ideal.mul_le_inf.trans inf_le_left)

theorem isUnit_det {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F} (ha : ∀ i, a i ≠ 0)
    {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k) {X : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hX : X ∈ skSet K 𝔭 k a) : IsUnit X.det := by
  classical
  have hX0 : Xᴴ * diagQ K 𝔭 k a * X = diagQ K 𝔭 k a := hX
  have hA0 : ∏ i, a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hdet : (diagQ K 𝔭 k a).det = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (∏ i, a i)) := by
    unfold diagQ
    rw [Matrix.det_diagonal]
    simp only [map_prod]
  have hd := congrArg Matrix.det hX0
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdet] at hd

  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (1 - star X.det * X.det)
  have hAw : ι (∏ i, a i) * w ∈ extP K 𝔭 ^ k := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hw]
    linear_combination -hd
  have he : vF 𝔭 (∏ i, a i) ≤ vJof 𝔭 a := by
    by_contra h
    have h2 : ∑ i, vF 𝔭 (a i) + 1 ≤ vF 𝔭 (∏ i, a i) := by
      unfold vJof at h
      omega
    exact prod_notMem h𝔭 Finset.univ a ha (Ideal.pow_le_pow_right h2 (mem_pow_vF h𝔭 hA0))
  have hwJ : w ∈ extP K 𝔭 := mem_extP_of_mul_mem_pow_succ h𝔭 (mem_pow_vF h𝔭 hA0) (notMem_pow_vF h𝔭 hA0)
    (Ideal.pow_le_pow_right (by omega) hAw)
  have hnil : IsNilpotent (1 - star X.det * X.det) := by
    refine ⟨k, ?_⟩
    rw [← hw, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hwJ k
  have h1 : IsUnit (star X.det * X.det) := by
    have h := hnil.isUnit_one_sub
    rwa [sub_sub_cancel] at h
  exact isUnit_of_mul_isUnit_right h1

theorem mul_mem_skSet {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {X X' : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)} (hX : X ∈ skSet K 𝔭 k a)
    (hX' : X' ∈ skSet K 𝔭 k a) : X * X' ∈ skSet K 𝔭 k a := by
  have h1 : Xᴴ * diagQ K 𝔭 k a * X = diagQ K 𝔭 k a := hX
  have h2 : X'ᴴ * diagQ K 𝔭 k a * X' = diagQ K 𝔭 k a := hX'
  show (X * X')ᴴ * diagQ K 𝔭 k a * (X * X') = diagQ K 𝔭 k a
  rw [conjTranspose_mul, show X'ᴴ * Xᴴ * diagQ K 𝔭 k a * (X * X') = X'ᴴ * (Xᴴ * diagQ K 𝔭 k a * X) * X' by
    simp only [Matrix.mul_assoc], h1, h2]

theorem inv_mem_skSet {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {X : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)} (hX : X ∈ skSet K 𝔭 k a)
    (hu : IsUnit X.det) : X⁻¹ ∈ skSet K 𝔭 k a := by
  have h1 : Xᴴ * diagQ K 𝔭 k a * X = diagQ K 𝔭 k a := hX
  show (X⁻¹)ᴴ * diagQ K 𝔭 k a * X⁻¹ = diagQ K 𝔭 k a
  calc (X⁻¹)ᴴ * diagQ K 𝔭 k a * X⁻¹ = (X⁻¹)ᴴ * (Xᴴ * diagQ K 𝔭 k a * X) * X⁻¹ := by rw [h1]
    _ = (X * X⁻¹)ᴴ * diagQ K 𝔭 k a * (X * X⁻¹) := by
        rw [conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = diagQ K 𝔭 k a := by
        rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def toPre {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F} (ha : ∀ i, a i ≠ 0)
    {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k) (X : skSet K 𝔭 k a) : udPre K 𝔭 k a :=
  ⟨X.1, ⟨(X.1⁻¹)ᴴ, by
    have hu := isUnit_det h𝔭 ha hk X.2
    have hX0 : X.1ᴴ * diagQ K 𝔭 k a * X.1 = diagQ K 𝔭 k a := X.2
    calc (X.1⁻¹)ᴴ * diagQ K 𝔭 k a = (X.1⁻¹)ᴴ * (X.1ᴴ * diagQ K 𝔭 k a * X.1) := by rw [hX0]
      _ = (X.1 * X.1⁻¹)ᴴ * diagQ K 𝔭 k a * X.1 := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul]⟩,
    ⟨0, by
      have hX0 : X.1ᴴ * diagQ K 𝔭 k a * X.1 = diagQ K 𝔭 k a := X.2
      rw [hX0, sub_self, Matrix.mul_zero, Matrix.zero_mul]⟩⟩

def cls {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F} (ha : ∀ i, a i ≠ 0)
    {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k) (X : skSet K 𝔭 k a) : udQ K 𝔭 k a :=
  Quotient.mk (udSetoid K 𝔭 k a) (toPre h𝔭 ha hk X)

theorem cls_eq_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F} (ha : ∀ i, a i ≠ 0)
    {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k) (X X' : skSet K 𝔭 k a) :
    cls h𝔭 ha hk X = cls h𝔭 ha hk X' ↔ ∃ Z, X.1 - X'.1 = Z * diagQ K 𝔭 k a :=
  Quotient.eq

theorem mem_kerSet_of_cls {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F}
    (ha : ∀ i, a i ≠ 0) {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k) {S X : skSet K 𝔭 k a}
    (hSX : cls h𝔭 ha hk S = cls h𝔭 ha hk X) : S.1⁻¹ * X.1 ∈ kerSet K 𝔭 k a := by
  obtain ⟨Z, hZ⟩ := (cls_eq_iff h𝔭 ha hk S X).mp hSX
  have hu := isUnit_det h𝔭 ha hk S.2
  refine ⟨mul_mem_skSet (inv_mem_skSet S.2 hu) X.2, -(S.1⁻¹ * Z), ?_⟩
  have hX : X.1 = S.1 - Z * diagQ K 𝔭 k a := by rw [← hZ]; abel
  rw [hX, Matrix.mul_sub, Matrix.nonsing_inv_mul _ hu, Matrix.neg_mul, Matrix.mul_assoc,
    sub_eq_add_neg]

theorem cls_mul_ker {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F}
    (ha : ∀ i, a i ≠ 0) {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k) (S : skSet K 𝔭 k a) (T : kerSet K 𝔭 k a) :
    cls h𝔭 ha hk ⟨S.1 * T.1, mul_mem_skSet S.2 T.2.1⟩ = cls h𝔭 ha hk S := by
  rw [cls_eq_iff]
  obtain ⟨Y, hY⟩ := T.2.2
  refine ⟨S.1 * Y, ?_⟩
  show S.1 * T.1 - S.1 = S.1 * Y * diagQ K 𝔭 k a
  rw [hY, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left, Matrix.mul_assoc]

theorem orbitCount_of_lift (hL : LiftOnto) : OrbitCount := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk
  have hk' : vJof 𝔭 a + 1 ≤ k := by omega

  have hs : ∀ q : udQ K 𝔭 k a, ∃ X : skSet K 𝔭 k a, cls h𝔭 ha hk' X = q := by
    intro q
    obtain ⟨Y, rfl⟩ := Quotient.exists_rep q
    obtain ⟨X, hX, Z, hZ⟩ := hL K F hK 𝔭 h𝔭 m a ha k hk Y
    exact ⟨⟨X, hX⟩, Quotient.sound ⟨Z, hZ⟩⟩
  choose s hs using hs
  have hu : ∀ X : skSet K 𝔭 k a, IsUnit X.1.det := fun X => isUnit_det h𝔭 ha hk' X.2

  let e : skSet K 𝔭 k a ≃ udQ K 𝔭 k a × kerSet K 𝔭 k a :=
    { toFun := fun X => (cls h𝔭 ha hk' X, ⟨(s (cls h𝔭 ha hk' X)).1⁻¹ * X.1,
          mem_kerSet_of_cls h𝔭 ha hk' (hs _)⟩)
      invFun := fun p => ⟨(s p.1).1 * p.2.1, mul_mem_skSet (s p.1).2 p.2.2.1⟩
      left_inv := fun X => Subtype.ext (Matrix.mul_nonsing_inv_cancel_left _ _ (hu _))
      right_inv := fun p => by
        obtain ⟨q, T⟩ := p
        have hc : cls h𝔭 ha hk' ⟨(s q).1 * T.1, mul_mem_skSet (s q).2 T.2.1⟩ = q := by
          rw [cls_mul_ker, hs]
        refine Prod.ext hc (Subtype.ext ?_)
        show (s (cls h𝔭 ha hk' ⟨(s q).1 * T.1, _⟩)).1⁻¹ * ((s q).1 * T.1) = T.1
        rw [hc]
        exact Matrix.nonsing_inv_mul_cancel_left _ _ (hu _) }
  rw [Nat.card_congr e, Nat.card_prod]

theorem discOnto_of_lift (hU : UDModel) (hL : LiftOnto) : DiscOnto :=
  discOnto_of hU (orbitCount_of_lift hL)

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

def SolveOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z = 0

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

private theorem star_algebraMap_ringOfIntegers (x : 𝓞 F) :
    star (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x := by
  have h := Formalism.HermitianLattices.Ext.L3.localizedQuotients.star_ι (K := K) (F := F) Fact.out x
  exact FaithfulSMul.algebraMap_injective (𝓞 K) K h

theorem diagQ_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (diagQ K 𝔭 k a)ᴴ = diagQ K 𝔭 k a := by
  unfold diagQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  rw [Pi.star_apply, star_mk, star_algebraMap_ringOfIntegers]

theorem hom_shift {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y) (Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (P + diagQ K 𝔭 k a * Z) * diagQ K 𝔭 k a = diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) := by
  rw [Matrix.add_mul, hPY, Matrix.mul_add, Matrix.mul_assoc]

theorem form_shift {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P W : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (Y + Z * diagQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) - diagQ K 𝔭 k a =
      diagQ K 𝔭 k a * (W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z) * diagQ K 𝔭 k a := by
  have hH := diagQ_conjTranspose (K := K) 𝔭 k a
  have h1 : Yᴴ * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Pᴴ := by
    have h := congrArg Matrix.conjTranspose hPY
    rw [conjTranspose_mul, conjTranspose_mul, hH] at h
    exact h.symm
  calc _ = Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a + Yᴴ * diagQ K 𝔭 k a * Z * diagQ K 𝔭 k a + diagQ K 𝔭 k a * Zᴴ * (diagQ K 𝔭 k a * Y) +
        diagQ K 𝔭 k a * Zᴴ * diagQ K 𝔭 k a * Z * diagQ K 𝔭 k a := by
        simp only [conjTranspose_add, conjTranspose_mul, hH, Matrix.add_mul, Matrix.mul_add,
          Matrix.mul_assoc]
        abel
    _ = _ := by
        rw [hW, h1, ← hPY]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]


theorem mem_skSet_of_solve {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P W Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (hZ : W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z = 0) :
    Y + Z * diagQ K 𝔭 k a ∈ skSet K 𝔭 k a := by
  show (Y + Z * diagQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) = diagQ K 𝔭 k a
  have h := form_shift hPY hW Z
  rw [hZ, Matrix.mul_zero, Matrix.zero_mul] at h
  exact sub_eq_zero.mp h

theorem liftOnto_of_solve (hS : SolveOnto) : LiftOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z, Z₀, hY, hPY, hW, hZ⟩ := hS K F hK 𝔭 h𝔭 m a ha k hk Y
  refine ⟨Y' + Z * diagQ K 𝔭 k a, mem_skSet_of_solve hPY hW hZ, Z₀ + Z, ?_⟩
  rw [Matrix.add_mul, ← hY]
  abel

theorem discOnto_of_solve (hU : UDModel) (hS : SolveOnto) : DiscOnto :=
  discOnto_of_lift hU (liftOnto_of_solve hS)

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

section
open NumberField Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {c : Type} [Fintype c] [DecidableEq c]

def Ent (J : Ideal (𝓞 K)) (A : Matrix c c (𝓞 K)) : Prop := ∀ i j, A i j ∈ J

theorem ent_mul {I J : Ideal (𝓞 K)} {A B : Matrix c c (𝓞 K)} (hA : Ent I A) (hB : Ent J B) :
    Ent (I * J) (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hA i k) (hB k j)

theorem ent_mul_left {J : Ideal (𝓞 K)} (A : Matrix c c (𝓞 K)) {B : Matrix c c (𝓞 K)} (hB : Ent J B) :
    Ent J (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => J.mul_mem_left _ (hB k j)

theorem ent_mul_right {J : Ideal (𝓞 K)} {A : Matrix c c (𝓞 K)} (hA : Ent J A) (B : Matrix c c (𝓞 K)) :
    Ent J (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => J.mul_mem_right _ (hA i k)

theorem ent_add {J : Ideal (𝓞 K)} {A B : Matrix c c (𝓞 K)} (hA : Ent J A) (hB : Ent J B) :
    Ent J (A + B) := fun i j => J.add_mem (hA i j) (hB i j)

theorem ent_sub {J : Ideal (𝓞 K)} {A B : Matrix c c (𝓞 K)} (hA : Ent J A) (hB : Ent J B) :
    Ent J (A - B) := fun i j => J.sub_mem (hA i j) (hB i j)

theorem ent_neg {J : Ideal (𝓞 K)} {A : Matrix c c (𝓞 K)} (hA : Ent J A) : Ent J (-A) := fun i j => J.neg_mem (hA i j)

theorem ent_smul {J : Ideal (𝓞 K)} (a : 𝓞 K) {A : Matrix c c (𝓞 K)} (hA : Ent J A) : Ent J (a • A) := fun i j => J.mul_mem_left a (hA i j)

theorem ent_mono {I J : Ideal (𝓞 K)} (hIJ : I ≤ J) {A : Matrix c c (𝓞 K)} (hA : Ent I A) : Ent J A := fun i j => hIJ (hA i j)


theorem ent_conjTranspose (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {A : Matrix c c (𝓞 K)}
    (hA : Ent (extP K 𝔭 ^ k) A) : Ent (extP K 𝔭 ^ k) Aᴴ := fun i j => conjO_mem_pow hF 𝔭 k _ (hA j i)


private theorem exists_add_conj_sub_one_mem_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ t : 𝓞 K, t + conjO K t - 1 ∈ extP K 𝔭 := by
  by_cases h : ∃ t : 𝓞 K, t + conjO K t ∉ extP K 𝔭
  · obtain ⟨t0, ht0⟩ := h
    obtain ⟨a, ha⟩ := exists_tr hF t0
    have haP : a ∉ 𝔭 := by
      intro haP
      apply ht0
      rw [← ha]
      exact Ideal.mem_map_of_mem _ haP
    obtain ⟨b, c, hc, hbc⟩ := h𝔭.exists_inv haP
    refine ⟨algebraMap (𝓞 F) (𝓞 K) b * t0, ?_⟩
    have e1 : algebraMap (𝓞 F) (𝓞 K) b * t0 + conjO K (algebraMap (𝓞 F) (𝓞 K) b * t0) - 1 = algebraMap (𝓞 F) (𝓞 K) (b * a - 1) := by
      rw [map_mul, conjO_map hF, map_sub, map_mul, map_one, ha]; ring
    have e2 : b * a - 1 = -c := by linear_combination hbc
    rw [e1, e2, map_neg]
    exact (extP K 𝔭).neg_mem (Ideal.mem_map_of_mem _ hc)
  · push_neg at h
    have h1 : (1 : 𝓞 K) ∈ extP K 𝔭 := by
      apply BallB.mem_of_unram hK
      intro θ
      have e : (θ - conjO K θ) * 1 = θ * (1 + conjO K 1) - (θ + conjO K θ) := by
        rw [map_one]; ring
      rw [e]
      exact (extP K 𝔭).sub_mem ((extP K 𝔭).mul_mem_left _ (h 1)) (h θ)
    refine ⟨0, ?_⟩
    simpa using (extP K 𝔭).neg_mem h1

theorem exists_solve_herm (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {H P Q S : Matrix c c (𝓞 K)} (hH : Ent (extP K 𝔭) H)
    (hPQ : Ent (extP K 𝔭) (Pᴴ * Q - 1)) {N : ℕ} (hHh : Ent (extP K 𝔭 ^ N) (Hᴴ - H))
    (hS : Ent (extP K 𝔭 ^ N) (Sᴴ - S)) :
    ∀ j, j ≤ N → ∃ Z : Matrix c c (𝓞 K),
      Ent (extP K 𝔭 ^ j) (S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z) := by
  obtain ⟨t, ht⟩ := exists_add_conj_sub_one_mem_extP hK hF h𝔭
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨0, fun _ _ => ?_⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ j ih =>
    intro hj
    obtain ⟨Z, hZ⟩ := ih (by omega)
    set E := S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z with hE
    set Y : Matrix c c (𝓞 K) := -(t • E) with hYdef
    set W := Q * Y with hW
    refine ⟨Z + W, ?_⟩
    have hJ : extP K 𝔭 ^ (j + 1) = extP K 𝔭 * extP K 𝔭 ^ j := pow_succ' _ _
    have hJ' : extP K 𝔭 ^ (j + 1) = extP K 𝔭 ^ j * extP K 𝔭 := pow_succ _ _
    have hY : Ent (extP K 𝔭 ^ j) Y := ent_neg (ent_smul t hZ)
    have hYh : Ent (extP K 𝔭 ^ j) Yᴴ := ent_conjTranspose hF 𝔭 j hY
    have hWj : Ent (extP K 𝔭 ^ j) W := ent_mul_left Q hY
    have hWh : Ent (extP K 𝔭 ^ j) Wᴴ := ent_conjTranspose hF 𝔭 j hWj
    have hPQh : Ent (extP K 𝔭) (Pᴴ * Q - 1)ᴴ := by
      have := ent_conjTranspose hF 𝔭 1 (A := Pᴴ * Q - 1) (by rw [pow_one]; exact hPQ)
      rwa [pow_one] at this
    have hEh : Ent (extP K 𝔭 ^ (j + 1)) (Eᴴ - E) := by
      have e : Eᴴ - E = (Sᴴ - S) + Zᴴ * (Hᴴ - H) * Z := by
        simp only [hE, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
        abel
      rw [e]
      have hN : extP K 𝔭 ^ N ≤ extP K 𝔭 ^ (j + 1) := Ideal.pow_le_pow_right hj
      exact ent_mono hN (ent_add hS (ent_mul_right (ent_mul_left _ hHh) _))
    have eq1 : S + Pᴴ * (Z + W) + (Z + W)ᴴ * P + (Z + W)ᴴ * H * (Z + W) =
        E + Pᴴ * W + Wᴴ * P + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W := by
      simp only [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      rw [hE]
      abel
    have eq2 : Pᴴ * W = (Pᴴ * Q - 1) * Y + Y := by
      rw [hW, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
      abel
    have eq3 : Wᴴ * P = Yᴴ * (Pᴴ * Q - 1)ᴴ + Yᴴ := by
      rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one, Matrix.mul_sub,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    have eq4 : E + Y + Yᴴ = (1 - t - star t) • E - star t • (Eᴴ - E) := by
      rw [hYdef, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul]
      simp only [sub_smul, one_smul, smul_sub]
      abel
    have hx : (1 - t - star t) ∈ extP K 𝔭 := by
      have := (extP K 𝔭).neg_mem ht
      convert this using 1
      show 1 - t - conjO K t = -(t + conjO K t - 1)
      ring
    have T1 : Ent (extP K 𝔭 ^ (j + 1)) ((1 - t - star t) • E) := fun a b => by
      rw [hJ]; exact Ideal.mul_mem_mul hx (hZ a b)
    have T2 : Ent (extP K 𝔭 ^ (j + 1)) (star t • (Eᴴ - E)) := ent_smul _ hEh
    have T3 : Ent (extP K 𝔭 ^ (j + 1)) ((Pᴴ * Q - 1) * Y) := by
      rw [hJ]; exact ent_mul hPQ hY
    have T4 : Ent (extP K 𝔭 ^ (j + 1)) (Yᴴ * (Pᴴ * Q - 1)ᴴ) := by
      rw [hJ']; exact ent_mul hYh hPQh
    have T5 : Ent (extP K 𝔭 ^ (j + 1)) (Zᴴ * H * W) := by
      rw [hJ]; exact ent_mul (ent_mul_left Zᴴ hH) hWj
    have FreeQuotientRank : Ent (extP K 𝔭 ^ (j + 1)) (Wᴴ * H * Z) := by
      rw [hJ']; exact ent_mul_right (ent_mul hWh hH) Z
    have T7 : Ent (extP K 𝔭 ^ (j + 1)) (Wᴴ * H * W) := by
      rw [hJ']; exact ent_mul_right (ent_mul hWh hH) W
    have eq5 : E + Pᴴ * W + Wᴴ * P + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W =
        ((1 - t - star t) • E - star t • (Eᴴ - E)) + (Pᴴ * Q - 1) * Y + Yᴴ * (Pᴴ * Q - 1)ᴴ
          + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W := by
      rw [eq2, eq3, ← eq4]
      abel
    rw [eq1, eq5]
    exact ent_add (ent_add (ent_add (ent_add (ent_add (ent_sub T1 T2) T3) T4) T5) FreeQuotientRank) T7

variable [Fact (IsFixF K F)]

theorem ent_lift {𝔭 : Ideal (𝓞 F)} {k : ℕ} (hk : 1 ≤ k)
    {A : Matrix c c (𝓞 K)}
    (hA : ∀ i j, Ideal.Quotient.mk (extP K 𝔭 ^ k) (A i j) ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) :
    Ent (extP K 𝔭) A := fun i j => by
  obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (hA i j)
  have h1 : A i j - x ∈ extP K 𝔭 ^ k := by
    rw [← Ideal.Quotient.eq]; exact hxe.symm
  have h2 : extP K 𝔭 ^ k ≤ extP K 𝔭 := by
    calc extP K 𝔭 ^ k ≤ extP K 𝔭 ^ 1 := Ideal.pow_le_pow_right hk
      _ = extP K 𝔭 := pow_one _
  have := (extP K 𝔭).add_mem (h2 h1) hx
  simpa using this

theorem ent_of_map_eq_zero {𝔭 : Ideal (𝓞 F)} {k : ℕ} {A : Matrix c c (𝓞 K)}
    (hA : A.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = 0) : Ent (extP K 𝔭 ^ k) A := fun i j => by
  have := congrFun (congrFun hA i) j
  simpa [Ideal.Quotient.eq_zero_iff_mem] using this

theorem exists_solve_quot (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ}
    (hk : 1 ≤ k) {H P Q S : Matrix c c (𝓞 K ⧸ extP K 𝔭 ^ k)} (hHh : Hᴴ = H)
    (hH : ∀ i j, H i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))
    (hPQ : ∀ i j, (Pᴴ * Q - 1) i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))
    (hS : Sᴴ = S) : ∃ Z, S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z = 0 := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨H', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k H
  obtain ⟨P', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k P
  obtain ⟨Q', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k Q
  obtain ⟨S', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k S
  have hmap : ∀ A : Matrix c c (𝓞 K), A.map (reductionMapsOfForms.mkk K 𝔭 k) = 0 → Ent (extP K 𝔭 ^ k) A :=
    fun A hA => ent_of_map_eq_zero hA
  have hH' : Ent (extP K 𝔭) H' := ent_lift hk hH
  have hPQ' : Ent (extP K 𝔭) (P'ᴴ * Q' - 1) := by
    apply ent_lift hk
    intro i j
    have e : (P'ᴴ * Q' - 1).map (reductionMapsOfForms.mkk K 𝔭 k) = (P'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * Q'.map (reductionMapsOfForms.mkk K 𝔭 k) - 1 := by
      rw [reductionMapsOfForms.map_conjTranspose, Matrix.map_sub, Matrix.map_mul, Matrix.map_one] <;> simp
    have := hPQ i j
    rw [← e] at this
    exact this
  have hHh' : Ent (extP K 𝔭 ^ k) (H'ᴴ - H') := by
    apply hmap
    rw [Matrix.map_sub, ← reductionMapsOfForms.map_conjTranspose, hHh, sub_self]
    simp
  have hS' : Ent (extP K 𝔭 ^ k) (S'ᴴ - S') := by
    apply hmap
    rw [Matrix.map_sub, ← reductionMapsOfForms.map_conjTranspose, hS, sub_self]
    simp
  obtain ⟨Z', hZ'⟩ := exists_solve_herm hK hF h𝔭 hH' hPQ' hHh' hS' k le_rfl
  refine ⟨Z'.map (reductionMapsOfForms.mkk K 𝔭 k), ?_⟩
  have e : (S' + P'ᴴ * Z' + Z'ᴴ * P' + Z'ᴴ * H' * Z').map (reductionMapsOfForms.mkk K 𝔭 k) =
      S'.map (reductionMapsOfForms.mkk K 𝔭 k) + (P'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * Z'.map (reductionMapsOfForms.mkk K 𝔭 k) +
        (Z'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * P'.map (reductionMapsOfForms.mkk K 𝔭 k) +
        (Z'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * H'.map (reductionMapsOfForms.mkk K 𝔭 k) * Z'.map (reductionMapsOfForms.mkk K 𝔭 k) := by
    simp only [reductionMapsOfForms.map_conjTranspose]
    simp only [← RingHom.mapMatrix_apply, map_add, map_mul]
  rw [← e]
  ext i j
  show Ideal.Quotient.mk (extP K 𝔭 ^ k) _ = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hZ' i j)

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

open Classical in

def eQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (a : Fin m → 𝓞 F) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.diagonal fun j => if a j ∈ 𝔭 then 1 else 0

def NormOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        Wᴴ = W ∧ eQ K 𝔭 k a * W * eQ K 𝔭 k a = W ∧
        eQ K 𝔭 k a * P = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧
        P * eQ K 𝔭 k a = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧ IsUnit P.det

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

theorem eQ_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (eQ K 𝔭 k a)ᴴ = eQ K 𝔭 k a := by
  unfold eQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  rw [Pi.star_apply]
  split_ifs <;> simp

theorem eQ_mul_diagQ_mul_eQ_mem {𝔭 : Ideal (𝓞 F)} {k : ℕ} (a : Fin m → 𝓞 F) (i j : Fin m) :
    (eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) i j ∈
      (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  unfold eQ diagQ
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs with hij hi
  · rw [one_mul, mul_one]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 K)) hi)
  · simp
  · exact zero_mem _

theorem solveOnto_of_norm (hN : NormOnto) : SolveOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z₀, hY, hPY, hW, hWh, hEW, hEP1, hEP2, hdet⟩ := hN K F hK 𝔭 h𝔭 m a ha k hk Y
  have hEh := eQ_conjTranspose (K := K) 𝔭 k a
  have hH := diagQ_conjTranspose (K := K) 𝔭 k a

  have h2 : P * eQ K 𝔭 k a = eQ K 𝔭 k a * P := hEP2.trans hEP1.symm
  have h1 : Pᴴ * eQ K 𝔭 k a = eQ K 𝔭 k a * Pᴴ := by
    have h := congrArg Matrix.conjTranspose h2
    rw [conjTranspose_mul, conjTranspose_mul, hEh] at h
    exact h.symm
  have hu : IsUnit (Pᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star

  obtain ⟨Z', hZ'⟩ := exists_solve_quot hK h𝔭 (k := k) (by omega)
    (H := eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) (P := P) (Q := (Pᴴ)⁻¹) (S := W)
    (by simp only [conjTranspose_mul, hEh, hH, Matrix.mul_assoc])
    (fun i j => eQ_mul_diagQ_mul_eQ_mem a i j)
    (fun i j => by rw [Matrix.mul_nonsing_inv _ hu, sub_self]; simp)
    hWh
  refine ⟨Y', P, W, eQ K 𝔭 k a * Z' * eQ K 𝔭 k a, Z₀, hY, hPY, hW, ?_⟩
  have h2' : ∀ X : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), X * P * eQ K 𝔭 k a = X * eQ K 𝔭 k a * P :=
    fun X => by rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
  have key : W + Pᴴ * (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a) + (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a)ᴴ * P +
      (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a) =
      eQ K 𝔭 k a * (W + Pᴴ * Z' + Z'ᴴ * P + Z'ᴴ * (eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) * Z') * eQ K 𝔭 k a := by
    simp only [conjTranspose_mul, hEh, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, h2',
      ← h1, hEW] <;> abel
  rw [key, hZ', Matrix.mul_zero, Matrix.zero_mul]

theorem discOnto_of_norm (hU : UDModel) (hN : NormOnto) : DiscOnto :=
  discOnto_of_solve hU (solveOnto_of_norm hN)

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.HermitianLattices.Ext.L3.localValuationFiltration Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

def NormShape : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        Wᴴ = W ∧ eQ K 𝔭 k a * W * eQ K 𝔭 k a = W ∧
        eQ K 𝔭 k a * P = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧
        P * eQ K 𝔭 k a = eQ K 𝔭 k a * P * eQ K 𝔭 k a

theorem det_one_add_sub_mem {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    {I : Ideal R} {N : Matrix n n R} (hN : ∀ i j, N i j ∈ I) : (1 + N).det - 1 ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, RingHom.map_det]
  have hM : (Ideal.Quotient.mk I).mapMatrix (1 + N) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hN i i)]
    · simp [Matrix.one_apply_ne hij, Ideal.Quotient.eq_zero_iff_mem.mpr (hN i j)]
  rw [hM, Matrix.det_one]

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

private theorem mem_pow_vF_not_mem_pow_vF_succ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {x : 𝓞 F} (hx : x ≠ 0) :
    x ∈ 𝔭 ^ vF 𝔭 x ∧ x ∉ 𝔭 ^ (vF 𝔭 x + 1) := by
  have hbdd : BddAbove {e : ℕ | x ∈ 𝔭 ^ e} := by
    have h0 : x ∉ ⨅ n : ℕ, 𝔭 ^ n := by
      rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top]
      simpa using hx
    simp only [Submodule.mem_iInf, not_forall] at h0
    obtain ⟨n, hn⟩ := h0
    refine ⟨n, fun e he => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hn (Ideal.pow_le_pow_right hlt.le he)
  refine ⟨?_, fun h => ?_⟩
  · have h1 := Nat.sSup_mem (s := {e : ℕ | x ∈ 𝔭 ^ e}) ⟨0, by simp⟩ hbdd
    exact h1
  · have h2 : vF 𝔭 x + 1 ≤ vF 𝔭 x := le_csSup hbdd h
    omega

private theorem mem_extP_pow_sub_of_mul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} {e k : ℕ}
    (ha : a ∈ 𝔭 ^ e) (ha' : a ∉ 𝔭 ^ (e + 1)) (hek : e ≤ k) {w : 𝓞 K}
    (hw : w * ι a ∈ extP K 𝔭 ^ k) : w ∈ extP K 𝔭 ^ (k - e) := by
  have hkP : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e := by
    rw [← pow_add, Nat.sub_add_cancel hek]
  obtain ⟨J, hJ⟩ : 𝔭 ^ e ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr ha
  have hJP : J ⊔ 𝔭 = ⊤ := by
    by_contra hne
    have hle : J ≤ 𝔭 := le_sup_left.trans (le_of_eq (h𝔭.eq_of_le hne le_sup_right).symm)
    apply ha'
    have h1 : a ∈ 𝔭 ^ e * J := by
      rw [← hJ]
      exact Ideal.mem_span_singleton_self a
    rw [pow_succ]
    exact Ideal.mul_mono_right hle h1
  have hspan : Ideal.span {algebraMap (𝓞 F) (𝓞 K) a} =
      extP K 𝔭 ^ e * J.map (algebraMap (𝓞 F) (𝓞 K)) := by
    have h1 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_mul, Ideal.map_pow] at h1
    exact h1
  have hcop : IsCoprime (extP K 𝔭 ^ (k - e)) (J.map (algebraMap (𝓞 F) (𝓞 K))) := by
    apply IsCoprime.pow_left
    rw [Ideal.isCoprime_iff_sup_eq]
    have h1 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJP
    rw [Ideal.map_sup, Ideal.map_top] at h1
    rw [sup_comm]
    exact h1
  have hιinj : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x = 0 → x = 0 := by
    intro x hx
    have h1 : algebraMap F K (algebraMap (𝓞 F) F x) = 0 := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, hx,
        map_zero]
    rw [map_eq_zero_iff _ (algebraMap F K).injective] at h1
    exact IsFractionRing.injective (𝓞 F) F (by rw [h1, map_zero])
  have ha0 : a ≠ 0 := fun h => ha' (h ▸ Ideal.zero_mem _)
  have hPe : extP K 𝔭 ^ e ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot]
    intro h0
    rw [h0, Ideal.bot_mul, Ideal.span_singleton_eq_bot] at hspan
    exact ha0 (hιinj a hspan)
  have hdiv : extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e ∣
      (Ideal.span {w} * J.map (algebraMap (𝓞 F) (𝓞 K))) * extP K 𝔭 ^ e := by
    rw [← hkP]
    have h2 : extP K 𝔭 ^ k ∣ Ideal.span {w * algebraMap (𝓞 F) (𝓞 K) a} :=
      Ideal.dvd_span_singleton.mpr hw
    rw [← Ideal.span_singleton_mul_span_singleton, hspan, mul_comm (extP K 𝔭 ^ e),
      ← mul_assoc] at h2
    exact h2
  rw [mul_dvd_mul_iff_right hPe] at hdiv
  exact Ideal.dvd_span_singleton.mp (hcop.dvd_of_dvd_mul_right hdiv)

private theorem mem_extP_pow_sub_sum_vF_of_mul_prod_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (a : Fin m → 𝓞 F)
    (ha : ∀ i, a i ≠ 0) (w : 𝓞 K) (s : Finset (Fin m)) :
    ∀ k, w * ∏ i ∈ s, ι (a i) ∈ extP K 𝔭 ^ k → w ∈ extP K 𝔭 ^ (k - ∑ i ∈ s, vF 𝔭 (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k hk
    simpa using hk
  | @insert i s hi ih =>
    intro k hk
    rw [Finset.prod_insert hi] at hk
    rw [Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := mem_pow_vF_not_mem_pow_vF_succ h𝔭 (ha i)
    by_cases hle : vF 𝔭 (a i) ≤ k
    · have h3 : (w * ∏ j ∈ s, ι (a j)) * ι (a i) ∈ extP K 𝔭 ^ k := by
        convert hk using 1
        ring
      have h4 := ih (k - vF 𝔭 (a i)) (mem_extP_pow_sub_of_mul_mem h𝔭 h1 h2 hle h3)
      rwa [Nat.sub_sub] at h4
    · have h5 : k - (vF 𝔭 (a i) + ∑ j ∈ s, vF 𝔭 (a j)) = 0 := by omega
      rw [h5, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top

theorem isUnit_det_of_witness {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F}
    (ha : ∀ i, a i ≠ 0) {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k)
    {Y P W : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (hWH : ∀ i j, (W * diagQ K 𝔭 k a) i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) :
    IsUnit P.det := by
  classical
  have hk0 : k ≠ 0 := by omega
  have hPk : extP K 𝔭 ^ k ≤ extP K 𝔭 := Ideal.pow_le_self hk0
  have hnil : ∀ z ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)), IsNilpotent z := by
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hw : w ∈ extP K 𝔭 := (Ideal.mem_quotient_iff_mem hPk).mp hz
    exact ⟨k, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hw k⟩
  have hmat : Yᴴ * P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * (1 + W * diagQ K 𝔭 k a) := by
    rw [Matrix.mul_assoc, hPY, ← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one,
      ← Matrix.mul_assoc, ← hW]
    abel
  have hdet := congrArg Matrix.det hmat
  simp only [Matrix.det_mul] at hdet
  have hδ : (diagQ K 𝔭 k a).det = Ideal.Quotient.mk (extP K 𝔭 ^ k) (∏ i, ι (a i)) := by
    simp only [diagQ, Matrix.det_diagonal, map_prod]
  have hu := det_one_add_sub_mem hWH
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (Yᴴ.det * P.det - (1 + W * diagQ K 𝔭 k a).det)
  have hx : w * ∏ i, ι (a i) ∈ extP K 𝔭 ^ k := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hw, ← hδ, sub_mul, hdet]
    ring
  have hv : vJof 𝔭 a = ∑ i, vF 𝔭 (a i) := rfl
  have hw1 : w ∈ extP K 𝔭 := by
    have h1 := mem_extP_pow_sub_sum_vF_of_mul_prod_mem h𝔭 a ha w Finset.univ k hx
    exact Ideal.pow_le_self (by rw [hv] at hk; omega) h1
  have hsum : Yᴴ.det * P.det - 1 ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
    have h2 : Yᴴ.det * P.det - 1 = (Yᴴ.det * P.det - (1 + W * diagQ K 𝔭 k a).det) +
        ((1 + W * diagQ K 𝔭 k a).det - 1) := by ring
    rw [h2]
    refine Ideal.add_mem _ ?_ hu
    rw [← hw]
    exact Ideal.mem_map_of_mem _ hw1
  have hunit : IsUnit (Yᴴ.det * P.det) := by
    have h3 := (hnil _ hsum).isUnit_one_add
    have h4 : 1 + (Yᴴ.det * P.det - 1) = Yᴴ.det * P.det := by ring
    rw [h4] at h3
    exact h3
  exact isUnit_of_mul_isUnit_right hunit

theorem eQ_mul_self (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    eQ K 𝔭 k a * eQ K 𝔭 k a = eQ K 𝔭 k a := by
  simp only [eQ, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs <;> simp

theorem eQ_mul_diagQ_mem {𝔭 : Ideal (𝓞 F)} {k : ℕ} (a : Fin m → 𝓞 F) (i j : Fin m) :
    (eQ K 𝔭 k a * diagQ K 𝔭 k a) i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  simp only [eQ, diagQ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs with h1 h2
  · rw [one_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ h2)
  · rw [zero_mul]
    exact Ideal.zero_mem _
  · exact Ideal.zero_mem _

theorem normOnto_of_shape (hS : NormShape) : NormOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z₀, h1, h2, h3, h4, h5, h6, h7⟩ := hS K F hK 𝔭 h𝔭 m a ha k hk Y
  refine ⟨Y', P, W, Z₀, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  refine isUnit_det_of_witness h𝔭 ha (by omega) h2 h3 ?_
  intro i j
  rw [← h5, show eQ K 𝔭 k a * W * eQ K 𝔭 k a * diagQ K 𝔭 k a =
      (eQ K 𝔭 k a * W) * (eQ K 𝔭 k a * diagQ K 𝔭 k a) by simp only [Matrix.mul_assoc],
    Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (eQ_mul_diagQ_mem a l j)

theorem discOnto_of_shape (hU : UDModel) (hS : NormShape) : DiscOnto := discOnto_of_norm hU (normOnto_of_shape hS)

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem exists_inv_unit {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b : 𝓞 F} (hb : b ∉ 𝔭) (k : ℕ) :
    ∃ g : 𝓞 K ⧸ extP K 𝔭 ^ k, g * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι b) = 1 := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv hb

  have hnil : IsNilpotent (Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι i)) := by
    refine ⟨k, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hi) k
  obtain ⟨u, hu⟩ := hnil.isUnit_one_sub
  refine ⟨↑u⁻¹ * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι y), ?_⟩
  have h : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι y) * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι b) = 1 - Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι i) := by
    rw [← map_mul, ← map_mul, eq_sub_iff_add_eq, ← map_add, ← map_add, hyi, map_one, map_one]
  rw [mul_assoc, h, ← hu, Units.inv_mul]

open Classical in

def gQ (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (a : Fin m → 𝓞 F) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.diagonal fun j => if h : a j ∈ 𝔭 then 0 else (exists_inv_unit (K := K) h𝔭 h k).choose

theorem gQ_mul_diagQ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a : Fin m → 𝓞 F) :
    gQ K h𝔭 k a * diagQ K 𝔭 k a = 1 - eQ K 𝔭 k a := by
  unfold gQ eQ diagQ
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext j
  by_cases h : a j ∈ 𝔭
  · simp [h]
  · rw [dif_neg h, if_neg h, sub_zero]
    exact (exists_inv_unit (K := K) h𝔭 h k).choose_spec

theorem diag_comm {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (d d' : n → R) :
    diagonal d * diagonal d' = diagonal d' * diagonal d := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem norm_shape_holds : NormShape := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨⟨P, hPY⟩, ⟨W, hW⟩⟩ := Y.2
  have hF : IsFixF K F := Fact.out
  set H := diagQ K 𝔭 k a with hHdef
  set E := eQ K 𝔭 k a with hEdef
  set G := gQ K h𝔭 k a with hGdef
  set Y0 := Y.1 with hY0
  have hGH : G * H = 1 - E := gQ_mul_diagQ h𝔭 k a
  have hHE : H * E = E * H := diag_comm _ _
  have hHG : H * G = G * H := diag_comm _ _
  have hEE : E * E = E := eQ_mul_self 𝔭 k a
  have hE : Eᴴ = E := eQ_conjTranspose 𝔭 k a
  have hEE' : ∀ M : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), E * (E * M) = E * M :=
    fun M => by rw [← Matrix.mul_assoc, hEE]
  have hHh : Hᴴ = H := diagQ_conjTranspose 𝔭 k a
  have hE0E : (1 - E) * E = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hEE, sub_self]
  have hEE0 : E * (1 - E) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hEE, sub_self]
  have hE0E0 : (1 - E) * (1 - E) = 1 - E := by rw [Matrix.sub_mul, Matrix.one_mul, hEE0, sub_zero]
  have hE0h : (1 - E)ᴴ = 1 - E := by rw [conjTranspose_sub, conjTranspose_one, hE]
  have hHE0 : H * (1 - E) = (1 - E) * H := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hHE]

  set ZA := (1 - Y0) * G with hZA
  have hY1 : Y0 + ZA * H = Y0 * E + (1 - E) := by
    rw [hZA, Matrix.mul_assoc, hGH]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have hP1 := hom_shift hPY ZA
  have hW1 := form_shift hPY hW ZA
  rw [hY1] at hP1 hW1
  rw [← hHdef] at hP1 hW1
  set P1 := P + H * ZA with hP1def
  set W1 := W + Pᴴ * ZA + ZAᴴ * P + ZAᴴ * H * ZA with hW1def
  set Y1 := Y0 * E + (1 - E) with hY1def
  clear_value ZA P1 W1 Y1
  have hY1E0 : Y1 * (1 - E) = 1 - E := by
    rw [hY1def, Matrix.add_mul, Matrix.mul_assoc, hEE0, Matrix.mul_zero, zero_add, hE0E0]
  have hE0Y1 : (1 - E) * Y1ᴴ = 1 - E := by
    have := congrArg conjTranspose hY1E0
    rwa [conjTranspose_mul, hE0h] at this

  have hoff : (1 - E) * Y1 * E = (1 - E) * W1 * E * H := by
    have h1 : (1 - E) * (Y1ᴴ * H * Y1 - H) * E = (1 - E) * H * Y1 * E := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE0Y1,
        Matrix.mul_assoc (1 - E) H E, hHE, ← Matrix.mul_assoc, hE0E, Matrix.zero_mul, sub_zero]
    rw [hW1] at h1
    have h2 : G * ((1 - E) * H) = 1 - E := by rw [← hHE0, ← Matrix.mul_assoc, hGH, hE0E0]
    calc (1 - E) * Y1 * E = G * ((1 - E) * H) * Y1 * E := by rw [h2]
      _ = G * ((1 - E) * H * Y1 * E) := by simp only [Matrix.mul_assoc]
      _ = G * ((1 - E) * (H * W1 * H) * E) := by rw [← h1]
      _ = G * ((1 - E) * H) * W1 * (H * E) := by simp only [Matrix.mul_assoc]
      _ = (1 - E) * W1 * E * H := by rw [h2, hHE]; simp only [Matrix.mul_assoc]

  set ZB := -((1 - E) * W1 * E) with hZB
  have hY2 : Y1 + ZB * H = E * Y0 * E + (1 - E) := by
    rw [hZB, Matrix.neg_mul, ← hoff, hY1def]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, hEE, hE0E, Matrix.zero_mul]
    abel
  have hP2 := hom_shift hP1 ZB
  have hW2 := form_shift hP1 hW1 ZB
  rw [hY2] at hP2 hW2
  rw [← hHdef] at hP2 hW2
  set P2 := P1 + H * ZB with hP2def
  set W2 := W1 + P1ᴴ * ZB + ZBᴴ * P1 + ZBᴴ * H * ZB with hW2def
  set Y2 := E * Y0 * E + (1 - E) with hY2def
  clear_value ZB P2 W2 Y2

  have hY2E0 : (1 - E) * Y2 = 1 - E := by
    rw [hY2def, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE0E, Matrix.zero_mul,
      Matrix.zero_mul, zero_add, hE0E0]
  have hY2E0' : Y2 * (1 - E) = 1 - E := by
    rw [hY2def, Matrix.add_mul, Matrix.mul_assoc, hEE0, Matrix.mul_zero, zero_add, hE0E0]
  have hE0Y2 : Y2ᴴ * (1 - E) = 1 - E := by
    have := congrArg conjTranspose hY2E0
    rwa [conjTranspose_mul, hE0h] at this
  have hE0Y2' : (1 - E) * Y2ᴴ = 1 - E := by
    have := congrArg conjTranspose hY2E0'
    rwa [conjTranspose_mul, hE0h] at this
  set X := Y2ᴴ * H * Y2 - H with hXdef
  clear_value X
  have hX0 : (1 - E) * X = 0 := by
    rw [hXdef, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE0Y2', ← hHE0,
      Matrix.mul_assoc, hY2E0, sub_self]
  have hX1 : X * (1 - E) = 0 := by
    rw [hXdef, Matrix.sub_mul, Matrix.mul_assoc, hY2E0', Matrix.mul_assoc, hHE0, ← Matrix.mul_assoc,
      hE0Y2, sub_self]
  have hEX : E * X = X := by
    have := hX0; rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this; exact this.symm
  have hXE : X * E = X := by
    have := hX1; rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this; exact this.symm
  have hXh : Xᴴ = X := by
    rw [hXdef, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      hHh, Matrix.mul_assoc]
  have hA : H * (E * W2 * E) * H = X := by
    calc H * (E * W2 * E) * H = (H * E) * W2 * (E * H) := by simp only [Matrix.mul_assoc]
      _ = (E * H) * W2 * (H * E) := by rw [hHE]
      _ = E * (H * W2 * H) * E := by simp only [Matrix.mul_assoc]
      _ = X := by rw [← hW2, hEX, hXE]
  obtain ⟨t, ht⟩ := exists_trace_one hK hF h𝔭 k
  set θ := Ideal.Quotient.mk (extP K 𝔭 ^ k) t with hθ
  have hθ1 : θ + star θ = 1 := by
    rw [hθ, star_mk, ← map_add, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]
    exact ht
  set A := E * W2 * E with hAdef
  clear_value A
  set W' := θ • A + star θ • Aᴴ with hW'def
  clear_value W'
  have hAh : H * Aᴴ * H = X := by
    have := congrArg conjTranspose hA
    rwa [conjTranspose_mul, conjTranspose_mul, hHh, hXh, ← Matrix.mul_assoc] at this
  have hW' : Y2ᴴ * H * Y2 - H = H * W' * H := by
    rw [← hXdef, hW'def, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, hA, hAh, ← add_smul, hθ1, one_smul]
  have hW'h : W'ᴴ = W' := by
    rw [hW'def, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_conjTranspose,
      star_star, add_comm]
  have hEAE : E * A * E = A := by
    rw [hAdef]; simp only [Matrix.mul_assoc, hEE, hEE']
  have hEAhE : E * Aᴴ * E = Aᴴ := by
    have := congrArg conjTranspose hEAE
    rwa [conjTranspose_mul, conjTranspose_mul, hE, ← Matrix.mul_assoc] at this
  have hW's : E * W' * E = W' := by
    rw [hW'def, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, hEAE, hEAhE]
  set P3 := (1 - E) + E * P2 * E with hP3def
  clear_value P3
  have hEY2E : E * Y2 * E = E * Y0 * E := by
    rw [hY2def, Matrix.mul_add, Matrix.add_mul, hEE0, Matrix.zero_mul, add_zero]
    simp only [Matrix.mul_assoc, hEE, hEE']
  have hP3H : P3 * H = H * Y2 := by
    have e1 : E * P2 * E * H = H * (E * Y0 * E) := by
      calc E * P2 * E * H = E * P2 * (E * H) := by simp only [Matrix.mul_assoc]
        _ = E * P2 * (H * E) := by rw [hHE]
        _ = E * (P2 * H) * E := by simp only [Matrix.mul_assoc]
        _ = E * (H * Y2) * E := by rw [hP2]
        _ = (E * H) * Y2 * E := by simp only [Matrix.mul_assoc]
        _ = (H * E) * Y2 * E := by rw [hHE]
        _ = H * (E * Y2 * E) := by simp only [Matrix.mul_assoc]
        _ = H * (E * Y0 * E) := by rw [hEY2E]
    rw [hP3def, Matrix.add_mul, e1, ← hHE0, hY2def, Matrix.mul_add]
    abel
  have hEP3 : E * P3 = E * P3 * E := by
    rw [hP3def, Matrix.mul_add, Matrix.add_mul, hEE0, Matrix.zero_mul]
    simp only [Matrix.mul_assoc, hEE, hEE', zero_add]
  have hP3E : P3 * E = E * P3 * E := by
    rw [hP3def, Matrix.add_mul, hE0E, zero_add, Matrix.mul_add, Matrix.add_mul, hEE0, Matrix.zero_mul,
      zero_add]
    simp only [Matrix.mul_assoc, hEE, hEE']
  refine ⟨Y2, P3, W', ZA + ZB, ?_, hP3H, hW', hW'h, hW's, hEP3, hP3E⟩
  rw [Matrix.add_mul, ← hY2, ← hY1]
  abel

theorem discOnto_of_uDModel (hU : UDModel) : DiscOnto :=
  discOnto_of_shape hU norm_shape_holds

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end
