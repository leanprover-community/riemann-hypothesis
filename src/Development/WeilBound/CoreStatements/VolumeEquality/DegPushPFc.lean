module

public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPFa
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPFb
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord

@[expose] public section

noncomputable section

namespace SheetDecomposition.PF

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal intNum pointConeMap)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)] {K' : Type} [Fintype K'] {ι' : K' → Type}
  [∀ b, Fintype (ι' b)]

def blkE (K K' : Type) : K' ≃ FibreBlock (Sum.inl : K → K ⊕ K') where
  toFun k := ⟨.inr k, by simp⟩
  invFun
    | ⟨.inl k, h⟩ => absurd ⟨k, rfl⟩ h
    | ⟨.inr k, _⟩ => k
  left_inv _ := rfl
  right_inv
    | ⟨.inl k, h⟩ => absurd ⟨k, rfl⟩ h
    | ⟨.inr _, _⟩ => rfl

def varE (ι : K → Type) (ι' : K' → Type) :
    (Σ b, ι' b) ≃ Σ b : FibreBlock (Sum.inl : K → K ⊕ K'), fibreIdx (Sum.elim ι ι') Sum.inl b where
  toFun p := ⟨⟨.inr p.1, by simp⟩, p.2⟩
  invFun
    | ⟨⟨.inl k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨.inr k, _⟩, i⟩ => ⟨k, i⟩
  left_inv _ := rfl
  right_inv
    | ⟨⟨.inl k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨.inr _, _⟩, _⟩ => rfl

variable {Ω₁ : Type} [Field Ω₁] {Ω : Type} [Field Ω] [Algebra Ω₁ Ω]

theorem image_join (y : (Σ b, ι b) → Ω₁) (y' : (Σ b, ι' b) → Ω) :
    imageZ inlV (mCoordIdeal (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')) = mCoordIdeal y := by
  have key : ∀ f, mConeMap (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y') (rename inlV f) =
      rename Sum.inl (MvPolynomial.map (algebraMap Ω₁ Ω) (mConeMap y f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp]
      simp [mConeMap, inlV, joinPt]
  ext f
  simp only [imageZ, Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
  rw [show (rename inlV).toRingHom f = rename inlV f from rfl, key]
  constructor
  · intro h
    apply MvPolynomial.map_injective _ (algebraMap Ω₁ Ω).injective
    apply MvPolynomial.rename_injective _ Sum.inl_injective
    rw [h, map_zero, map_zero]
  · intro h
    rw [h, map_zero, map_zero]

theorem ker_aeval_cone {Φ : Type} [Field Φ] (y : (Σ b, ι b) → Ω) (ν : MvPolynomial K Ω →+* Φ) (hν : Function.Injective ν) :
    RingHom.ker (aeval (fun p : Σ b, ι b => ν (C (y p) * X p.1)) : MRing ι →ₐ[ℤ] Φ) = mCoordIdeal y := by
  have key : ∀ f : MRing ι, (aeval (fun p : Σ b, ι b => ν (C (y p) * X p.1)) : MRing ι →ₐ[ℤ] Φ) f =
      ν (mConeMap y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      rw [map_mul, hp, map_mul (mConeMap y), map_mul ν, aeval_X]
      congr 1
      simp [mConeMap]
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker]
  rw [key]
  constructor
  · intro h
    apply hν
    rw [h, map_zero]
  · intro h
    rw [h, map_zero]

theorem gen_cone {Φ : Type} [Field Φ] [Algebra (MvPolynomial K Ω₁) Φ] [IsFractionRing (MvPolynomial K Ω₁) Φ]
    {y : (Σ b, ι b) → Ω₁} (hb : Birational y) (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) (c : Φ) :
    ∃ f g : MRing ι, aeval (fun p : Σ b, ι b => algebraMap (MvPolynomial K Ω₁) Φ (C (y p) * X p.1)) g ≠ 0 ∧
      c = aeval (fun p : Σ b, ι b => algebraMap (MvPolynomial K Ω₁) Φ (C (y p) * X p.1)) f /
        aeval (fun p : Σ b, ι b => algebraMap (MvPolynomial K Ω₁) Φ (C (y p) * X p.1)) g := by
  set φ : MRing ι →ₐ[ℤ] Φ :=
    aeval (fun p : Σ b, ι b => algebraMap (MvPolynomial K Ω₁) Φ (C (y p) * X p.1)) with hφ
  have key : ∀ f : MRing ι, φ f = algebraMap (MvPolynomial K Ω₁) Φ (mConeMap y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [hφ, mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      rw [map_mul, hp, map_mul (mConeMap y), map_mul (algebraMap _ Φ), hφ, aeval_X]
      congr 1
      simp [mConeMap]
  have hinj : Function.Injective (algebraMap (MvPolynomial K Ω₁) Φ) := IsFractionRing.injective _ _
  set S := Subfield.closure (Set.range φ) with hS
  have hmem : ∀ f, algebraMap (MvPolynomial K Ω₁) Φ (mConeMap y f) ∈ S := by
    intro f
    rw [← key]
    exact Subfield.subset_closure ⟨f, rfl⟩
  have hC : ∀ s : Ω₁, algebraMap (MvPolynomial K Ω₁) Φ (C s) ∈ S := by
    intro s
    obtain ⟨d, g, h, hg, hh, hne0, heq⟩ := hb s
    have eg := ConeTrdeg.mConeMap_of_isMultiHomog y hg
    have eh := ConeTrdeg.mConeMap_of_isMultiHomog y hh
    have hM : (∏ k : K, (X k : MvPolynomial K Ω₁) ^ d k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (X_ne_zero k))
    have hCne : (C (aeval y h) : MvPolynomial K Ω₁) ≠ 0 := by
      rw [Ne, MvPolynomial.C_eq_zero]
      exact hne0
    have hden : algebraMap (MvPolynomial K Ω₁) Φ (mConeMap y h) ≠ 0 := by
      rw [eh]
      intro h0
      have := hinj (h0.trans (map_zero _).symm)
      exact mul_ne_zero hCne hM this
    have : algebraMap (MvPolynomial K Ω₁) Φ (C s) =
        algebraMap (MvPolynomial K Ω₁) Φ (mConeMap y g) / algebraMap (MvPolynomial K Ω₁) Φ (mConeMap y h) := by
      rw [eq_div_iff hden, ← map_mul, eg, eh, heq]
      congr 1
      rw [map_mul]
      ring
    rw [this]
    exact div_mem (hmem g) (hmem h)
  have hX : ∀ k : K, algebraMap (MvPolynomial K Ω₁) Φ (X k) ∈ S := by
    intro k
    obtain ⟨j, hj⟩ := hne k
    have e1 : (X k : MvPolynomial K Ω₁) = C (y ⟨k, j⟩)⁻¹ * mConeMap y (X ⟨k, j⟩) := by
      simp only [mConeMap, aeval_X]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hj, map_one, one_mul]
    rw [e1, map_mul]
    exact mul_mem (hC _) (hmem _)
  have hall : ∀ a : MvPolynomial K Ω₁, algebraMap (MvPolynomial K Ω₁) Φ a ∈ S := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C s => exact hC s
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p n hp => rw [map_mul]; exact mul_mem hp (hX n)
  have hc : c ∈ S := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial K Ω₁) c
    exact div_mem (hall a) (hall b)
  have hsub : Subring.closure (Set.range φ) ≤ φ.toRingHom.range :=
    Subring.closure_le.mpr (by
      rintro _ ⟨f, rfl⟩
      exact ⟨f, rfl⟩)
  obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.mp hc
  obtain ⟨f, rfl⟩ := hsub hu
  obtain ⟨g, rfl⟩ := hsub hv
  by_cases hg0 : φ.toRingHom g = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [← huv, hg0, div_zero, map_zero, zero_div]
  · exact ⟨f, g, hg0, huv.symm⟩

end SheetDecomposition.PF
