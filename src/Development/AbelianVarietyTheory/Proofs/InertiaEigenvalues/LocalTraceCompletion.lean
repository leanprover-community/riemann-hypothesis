module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallLeExp

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.TraceCompl

theorem le_one_iff_of_mul_eq_one {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (hab : a * b = 1)
    (hb : b ≤ 1) : a ≤ 1 ↔ b = 1 := by
  constructor
  · intro ha
    by_contra hb1
    have hlt : b < 1 := lt_of_le_of_ne hb hb1
    have : (1 : Γ) < 1 := calc
      (1 : Γ) = a * b := hab.symm
      _ ≤ 1 * b := by gcongr
      _ = b := one_mul b
      _ < 1 := hlt
    exact lt_irrefl _ this
  · rintro rfl
    rw [mul_one] at hab
    exact hab.le

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

theorem algebraMap_int_mem (A : ValuationSubring Ω) (x : 𝓞 K) : algebraMap K Ω x ∈ A := by
  have h1 : IsIntegral ℤ (algebraMap K Ω x) := x.2.map (algebraMap K Ω).toIntAlgHom
  have h2 : IsIntegral A (algebraMap K Ω x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact hy ▸ y.2

theorem algebraMap_mem_iff {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)
    (x : K) : algebraMap K Ω x ∈ A ↔ v.valuation K x ≤ 1 := by
  have key : ∀ n : 𝓞 K, A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) ≤ 1 ∧
      v.valuation K (algebraMap (𝓞 K) K n) ≤ 1 ∧
      (A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) = 1 ↔
        v.valuation K (algebraMap (𝓞 K) K n) = 1) := by
    intro n
    have h1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) ≤ 1 :=
      (A.valuation_le_one_iff _).2 (algebraMap_int_mem A n)
    have h2 : v.valuation K (algebraMap (𝓞 K) K n) ≤ 1 := v.valuation_le_one n
    have h3 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) < 1 ↔ n ∈ v.asIdeal := h n
    have h4 : v.valuation K (algebraMap (𝓞 K) K n) < 1 ↔ n ∈ v.asIdeal := v.valuation_lt_one_iff_mem n
    refine ⟨h1, h2, ?_⟩
    have e1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) = 1 ↔ n ∉ v.asIdeal := by
      rw [← h3, not_lt]; exact ⟨fun e => e.ge, fun e => le_antisymm h1 e⟩
    have e2 : v.valuation K (algebraMap (𝓞 K) K n) = 1 ↔ n ∉ v.asIdeal := by
      rw [← h4, not_lt]; exact ⟨fun e => e.ge, fun e => le_antisymm h2 e⟩
    exact e1.trans e2.symm
  obtain ⟨n, d, hd | hd⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := K) x
  · have hd1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) (d : 𝓞 K)).not.2 d.2
      exact le_antisymm (v.valuation_le_one _) (not_lt.1 this)
    have hA1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K d)) = 1 := ((key d).2.2).2 hd1
    have e1 := congrArg (fun y => A.valuation (algebraMap K Ω y)) hd
    have e2 := congrArg (v.valuation K) hd
    simp only [map_mul, hA1, hd1, mul_one] at e1 e2
    rw [← A.valuation_le_one_iff, e1, e2]
    exact iff_of_true (key n).1 (key n).2.1
  · have hd1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) (d : 𝓞 K)).not.2 d.2
      exact le_antisymm (v.valuation_le_one _) (not_lt.1 this)
    have hA1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K d)) = 1 := ((key d).2.2).2 hd1
    have e1 := congrArg (fun y => A.valuation (algebraMap K Ω y)) hd
    have e2 := congrArg (v.valuation K) hd
    simp only [map_mul, hA1, hd1] at e1 e2
    rw [← A.valuation_le_one_iff, le_one_iff_of_mul_eq_one e1 (key n).1,
      le_one_iff_of_mul_eq_one e2 (key n).2.1]
    exact (key n).2.2

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

open WithZero

variable (K : Type) {L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {K} {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  [IsScalarTower K L Ω]

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

end GlobalTheory.LocLanglands.TraceCompl
