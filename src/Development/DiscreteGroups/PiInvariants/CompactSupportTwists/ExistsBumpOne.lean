import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.UncutHalf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def aS (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (s : ℝ) : H E n 0 := (splitCentre E n s, 1)

open GlobalTheory.CuspRep.CuspidalL2GL in
theorem aS_add (s t : ℝ) : aS E n (s + t) = aS E n s * aS E n t :=
  Prod.ext (splitCentre_add s t) (mul_one _).symm

def G2 {ι : Type} [Fintype ι] (D : Dom E n 0) (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D)
    (V : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (x z : H E n 0) : ℂ :=
  ∑ i, inner ℂ (k₁ x i) (V (k₂ z i))

def AvgInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (L : H E n 0 → ℂ), (∀ (γ : ratH E n 0) x, L ((γ : H E n 0) * x) = L x) → Continuous L → Integrable L D.ν →
  ∀ w : ℝ → ℂ, Continuous w → HasCompactSupport w → ∫ s : ℝ, w s = 1 →
    Integrable (fun x => w (ldet x) * ∫ s : ℝ, L (x * aS E n s)) D.ν ∧
      ∫ x, L x ∂D.ν = (ldet (aS E n 1) : ℂ) * ∫ x, w (ldet x) * (∫ s : ℝ, L (x * aS E n s)) ∂D.ν

def KerEquiv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
  (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D),
  IsTestM Φ₁ → IsTestM Φ₂ → (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ →
  IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂ →
  ∀ (U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)), IsTestM Φ →
    IsROp D Φ (T₁ * U * T₂) → IsPiPart D π U Uπ →
    (∀ (γ : ratH E n 0) x, lInt0 D k₁ k₂ Uπ ((γ : H E n 0) * x) = lInt0 D k₁ k₂ Uπ x) ∧
      ∀ s x z, G2 D k₁ k₂ Uπ (x * aS E n s) (z * aS E n (-s)) = G2 D k₁ k₂ Uπ x z

def TwTrK : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
  (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D),
  IsTestM Φ₁ → IsTestM Φ₂ → (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ →
  IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂ →
  ∀ (U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)) (t : ℂ), IsTestM Φ →
    IsROp D Φ (T₁ * U * T₂) → IsPiPart D π U Uπ → IsTwTr D.μ π (trM Φ M) t →
    Integrable (lInt0 D k₁ k₂ Uπ) D.ν ∧ ∀ w : ℝ → ℂ, Continuous w → HasCompactSupport w → ∫ s : ℝ, w s = 1 →
      (ldet (aS E n 1) : ℂ) * ∫ x, w (ldet x) * (∫ s : ℝ, G2 D k₁ k₂ Uπ (x * aS E n s) x) ∂D.ν = t



end DiscreteGroups.T1.G

end
