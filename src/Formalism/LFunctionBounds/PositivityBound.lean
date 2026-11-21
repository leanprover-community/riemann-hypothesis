import Formalism.StatementFL

section
open Complex

noncomputable section

namespace Formalism.FX

open Classical

def triples (l : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 l ×ˢ Finset.Icc 1 l ×ˢ Finset.Icc 1 l).filter (fun S => S.1 + S.2.1 + S.2.2 = l)

def IsProb (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) : Prop :=
  (∀ S ∈ triples l, 0 ≤ ν S) ∧ ∑ S ∈ triples l, ν S = 1

def W (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ S ∈ triples l, ν S *
    ((if S.1 = x then 1 else 0) + (if S.2.1 = x then 1 else 0) + (if S.2.2 = x then 1 else 0))

def Snu (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (χ : DirichletCharacter ℂ l) : ℂ :=
  ∑ x ∈ Finset.Ioo 0 l, (W l ν x : ℂ) * (starRingEnd ℂ) (χ (x : ZMod l))

def cW (l : ℕ) [NeZero l] (ν : ℕ × ℕ × ℕ → ℝ) (χ : DirichletCharacter ℂ l) : ℂ :=
  DirichletCharacter.LFunction χ 0 * Snu l ν χ / ((((l : ℝ) - 1) / 2 : ℝ) : ℂ)

def oddChars (l : ℕ) [NeZero l] : Finset (DirichletCharacter ℂ l) :=
  @Finset.filter _ (fun χ => χ.Odd) (Classical.decPred _) (@Finset.univ _ (Fintype.ofFinite _))

def saw (y : ℝ) : ℝ := if Int.fract y = 0 then 0 else Int.fract y - 1 / 2

def sgnS (l : ℕ) (S : ℕ × ℕ × ℕ) (t : ℤ) : ℝ :=
  -2 * (saw ((t : ℝ) * (S.1 : ℝ) / (l : ℝ)) + saw ((t : ℝ) * (S.2.1 : ℝ) / (l : ℝ)) +
    saw ((t : ℝ) * (S.2.2 : ℝ) / (l : ℝ)))

def oNu (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (t : ℤ) : ℝ := ∑ S ∈ triples l, ν S * sgnS l S t

def gam (s : ℝ) : ℝ := Real.Gamma s / Real.Gamma (1 - s)

def logOm1 (l : ℕ) (S : ℕ × ℕ × ℕ) : ℝ :=
  -Real.log l + (Real.log (gam ((S.1 : ℝ) / (l : ℝ))) + Real.log (gam ((S.2.1 : ℝ) / (l : ℝ))) +
    Real.log (gam ((S.2.2 : ℝ) / (l : ℝ))))

def PeriodIdentity : Prop :=
  ∀ (l : ℕ) [NeZero l], l.Prime → l ≠ 2 → ∀ ν : ℕ × ℕ × ℕ → ℝ, IsProb l ν →
    (∀ t : ℤ, ¬ (l : ℤ) ∣ t →
      ((oNu l ν t : ℝ) : ℂ) = ∑ χ ∈ oddChars l, cW l ν χ * (starRingEnd ℂ) (χ (t : ZMod l))) ∧
    (∑ χ ∈ oddChars l, cW l ν χ = 1) ∧
    (∀ χ ∈ oddChars l, cW l ν χ⁻¹ = (starRingEnd ℂ) (cW l ν χ)) ∧
    (((∑ S ∈ triples l, ν S * logOm1 l S : ℝ) : ℂ) =
      (Real.eulerMascheroniConstant : ℂ) + (Real.log (2 * Real.pi / l) : ℂ) -
        ∑ χ ∈ oddChars l, cW l ν χ *
          (deriv (DirichletCharacter.LFunction χ⁻¹) 1 / DirichletCharacter.LFunction χ⁻¹ 1))

def KillingLemma : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ l₀ : ℕ, ∀ (l : ℕ) [NeZero l], l.Prime → l₀ ≤ l →
    ∀ BB : Finset (DirichletCharacter ℂ l), BB ⊆ oddChars l → (∀ χ ∈ BB, χ⁻¹ ∈ BB) →
      (BB.card : ℝ) ≤ (l : ℝ) ^ (1 - ε) →
      ∃ ν : ℕ × ℕ × ℕ → ℝ, IsProb l ν ∧ ∀ χ ∈ BB, cW l ν χ = 0

def zeroChars (l : ℕ) [NeZero l] (θ : ℝ) (Z : Finset ℂ) : Finset (DirichletCharacter ℂ l) :=
  @Finset.filter _ (fun χ => (∃ σ : ℝ, θ ≤ σ ∧ σ ≤ 1 ∧ DirichletCharacter.LFunction χ σ = 0) ∨
      ∃ z ∈ Z, DirichletCharacter.LFunction χ z = 0) (Classical.decPred _)
    (@Finset.univ _ (Fintype.ofFinite _))

def Density : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℝ, 1 ≤ T → ∀ k : ℕ, ∃ C : ℝ,
    ∀ (l : ℕ) [NeZero l], l.Prime → ∀ Z : Finset ℂ, Z.card ≤ k →
      (∀ z ∈ Z, θ ≤ z.re ∧ |z.im| ≤ T) →
      ((zeroChars l θ Z).card : ℝ) ≤ C * (l : ℝ) ^ (1 - δ)

def zeroCharsRect (l : ℕ) [NeZero l] (θ T : ℝ) : Finset (DirichletCharacter ℂ l) :=
  @Finset.filter _ (fun χ => ∃ s : ℂ, θ ≤ s.re ∧ |s.im| ≤ T ∧ DirichletCharacter.LFunction χ s = 0)
    (Classical.decPred _) (@Finset.univ _ (Fintype.ofFinite _))

def DensityRect : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℝ, 1 ≤ T → ∃ C : ℝ,
    ∀ (l : ℕ) [NeZero l], l.Prime → ((zeroCharsRect l θ T).card : ℝ) ≤ C * (l : ℝ) ^ (1 - δ)

def inCM (l : ℕ) (S : ℕ × ℕ × ℕ) (n : ℕ) : Prop :=
  Int.fract ((n * S.1 : ℝ) / l) + Int.fract ((n * S.2.1 : ℝ) / l) < 1

open ArithmeticFunction in

def AS (l : ℕ) (S : ℕ × ℕ × ℕ) (y : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
    if ¬ l ∣ n ∧ ¬ inCM l S n then Λ n * max 0 (y / (n : ℝ) - 1) else 0

def Al (l : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 ⌊y⌋₊, Real.log l * max 0 (y / (l : ℝ) ^ i - 1)

def logPiV (l : ℕ) : ℝ := Real.log (2 * Real.pi / l) + Real.log l / ((l : ℝ) - 1)

def tripleMainTerm (l : ℕ) (S : ℕ × ℕ × ℕ) (y : ℝ) : ℝ :=
  y * (Real.log y - 1 - logOm1 l S + logPiV l)

def FixedLPointwise : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 →
  (∀ L₀ : ℕ, ∃ l : ℕ, L₀ ≤ l ∧ l.Prime ∧
    ∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ S ∈ triples l,
      AS l S x + 2 * Al l x ≤ tripleMainTerm l S x + C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def FixedLW3 : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 →
  (∀ L₀ : ℕ, ∃ l : ℕ, L₀ ≤ l ∧ l.Prime ∧
    ∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ m : ℕ, 0 < m ∧ x ^ (1 - θ - ε) ≤ m ∧
      ∀ S ∈ triples l,
        chebyshevWeightedAverage m x (fun y => AS l S y + 2 * Al l y) ≤ chebyshevWeightedAverage m x (tripleMainTerm l S) + C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

example : triples 3 = {(1, 1, 1)} := by decide
example : saw (1 / 2) = 0 := by norm_num [saw]
example (y : ℝ) : saw (y + 1) = saw y := by simp [saw]

def Theorem7 : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∀ L₀ : ℕ, ∃ l : ℕ, L₀ ≤ l ∧ l.Prime ∧
    ∀ S ∈ triples l, ∀ x : ℝ, (l : ℝ) ^ (1 / ε) ≤ x → x ≤ (l : ℝ) ^ (1300 / ε) →
      AS l S x + 2 * Al l x ≤ tripleMainTerm l S x + x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def PrimesLL : Prop :=
  ∀ K : ℝ, 0 < K → ∀ L₀ : ℕ, ∃ l : ℕ, L₀ ≤ l ∧ l.Prime ∧ l % 4 = 3 ∧
    ∀ p : ℕ, p.Prime → p ∣ (l - 1) / 2 → K * Real.log l ≤ p

end Formalism.FX
end
end

section
open Complex

noncomputable section

namespace Formalism.FX

open Classical

def allChars (l : ℕ) [NeZero l] : Finset (DirichletCharacter ℂ l) := @Finset.univ _ (Fintype.ofFinite _)

def IX {l : ℕ} (χ : DirichletCharacter ℂ l) (X : ℕ) : ℂ := ∑ x ∈ Finset.Icc 1 X, χ (x : ZMod l)

def LFunZero : Prop :=
  ∀ (l : ℕ) [NeZero l], l.Prime → ∀ χ : DirichletCharacter ℂ l, χ ≠ 1 →
    DirichletCharacter.LFunction χ 0 = -(1 / (l : ℂ)) * ∑ x ∈ Finset.Ioo 0 l, χ (x : ZMod l) * (x : ℂ)

def Lerch : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ 1 →
    HasDerivAt (fun s : ℂ => HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s)
      (((Real.log (Real.Gamma a) - Real.log (2 * Real.pi) / 2 : ℝ)) : ℂ) 0

def LogDerivZeroOdd : Prop :=
  ∀ (l : ℕ) [NeZero l], l.Prime → ∀ χ : DirichletCharacter ℂ l, χ.Odd →
    DirichletCharacter.LFunction χ 0 ≠ 0 ∧
    deriv (DirichletCharacter.LFunction χ) 0 / DirichletCharacter.LFunction χ 0 =
      (Real.eulerMascheroniConstant : ℂ) + (Real.log (2 * Real.pi / l) : ℂ) -
        deriv (DirichletCharacter.LFunction χ⁻¹) 1 / DirichletCharacter.LFunction χ⁻¹ 1

def Gordan : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ) (v : ι → Fin n → ℝ),
    (∃ ν : ι → ℝ, (∀ i, 0 ≤ ν i) ∧ ∑ i, ν i = 1 ∧ ∀ j, ∑ i, ν i * v i j = 0) ∨
    ∃ w : Fin n → ℝ, ∀ i, 0 < ∑ j, w j * v i j

def PositivityBound : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ l : ℕ, 3 ≤ l → Odd l → ∀ φ : ℕ → ℝ,
    (∀ x, 0 < x → x < l → φ (l - x) = -φ x) →
    (∀ S ∈ triples l, 0 < φ S.1 + φ S.2.1 + φ S.2.2) →
    ∃ X : ℕ, 1 ≤ X ∧ X ≤ (l - 1) / 2 ∧
      (X : ℝ) * ∑ x ∈ Finset.Ioo 0 l, φ x ^ 2 ≤
        K * (1 + Real.log l) * (∑ x ∈ Finset.Icc 1 X, φ x) ^ 2

def ParsevalHolder : Prop :=
  ∀ (l : ℕ) [NeZero l], l.Prime → ∀ (BB : Finset (DirichletCharacter ℂ l))
    (a : DirichletCharacter ℂ l → ℂ) (X : ℕ),
    ‖∑ x ∈ Finset.Icc 1 X, ∑ χ ∈ BB, a χ * χ (x : ZMod l)‖ ^ 2 ≤
      (∑ x ∈ Finset.Ioo 0 l, ‖∑ χ ∈ BB, a χ * χ (x : ZMod l)‖ ^ 2) / ((l : ℝ) - 1) *
        Real.sqrt BB.card * Real.sqrt (∑ χ ∈ BB, ‖IX χ X‖ ^ 4)

def DivisorBound : Prop :=
  ∀ e : ℝ, 0 < e → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ((Nat.divisors n).card : ℝ) ≤ C * (n : ℝ) ^ e

def M4 : Prop :=
  ∀ e : ℝ, 0 < e → ∃ C : ℝ, ∀ (l : ℕ) [NeZero l], l.Prime → ∀ X : ℕ, X ≤ l →
    ∑ χ ∈ (allChars l).filter (· ≠ 1), ‖IX χ X‖ ^ 4 ≤ C * (l : ℝ) ^ (1 + e) * (X : ℝ) ^ 2

def PolyaVinogradov : Prop :=
  ∃ K : ℝ, ∀ (l : ℕ) [NeZero l], l.Prime → ∀ χ : DirichletCharacter ℂ l, χ ≠ 1 → ∀ M N : ℕ,
    ‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod l)‖ ≤ K * Real.sqrt l * (1 + Real.log l)

def LPartialSum : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ B : ℝ,
    (∀ M : ℕ, ‖∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q)‖ ≤ B) →
    ∀ s : ℂ, 0 < s.re → ∀ N : ℕ, 1 ≤ N →
      ‖DirichletCharacter.LFunction χ s - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤
        2 * B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re)

def SubMeanDisc : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → ∀ (z : ℂ) (r : ℝ), 0 < r →
    ‖f z‖ ^ 2 ≤ (1 / (Real.pi * r ^ 2)) * ∫ w in Metric.ball z r, ‖f w‖ ^ 2

def CharOrtho : Prop :=
  ∀ (l : ℕ) [NeZero l], l.Prime → ∀ (b : ℕ → ℂ) (Y : ℕ),
    ∑ χ ∈ allChars l, ‖∑ n ∈ Finset.Ioc Y l, b n * χ (n : ZMod l)‖ ^ 2 ≤
      ((l : ℝ) - 1) * ∑ n ∈ Finset.Ioc Y l, ‖b n‖ ^ 2

def LConj : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ s : ℂ,
    DirichletCharacter.LFunction χ⁻¹ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (DirichletCharacter.LFunction χ s)

def AlAsymp : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ y : ℝ, 1 ≤ y →
    0 ≤ y * Real.log l / ((l : ℝ) - 1) - Al l y ∧
      y * Real.log l / ((l : ℝ) - 1) - Al l y ≤ 2 * Real.log l + Real.log y

end Formalism.FX
end
end
