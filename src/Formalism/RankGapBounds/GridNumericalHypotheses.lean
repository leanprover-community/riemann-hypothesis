import Mathlib
import Formalism.RankGapBounds.RandomSubsetCounterexample

section
namespace Formalism.RankGapBounds.AbsolutelyIrreducibleSpan

structure Hyp (k m t r N : ℕ) (h₀ : ℝ) : Prop where
  k_even : Even k
  m_even : Even m
  m_pos : 1 ≤ m
  r_def : r + 1 = k + m
  k_ge : m + 3 ≤ k
  t_odd : Odd t
  t_gt_m : 3 * m < t
  t_gt_r : r + 4 < t
  N_def : N = k + m * (t + r + 8)
  h₀_big : (t : ℝ) + 2 * (N : ℝ) ^ 3 < h₀

def SChoice : Prop :=
  ∀ (k m t r N s : ℕ) (h₀ : ℝ), Hyp k m t r N h₀ →
    ((Odd s ∧ r + 5 < s ∧ s ≤ r + 7) ↔ s = r + 6)

def GridParity : Prop :=
  ∀ (k m t r N : ℕ) (h₀ : ℝ), Hyp k m t r N h₀ →
    Odd r ∧ Even (t + (r + 6)) ∧
    (∀ i j : ℕ, Even (r + j * t + i * (r + 6)) ↔ Odd (i + j)) ∧
    (∀ i : ℕ, Even ((r + 1) + i * (r + 6 - 1))) ∧
    (∀ i j : ℕ, 1 ≤ j →
      Even ((r + j * t + i * (r + 6)) + (r + (j - 1) * t + (i + 1) * (r + 6))))

def SumShortForm : Prop :=
  ∀ m t s : ℕ, 3 * m < t → m + 3 ≤ s → 4 * m + 2 < t + s

def SquareDepth : Prop :=
  ∀ (k m t r N : ℕ) (h₀ : ℝ), Hyp k m t r N h₀ →
    m + 3 ≤ r + 6 ∧ 4 * m + 2 < t + (r + 6) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ m → 2 * (m - j) + 1 < (t + (r + 6)) / 2) ∧
    2 * m + 1 < (t + (r + 6)) / 2

def SquareIndexSum : Prop :=
  ∀ m j : ℕ, j ≤ m → (m - j) / 2 + (m - j + 1) / 2 = m - j

def SquareRank : Prop :=
  ∀ (k m t r N : ℕ) (h₀ : ℝ), Hyp k m t r N h₀ →
    ∀ i j : ℕ, i < m → 1 ≤ j → j ≤ m →
      2 * m + 1 < r + (j - 1) * t + i * (r + 6)

def CornerIff : Prop :=
  ∀ (k m t r N : ℕ) (h₀ : ℝ), Hyp k m t r N h₀ →
    (2 * (m - 1) + 1 < r ↔ m < k) ∧ (2 * m + 1 < r ↔ m + 2 < k)

def CornerForced : Prop :=
  ∀ (k m t r N : ℕ) (h₀ : ℝ), Hyp k m t r N h₀ → 2 * (m - 1) + 1 < r ∧ 2 * m + 1 < r

def RankGaps : Prop :=
  ∀ (k m t r N : ℕ) (h₀ : ℝ), Hyp k m t r N h₀ →
    (∀ j : ℕ, 1 ≤ j → j ≤ m → 2 ≤ t ∧ (m - j) / 2 < t) ∧
    (∀ j : ℕ, j ≤ m → (m - j) / 2 < r + 6) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ m → 2 ≤ r + 6 - 1 ∧ (m - i + 1) / 2 < r + 6 - 1)

def SiegelWeilRanges : Prop :=
  ∀ (k m t r N : ℕ) (h₀ : ℝ), Hyp k m t r N h₀ →
    2 * ((r + 1) + 0 * (r + 5)) < (r + 1) + 1 * (r + 5) ∧ r + 1 < r + 6 - 1 ∧ r < r + 6 - 2 ∧
    ∀ i : ℕ, 2 ≤ i → i ≤ m →
      (r + 1) + (i - 1) * (r + 5) < (r + 1) + i * (r + 5) ∧
      (r + 1) + i * (r + 5) ≤ 2 * ((r + 1) + (i - 1) * (r + 5)) ∧
      (m - i + 1) / 2 ≤ (r + 1) + (i - 1) * (r + 5)

def RankAndGapBounds : Prop :=
  ∀ (k m t r N : ℕ) (h₀ γ : ℝ), Hyp k m t r N h₀ →
    2 * ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 + 2 * ((r + 6 : ℕ) : ℝ) + 2 < γ →
    k + m * (t + (r + 6) + 1) ≤ N ∧
    (∀ i j : ℕ, i ≤ m → j ≤ m → r + j * t + i * (r + 6) < k + m * (t + (r + 6) + 1)) ∧
    (∀ i : ℕ, i ≤ m → (r + 1) + i * (r + 5) < k + m * (t + (r + 6) + 1)) ∧
    (∀ M : ℕ, M < k + m * (t + (r + 6) + 1) →
      (M : ℝ) ^ 3 < (h₀ - t) / 2 ∧ (M : ℝ) ^ 3 < γ / 2 - ((r + 6 : ℕ) : ℝ)) ∧
    (((r + 6 : ℕ) : ℝ) + 1) / 2 ≤ γ / 2 - 1 ∧ ((r + 6 : ℕ) : ℝ) / 2 ≤ γ / 2 - 1 ∧
    γ / 2 - ((r + 6 : ℕ) : ℝ) ≤ γ / 2 - 1 - (((r + 6 : ℕ) : ℝ) - 1) / 2

def GammaLarge : Prop :=
  ∀ C Ns n Λ : ℝ, 2 ≤ C → 0 ≤ Ns → 2 ≤ n → 0 ≤ Λ →
    2 * Ns ^ 3 + 2 * (n + 5) + 2 < C * Ns ^ 3 + C * n ^ 7 + C * n ^ 3 * Real.sqrt Λ

def DecayHypothesis : Prop :=
  ∀ n m γ : ℝ, 3 ≤ n → 1 ≤ m → m ≤ n → n ^ 7 ≤ γ →
    48 * n ^ 2 * Real.sqrt m ≤ γ ∧ 40 * n * (m / 2) ≤ γ

def DecayToNorm : Prop :=
  ∀ n m γ X G : ℝ, 2 ≤ n → 1 ≤ m → 48 * n ^ 2 * Real.sqrt m ≤ γ → 0 ≤ X → 0 < G →
    G ≤ Real.sqrt n * Real.exp X →
    Real.exp (-(γ / 8) * min (X ^ 2) (X / Real.sqrt m)) ≤
      Real.exp (12 * n ^ 2 * Real.log n) * G ^ (-(6 * n ^ 2))

def DegreeEven : Prop :=
  ∀ (G : Type) [CommGroup G] [Fintype G] (c : G) (I : Subgroup G)
    (φ : G →* Multiplicative (ZMod 2)) (f : ℕ),
    Fintype.card G = 2 * f → orderOf c = 2 → c ∉ I → (∃ g ∈ I, φ g ≠ 1) → Even f

def OneRationalForm : Prop :=
  ∀ (L K EE : Type) [Field L] [Field K] [Algebra L K] [AddCommGroup EE] [Module K EE]
    [Module L EE] [IsScalarTower L K EE] [FiniteDimensional K EE]
    (d : ℕ) (Ψ : EE →ₗ[K] (Fin d → K)) (ι : Type) (A : ι → Set EE) (r : ι → L),
    Function.Injective Ψ →
    (∀ μ, Submodule.span K (A μ) = ⊤) →
    (∀ μ, ∀ a ∈ A μ, ∃ y : Fin d → L,
      Ψ a = (algebraMap L K (r μ))⁻¹ • (fun i => algebraMap L K (y i))) →
    ∃ EL : Submodule L EE,
      (∀ μ, Submodule.span L (A μ) = EL) ∧
      Submodule.span K (EL : Set EE) = ⊤ ∧
      ∀ s : Finset EE, (↑s : Set EE) ⊆ EL →
        LinearIndependent L (fun x : s => (x : EE)) → LinearIndependent K (fun x : s => (x : EE))

end Formalism.RankGapBounds.AbsolutelyIrreducibleSpan
end

section
namespace Formalism.RankGapBounds.ExistsSmulMemTer

abbrev G0 := ZMod 2 × ZMod 2
abbrev GG (e : ℕ) := G0 × ZMod (2 ^ e)

def sg : G0 := (1, 0)
def c0 : G0 := (0, 1)
def cc (e : ℕ) : GG e := (c0, 0)

def InPhi {e : ℕ} (γ : GG e) : Prop := γ.1.2 = 0

def place {e : ℕ} (γ : GG e) : GG e := if γ.1.2 = 0 then γ else γ + cc e

def OrbitParity : Prop :=
  ∀ (e : ℕ) (φ τ : GG e) (i : ℕ), φ.1.2 = 1 → InPhi τ → (InPhi (i • φ + τ) ↔ Even i)

def OrbitCoord : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)) (i : ℕ), (place (i • φ + ((0 : G0), t))).2 = t + i • φ.2

def OrbitOver : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)) (i : ℕ),
    (φ.1 = c0 → (place (i • φ + ((0 : G0), t))).1 = 0) ∧
    (φ.1 = sg + c0 → (place (i • φ + ((0 : G0), t))).1 = if Even i then 0 else sg)

def ConjInOrbit : Prop :=
  ∀ (e : ℕ) (φ : GG e), φ.1.2 = 1 → (cc e ∈ AddSubgroup.zmultiples φ ↔ φ = cc e)

def OrbitCard : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)), φ.1 = c0 → φ.2 ≠ 0 →
    (Set.range fun i : ℕ => place (i • φ + ((0 : G0), t))).ncard = addOrderOf φ.2 ∧
    Even (addOrderOf φ.2)

end Formalism.RankGapBounds.ExistsSmulMemTer
end

section
namespace Formalism.RankGapBounds.V4

open Formalism.RankGapBounds.LocalQuadraticParts Formalism.RankGapBounds.ExistsSmulMemTer

def RankGapPrintedLemma : Prop :=
  ∀ (α ι : Type) [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)],
    0 < δ → δ ≤ 1 → 16 ≤ δ * Fintype.card α → 0 ≤ β → (∀ p, 0 ≤ ω p) →
    (∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T), wt δ T ≤ β * δ) →
    ∃ T : Finset α, δ * Fintype.card α / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card α ∧
      ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ p, ω p

def ConjInOrbitAll : Prop :=
  ∀ (e : ℕ) (φ : GG e), cc e ∈ AddSubgroup.zmultiples φ ↔ φ = cc e

def RankGapDecayHypothesis : Prop :=
  ∀ n m γ : ℝ, 3 ≤ n → 1 ≤ m → m ≤ n → n ^ 7 ≤ γ →
    120 * n * (m / 2) ^ ((3 : ℝ) / 2) ≤ γ

structure GridNumericalHypotheses (k m t r : ℕ) (h₀ : ℝ) : Prop where
  k_even : Even k
  m_even : Even m
  m_pos : 1 ≤ m
  r_def : r + 1 = k + m
  k_ge : m + 3 ≤ k
  t_odd : Odd t
  t_gt_m : 3 * m < t
  t_gt_r : r + 4 < t
  h₀_big : (t : ℝ) + 2 * ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < h₀

def RankGapBoundPair : Prop :=
  ∀ (k m t r : ℕ) (h₀ γ : ℝ), GridNumericalHypotheses k m t r h₀ →
    2 * ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 + 2 * ((r + 6 : ℕ) : ℝ) + 2 < γ →
    (∀ i j : ℕ, i ≤ m → j ≤ m → r + j * t + i * (r + 6) < k + m * (t + (r + 6) + 1)) ∧
    (∀ i : ℕ, i ≤ m → (r + 1) + i * (r + 5) < k + m * (t + (r + 6) + 1)) ∧
    (∀ M : ℕ, M < k + m * (t + (r + 6) + 1) →
      (M : ℝ) ^ 3 < (h₀ - t) / 2 ∧ (M : ℝ) ^ 3 < γ / 2 - ((r + 6 : ℕ) : ℝ)) ∧
    ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < (h₀ - t) / 2 ∧
    ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < γ / 2 - ((r + 6 : ℕ) : ℝ) ∧
    (((r + 6 : ℕ) : ℝ) + 1) / 2 ≤ γ / 2 - 1 ∧ ((r + 6 : ℕ) : ℝ) / 2 ≤ γ / 2 - 1 ∧
    γ / 2 - ((r + 6 : ℕ) : ℝ) ≤ γ / 2 - 1 - (((r + 6 : ℕ) : ℝ) - 1) / 2

end Formalism.RankGapBounds.V4
end
