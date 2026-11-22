module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.BindPow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison

def G2s : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ lam : InfinitePlace E → DomWeight n, ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℕ) (l₁ : ∀ i, InfinitePlace E → DomWeight (a i))
    (l₂ : ∀ i, InfinitePlace E → DomWeight (n - a i)) (sg : ι → ℤˣ),
    (∀ i, a i ≤ n ∧ ∀ v, (infOfWeight (l₁ i v)).map (· + ((n - a i : ℕ) : ℂ) * (e v : ℂ) / 2) +
      (infOfWeight (l₂ i v)).map (· + (a i : ℂ) * (e v : ℂ) / 2) = infOfWeight (lam v)) ∧
    (∃ i, a i = n ∧ sg i = 1 ∧ ∀ j, a j = n → j = i) ∧ (∃ i, a i = 0 ∧ sg i = 1 ∧ ∀ j, a j = 0 → j = i) ∧
    ∀ S : Set (Pl E), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
      (φ : ∀ a (w : Pl E), GLw a w × GLw (n - a) w → ℂ), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
      GlobalTheory.BCT.IsTest (KL n) K' f → (∀ a ≤ n, IsTestP (φ a) ∧ ∀ w ∈ S, Match n a (n - a) w (μ.loc w) (f w) (φ a w)) →
      geomU S lam f = ∑ i, ((sg i : ℤ) : ℂ) * geomSt2 S (l₁ i) (l₂ i) (φ (a i))

def MuEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e

def MatchUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∀ n a b : ℕ, a + b = n →
  Match n a b w 1 ((KL n w : Set (UL n w)).indicator 1) ((K2 a b w : Set _).indicator 1)

def MatchSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), IsSplitAt w → ∀ (n a b : ℕ) (h : a + b = n) (μ : HChar E) (f : UL n w → ℂ),
  Lc (KL n w) f → Lc (K2 a b w) (ctMu h w (μ.loc w) f) ∧ Match n a b w (μ.loc w) f (ctMu h w (μ.loc w) f)

def Peak : Prop := ∀ (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B] (H : Type) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] (R : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (A : StarSubalgebra ℂ B) (p : A →⋆ₐ[ℂ] ℂ) (a₀ : A) (x : B)
  (ρ : ℝ), p a₀ = 1 → 0 < ρ →
  (∀ s : B →⋆ₐ[ℂ] ℂ, (∀ y, ‖s y‖ ≤ ‖R y‖) → (∀ a : A, s a = p a) → ‖s x‖ < ρ) →
  ∃ g : A, p g = 1 ∧ ‖R (x * (g * a₀ : A))‖ < ρ

end UpperTheory.V.Z.Tf.GlobalTraceComparison
