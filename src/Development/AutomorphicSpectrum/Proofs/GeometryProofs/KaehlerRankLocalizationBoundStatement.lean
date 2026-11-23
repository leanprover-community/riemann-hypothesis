module

public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankLocalizationBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.kaehler_rank_localization_bound : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type) [Finite σ']
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (e r : ℕ) (bd : Ideal (MvPolynomial σ ℤ)), Module.finrank Ω (KaehlerDifferential Ω₀ Ω) = r →
    ∀ (h : Ω₀), h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert h⁻¹ (Set.range r₀)) →
    T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (Set.range r₁)) →
    ∀ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) → ψ.Smooth →
    IsFractionRing S Ω₀ → IsFractionRing T Ω → Algebra.Smooth ℚ S →
    ∀ (z : Fin e → S) (n : ℕ), n ≤ e → LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) →
    ∀ (P : Ideal (Algebra.adjoin ℚ (Set.range r₁))), P.IsPrime →
    ∀ h₁ : Algebra.adjoin ℚ (Set.range r₁), (h₁ : Ω) = algebraMap Ω₀ Ω h → h₁ ∉ P →
    ∃ t : Algebra.adjoin ℚ (Set.range r₁), t ∉ P ∧ ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range r₁)) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + r) → S') (n' : ℕ), n' ≤ e + r ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
            ∃ i : Fin (e + r), (i : ℕ) < n' ∧ z' i ∈ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocalStep.local_step | exact GlobalTheory.CompanionTheory.Ar.LocalStep.local_step | (intros; apply GlobalTheory.CompanionTheory.Ar.LocalStep.local_step <;> assumption)
