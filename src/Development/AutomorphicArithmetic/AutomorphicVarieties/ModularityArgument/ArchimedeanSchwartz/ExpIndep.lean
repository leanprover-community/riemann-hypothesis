module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.HenQ

namespace UpperTheory.V.Z.Inf

def IsExp (f : ℂ → ℂ) : Prop := ∃ (T : Finset ℝ) (a : ℝ → ℂ), ∀ s, f s = ∑ t ∈ T, a t * Complex.exp (t * s)

def linPoly (m : Multiset ℂ) : ℂ[X] := (m.map fun z => X + C z).prod

def cx {P : Type} (B : P → Multiset ℂˣ) (w : P) : Multiset ℂ := (B w).map fun b : ℂˣ => (b : ℂ)

def ExpAlg : Prop :=
  (∀ f, IsExp f → Differentiable ℂ f) ∧ (∀ f g, IsExp f → IsExp g → IsExp fun s => f s * g s) ∧
    (∀ c : ℂ, IsExp fun _ => c) ∧ (∀ f (z : ℂ), IsExp f → IsExp fun s => f (s + z)) ∧
    ∀ (p : ℂ[X]) (t : ℝ) (z : ℂ), IsExp fun s => p.eval (Complex.exp (t * (s + z)))

def ExpIndep : Prop :=
  ∀ (p q : ℂ[X]) (U V : ℂ → ℂ), IsExp U → IsExp V → U ≠ 0 → (∀ s, p.eval s * U s = q.eval s * V s) →
    ∃ u v : ℂ, u ≠ 0 ∧ C u * p = C v * q

def Regroup : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M], Module.finrank K M = 2 →
    ∀ (MainNotions : Set (HeightOneSpectrum (𝓞 K))) (SM : Set (HeightOneSpectrum (𝓞 M))) (BK : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
      (BM : HeightOneSpectrum (𝓞 M) → Multiset ℂ) (c₀ : ℝ) (r : ℕ), (∀ w, w ∈ SM ↔ w.under (𝓞 K) ∈ MainNotions) →
    (∀ p ∉ MainNotions, Multiset.card (BK p) ≤ r ∧ ∀ b ∈ BK p,
      ‖b‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ c₀ ∧ ‖b⁻¹‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ c₀) →
    (∀ w ∉ SM, Multiset.card (BM w) ≤ r ∧ ∀ b ∈ BM w,
      ‖b‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀ ∧ ‖b⁻¹‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀) →
    (∀ w ∉ SM, (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ∧ ∃ w', w' ≠ w ∧
        w'.under (𝓞 K) = w.under (𝓞 K) ∧ BK (w.under (𝓞 K)) = BM w + BM w') ∨
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 ∧ ∃ B' : Multiset ℂ,
        BM w = B'.map (· ^ 2) ∧ BK (w.under (𝓞 K)) = B' + B'.map Neg.neg)) →
    ∃ c : ℝ, ∀ s : ℂ, (c < s.re → eulerL K BK MainNotions s = eulerL M BM SM s) ∧ (s.re < -c → eulerLd K BK MainNotions s = eulerLd M BM SM s)

end UpperTheory.V.Z.Inf
