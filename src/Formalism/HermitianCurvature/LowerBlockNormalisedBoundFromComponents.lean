module

public import Formalism.HermitianCurvature.LevelRecursionCondNeeded
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

namespace Formalism.FourierDecayAlt.PairingProductCorollary

open Finset
open scoped ComplexOrder

noncomputable section

def cg {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (a : Fin K) : ℝ :=
  ∑ i, |F7.lagCo (grid a) i|

def coProd {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, F7.lagCo (grid a) (j a)

def qProd {K d : ℕ} (q : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (grid : Fin K → Fin (d + 1) → ℝ)
    (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, F7.qW q w (grid a (j a))

def nnProd {K d : ℕ} (nn : ℝ → ℝ) (h : ℝ) (grid : Fin K → Fin (d + 1) → ℝ)
    (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, nn (grid a (j a) + h)

def LowerBlockNormalisedBoundFromComponents : Prop :=
  ∀ (K d : ℕ) (grid : Fin K → Fin (d + 1) → ℝ) (q nn : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (o W0 : ℂ)
    (RL RV : (Fin K → Fin (d + 1)) → ℝ) (wt wt' bw Qw BB : ℝ),
    (∀ a, Function.Injective (grid a)) →
    (∀ a i, 0 < q (grid a i) ∧ 0 < F7.qW q w (grid a i) ∧ 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1)) →
    (∀ a i, q (grid a i) ≤ Qw * F7.qW q w (grid a i)) →
    (∀ a i, nn (grid a i) * nn (grid a i + 1) / q (grid a i) ≤ BB ^ 2) →
    0 ≤ BB → 0 ≤ wt → 0 ≤ wt' → 0 < bw → (∀ j, 0 ≤ RL j ∧ 0 ≤ RV j) →
    ‖o‖ ^ K * ‖W0‖ ≤ ∑ j, |coProd grid j| * Real.sqrt (RL j * RV j / qProd q w grid j) →
    ‖o‖ ^ K * (wt * wt' / bw * ‖W0‖) ≤
      (∏ a, cg grid a) * (Real.sqrt Qw * BB) ^ K *
        ∑ j, F7.thGrid grid j *
          ((wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) + wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j)) / 2)

def PairingGramInequality (Ntt : ℂ) (Nt Nt' : ℝ) : Prop := ‖Ntt‖ ^ 2 ≤ Nt * Nt'

def minFac (L o : ℝ) (K : ℕ) : ℝ := if L < o then (L / o) ^ K else 1

def oAbs {ι : Type} (t t' : ι → ℂ) (v : ι) : ℝ := ‖1 / t v - 1 / t' v‖

def LeadingBlockSeveralPlacesBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (K : ℕ) (abelian₂ : ι → ℝ) (t t' : ι → ℂ) (Ntt : ℂ)
    (Nt Nt' S1 S2 : ℝ),
    (∀ v, t v ≠ 0 ∧ t' v ≠ 0) → (∀ v, 0 ≤ abelian₂ v) → 0 ≤ Nt → 0 ≤ Nt' → 0 ≤ S1 → 0 ≤ S2 →
    PairingGramInequality Ntt Nt Nt' →
    Nt ≤ (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖),
      (‖t v‖ * abelian₂ v) ^ (2 * K)) * S1 →
    Nt' ≤ (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖),
      (‖t' v‖ * abelian₂ v) ^ (2 * K)) * S2 →
    ‖Ntt‖ ≤ (∏ v, minFac (2 * abelian₂ v) (oAbs t t' v) K) * ((S1 + S2) / 2)

end

end Formalism.FourierDecayAlt.PairingProductCorollary
