module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes

@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

def fd {r : ℕ} (i : Fin r) (g : (Fin r → ℕ) → ℂ) : (Fin r → ℕ) → ℂ :=
  fun m => g (m + Pi.single i 1) - g m

def DL {r : ℕ} (cs : List (Fin r)) (g : (Fin r → ℕ) → ℂ) : (Fin r → ℕ) → ℂ := cs.foldr fd g

def fdR {r : ℕ} (i : Fin r) (G : (Fin r → ℝ) → ℂ) : (Fin r → ℝ) → ℂ :=
  fun x => G (x + Pi.single i 1) - G x

def DLR {r : ℕ} (cs : List (Fin r)) (G : (Fin r → ℝ) → ℂ) : (Fin r → ℝ) → ℂ := cs.foldr fdR G

def GoodAt (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) : Prop :=
  (∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) ∧
    ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single i e : Fin r → ℕ)) = 0

def BddW {r : ℕ} (v : (Fin r → ℕ) → ℚ) : Prop := ∃ C : ℝ, ∀ m, |(v m : ℝ)| ≤ C

def partialSum {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m i), v (Function.update m i k)

def meanP (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  (∑ k ∈ Finset.range l, partialSum i v (Function.update m i k)) / l

def Aop (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  partialSum i v (m + Pi.single i 1) - meanP l i v m

def Bop (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  if m i = 0 then meanP l i v m else 0

def linF {ι : Type} {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι) (x : Fin r → ℝ) : ℝ :=
  b j + ∑ i, a j i * x i

def Fr {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (β : ι → ℕ) (x : Fin r → ℝ) : ℂ :=
  ∏ j, ((linF a b j x : ℝ) : ℂ) ^ (-s - (β j : ℂ))

def sizeE {r : ℕ} (x : Fin r → ℝ) : ℝ := 1 + ∑ i, x i

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
