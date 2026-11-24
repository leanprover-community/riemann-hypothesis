module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice

def join {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) : Fin (D + 1) × Fin N → R :=
  fun p => Fin.lastCases (motive := fun _ => R) (ξ p.2) (fun i => u i p.2) p.1

def spec {F E : Type} [CommRing F] [CommRing E] [Algebra F E] {D N : ℕ} (s : Fin D → Fin N → E)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : MvPolynomial (Fin 1 × Fin N) E :=
  aeval (join (fun i j => C (s i j)) fun j => X (0, j)) f

def lin {K : Type} [CommRing K] {N : ℕ} (y : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K := ∑ j, X ((0 : Fin 1), j) * C (y j)

def finPart {K ι : Type} [Field K] [NumberField K] (g : MvPolynomial ι K) : ℝ :=
  (∑ᶠ v : FinitePlace K, Real.log (gaussAbs v g)) / (Module.finrank ℚ K : ℝ)

def mean (K : Type) [Field K] [NumberField K] (a : (K →+* ℂ) → ℝ) : ℝ := (∑ τ, a τ) / (Module.finrank ℚ K : ℝ)

structure ShortLat {F : Type} [Field F] [NumberField F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ) : Prop where
  pos : 0 < N
  spans : Submodule.span F (Set.range w.col) = ⊤
  int : ∀ u ∈ Submodule.span (𝓞 F) (Set.range w.col), u ∈ Submodule.span ℤ (Set.range w.col)
  det : ∀ σ, (A σ).det ≠ 0
  conj : ConjCompat A
  le : ∀ k σ, frameNorm (A σ) (fun j => σ (w j k)) ≤ Λ
  one_le : 1 ≤ Λ

def NoSquare {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin 1 × Fin N) K) : Prop :=
  g ≠ 0 ∧ ∀ y : Fin N → K, y ≠ 0 → ¬ lin y ^ 2 ∣ g

theorem join_last {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (j : Fin N) : join u ξ (Fin.last D, j) = ξ j := by
  simp [join]

theorem join_castSucc {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (i : Fin D) (j : Fin N) :
    join u ξ (i.castSucc, j) = u i j := by
  simp [join]

namespace Check

theorem lin_ne {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : lin y ≠ 0 := by
  intro h
  apply hy
  funext j
  have := congrArg (eval (fun p : Fin 1 × Fin N => if p.2 = j then (1:K) else 0)) h
  simpa [lin] using this

end Check

end GlobalTheory.HSChoice
