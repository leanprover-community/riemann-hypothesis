module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundLargeConductor
public import Formalism.PolynomialDimension.DigitClassSize
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

namespace Dat

variable (X : Dat) (K : Cst)

def ua : ℕ := ⌊X.ar + X.ar / (X.k * X.Y)⌋₊

def lb : ℕ := ⌈X.bl⌉₊

def ub : ℕ := ⌊X.bu⌋₊

def Wa (τ : ℕ) : Finset ℕ := Finset.Icc (X.a + τ) (X.ua + τ)

def Wb (τ : ℕ) : Finset ℕ := Finset.Icc (X.lb + τ) (X.ub + τ)

def WaP : Finset ℕ := Finset.Icc X.a (X.ua + X.Jn K + X.ccl)

def WbP : Finset ℕ := Finset.Icc X.lb (X.ub + X.Jn K + X.ccl)

end Dat

def meanN {ι : Type} [Fintype ι] [DecidableEq ι] (Sa Sb : Finset ℕ) (f : (ι → ℕ) → (ι → ℕ) → ℝ) : ℝ :=
  (∑ A ∈ Fintype.piFinset (fun _ : ι => Sa), ∑ B ∈ Fintype.piFinset (fun _ : ι => Sb), f A B) /
    ((Sa.card : ℝ) ^ Fintype.card ι * (Sb.card : ℝ) ^ Fintype.card ι)

def RestDims : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 1 ≤ m → ∀ (TT : Finset (Fin n')) (A B : TT → ℕ),
    dimHH (m := m) R.Kf TT (ex A) (ex B) = ∏ s, Formalism.CountingSumsFrames.dimPol m (A s) * Formalism.CountingSumsFrames.dimPol m (B s) ∧
    dimV R.Kf (flatW m A B) = ∏ s, Formalism.CountingSumsFrames.dimHar m (A s) (B s)

def KeyIneq (K : Cst) (X : Dat) (R : RS X.p X.n') : Prop :=
  ∀ A ∈ Fintype.piFinset (fun _ : X.TT => X.WaP K), ∀ B ∈ Fintype.piFinset (fun _ : X.TT => X.WbP K),
    ∑ j ∈ Fintype.piFinset (fun _ : X.TT => Finset.range (X.Jn K + 1)),
        X.kF K R (fun s => A s - j s) (fun s => B s - j s) *
          dL R (flatW X.m (fun s => A s - j s) (fun s => B s - j s)) ≤
      X.kx K R A B * ((dimHH (m := X.m) R.Kf X.TT (ex A) (ex B) : ℝ) / gaussianNumber (X.p ^ X.n') (X.m + 1))

def Avg (K : Cst) (X : Dat) (R : RS X.p X.n') (τ : ℕ) : Prop :=
  meanN (X.Wa τ) (X.Wb τ) (X.kF K R) ≤ 2 * meanN (X.WaP K) (X.WbP K) (X.kx K R)

def MeanX (K : Cst) (X : Dat) (R : RS X.p X.n') : Prop :=
  meanN (X.WaP K) (X.WbP K) (X.kx K R) ≤ (K.CA + K.Cs) * X.N * X.N₁ / X.Y

def MidMean (D : Formalism.BasicNotions.D7) (K : Cst) (F : Dat → Prop) : Prop :=
  K.admitted D → ∀ X : Dat, F X → ∀ R : RS X.p X.n',
    meanKap X.TT X.m X.Y X.ar X.bl X.bu (X.kText K R) ≤ K.Cmean * X.TT.card * X.N₁ / X.Y

end Formalism.MainNotions.flipOneThree.Pf

end
