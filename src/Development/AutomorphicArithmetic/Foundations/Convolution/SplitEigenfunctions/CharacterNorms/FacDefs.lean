module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

def pv (v : H.P ℚ) : (A ℚ)ˣ := H.idl v (atFin v (unif v))

def pin (n : ℕ) : (A ℚ)ˣ := ∏ᶠ v : H.P ℚ, pv v ^ (n.factorization (normV v))

def TT (L : ℕ) : Set (A ℚ)ˣ := {t | t ∈ UU ∧ ∀ v, Dv L v ((t : A ℚ) - 1)}

def cT (L : ℕ) : ℝ := (finiteIdeleMeasure ℚ ((fun u => (IdeleGroup.prodEquiv ℚ).symm (1, u)) ⁻¹' TT L)).toReal

def SS (N : ℕ) : Set (G1 ℚ) := {k | ∀ v, Dv N v (k 1 0)}

def cK (M : Meas ℚ) (N : ℕ) : ℝ := (M.κ (SS N ∩ KK ℚ)).toReal

def sqN (N : ℕ) (n : ℕ) : ℂ := if ∃ m : ℕ, n = m * m ∧ m.Coprime N then 1 else 0

def bN (N : ℕ) (χ : HChar ℚ) (μ : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n.Coprime N then (n : ℂ) * ((χ.1 (pin n) : ℂˣ) : ℂ) * μ n else 0

variable {E : Type} [Field E] [NumberField E]

def Yt (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (s : ℂ) (g : GL (Fin 2) (A ℚ)) : ℂ :=
  ∫ y : IdeleGroup ℚ, Wo D φ (em E (aE y * g)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1) ∂(ideleMeasure ℚ)

def It (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (s : ℂ) (t : ℝ) : ℂ :=
  ∫ y : ℝ, Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ 0 * ((|y| : ℝ) : ℂ) ^ (s - 2)

def Zr (N : ℕ) (p : MvPolynomial (Fin 2) ℂ) (s : ℂ) (k : G1 ℚ) : ℂ :=
  ∫ z : IdeleGroup ℚ, (PhiN N p fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s) ∂(ideleMeasure ℚ)

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
