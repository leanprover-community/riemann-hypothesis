module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Ix (n : ℕ) := Bool × Fin n × Fin n

def hm (p : Ix n) : Mat n :=
  if p.1 then Matrix.single p.2.1 p.2.2 1 + Matrix.single p.2.2 p.2.1 1
  else Matrix.single p.2.1 p.2.2 Complex.I - Matrix.single p.2.2 p.2.1 Complex.I

def sk (p : Ix n) : Mat n :=
  if p.1 then Matrix.single p.2.1 p.2.2 1 - Matrix.single p.2.2 p.2.1 1
  else Matrix.single p.2.1 p.2.2 Complex.I + Matrix.single p.2.2 p.2.1 Complex.I

section Calc

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

def Rr (X : Mat n) (f : Mat n → W) : Mat n → W := fun g => fderiv ℝ f g (g * X)

def Sm (u : ℝ → Mat n → W) : Prop := ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)

def dt (u : ℝ → Mat n → W) : ℝ → Mat n → W := fun s y => deriv (fun r => u r y) s

def Rt (X : Mat n) (u : ℝ → Mat n → W) : ℝ → Mat n → W := fun s => Rr X (u s)

def dens (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) : ℝ :=
  ‖dt u s y‖ ^ 2 + (1 / 4) * ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 + ‖u s y‖ ^ 2

end Calc

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : GLs n = (fun g : Mat n => g.det) ⁻¹' {0}ᶜ := by ext g; simp [GLs]
  rw [this]
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det continuous_id)

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  exact this.ne_zero

end GlobalTheory.CompanionTheory.WaveSpd
