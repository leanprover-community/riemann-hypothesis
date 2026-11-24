module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GeometricAbelianConnected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
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

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.AI

def polar {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) (c : Fin n → σ → ℝ) : ℝ :=
  ∑ w : Fin n → σ, (∏ r, c r (w r)) * a w

namespace AnSq

variable {d : ℕ} {σ : Type} [Fintype σ] {SY : AnSys (d + 1) σ} {a₀ : σ} {ε : σ → ℤ} (Q : AnSq SY a₀ ε)

def pull0 (_Q : AnSq SY a₀ ε) (c : σ → ℝ) : Option σ → ℝ := fun o => o.elim 0 c


open Classical in
def pull1 (_Q : AnSq SY a₀ ε) (c : σ → ℝ) : Option σ → ℝ :=
  fun o => o.elim (c a₀) fun a => if a = a₀ then 0 else c a

def wcoef (c : σ → ℝ) (k i : ℕ) : Fin (d + 2) → Option σ → ℝ :=
  Fin.cons (α := fun _ => Option σ → ℝ) (Q.pull0 (fun a => (ε a : ℝ)) - Q.pull1 fun a => (ε a : ℝ))
    (word (d + 1) k i (Q.pull0 fun a => (ε a : ℝ)) (Q.pull1 fun a => (ε a : ℝ)) (Q.pull0 c))

def gT (t : ℝ) (x : Q.SW.X) : ℝ :=
  logNormSec Q.L' Q.v x + Q.cst + (1 / 2) * ∑ a, (ε a : ℝ) * (SY.phT a t (Q.q 0 x) + SY.phT a t (Q.q 1 x))

def gH (x : Q.SW.X) : ℝ :=
  logNormSec Q.L' Q.v x + Q.cst + (1 / 2) * ∑ a, (ε a : ℝ) * (SY.ph a (Q.q 0 x) + SY.ph a (Q.q 1 x))

end AnSq

end GlobalTheory.CompanionTheory.Ar.PB
