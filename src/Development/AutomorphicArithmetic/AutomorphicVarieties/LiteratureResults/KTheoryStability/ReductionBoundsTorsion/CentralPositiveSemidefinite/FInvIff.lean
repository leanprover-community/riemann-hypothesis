module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.CentralizerFixed

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

def pb {q : ℕ} (g : Gp L N) (ω : Form (HS L N) q) : Form (HS L N) q :=
  fun h => (ω (actL g h)).compContinuousLinearMap (actL g)

def sc (t : InfinitePlace L → ℝ) : Gp L N :=
  scal L N fun w => Units.mk0 ((Real.exp (t w) : ℝ) : ℂ) (by exact_mod_cast (Real.exp_pos (t w)).ne')

def av {q : ℕ} (v : InfinitePlace L → ℝ) (ω : Form (HS L N) q) : Form (HS L N) q :=
  fun h => ∫ τ in (0 : ℝ)..1, pb (sc (τ • v)) ω h

def Fix {q : ℕ} (ω : Form (HS L N) q) : Set (InfinitePlace L → ℝ) :=
  {t | ∀ h ∈ Pos L N, pb (sc t) ω h = ω h}

def lg (u : (𝓞 L)ˣ) : InfinitePlace L → ℝ := fun w => Real.log (w ((u : 𝓞 L) : L))

end PositivityTheory.KB.CentralizerFixed

end
