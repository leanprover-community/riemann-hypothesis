module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
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
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SobGL

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Idx (n : ℕ) := Bool × Fin n × Fin n

def cm {n : ℕ} (t : Idx n → ℝ) : Mat n := ∑ p, t p • bs p

def pd {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List ι → ((ι → ℝ) → V) → ((ι → ℝ) → V) :=
  fun L F => L.foldr (fun i H t => fderiv ℝ H t (Pi.single i 1)) F

def Dw {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (Idx n) → (Mat n → V) → (Mat n → V) :=
  fun L f => L.foldr (fun p H y => fderiv ℝ H y (bs p)) f

theorem pd_nil {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : (ι → ℝ) → V) : pd [] F = F := rfl

theorem pd_cons {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : ι) (L : List ι) (F : (ι → ℝ) → V) :
    pd (i :: L) F = fun t => fderiv ℝ (pd L F) t (Pi.single i 1) := rfl

theorem Dw_nil {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Mat n → V) :
    Dw [] f = f := rfl

theorem Dw_cons {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (p : Idx n)
    (L : List (Idx n)) (f : Mat n → V) :
    Dw (p :: L) f = fun y => fderiv ℝ (Dw L f) y (bs p) := rfl

end GlobalTheory.CompanionTheory.SobGL
