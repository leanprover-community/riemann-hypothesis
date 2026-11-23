module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Mathlib.Data.Matrix.ColumnRowPartitioned
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

def StdSupp (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : Prop :=
  (∀ i j, x.toRows₁ i j ∈ 𝒪[k]) ∧ valuation k x.toRows₁.det = 1 ∧ ∀ i j, x.toRows₂ i j ∈ cball (ϖ ^ c)

theorem StdSupp.det_ne {ϖ : kˣ} {c : ℕ} {x : Matrix (Fin n ⊕ Fin n') (Fin n) k} (h : StdSupp ϖ c x) :
    x.toRows₁.det ≠ 0 := fun h0 => by
  have := h.2.1
  rw [h0, map_zero] at this
  exact zero_ne_one this


open Classical in
def stdDatum (μ : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : ℂ :=
  if h : StdSupp ϖ c x then (((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ) else 0

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta
