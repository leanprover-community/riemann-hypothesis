module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

theorem depthZeroJacquetInjective_of_admissible :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.MoyPrasadJacquetIso →
      GlobalTheory.Published.DepthZeroJacquetInjective := by
  intro hBZ hMP k _ _ _ _ n s d e π v hv h0
  have hadm := (hBZ k).1 (Fin n) π.V π.π π.smooth π.irr
  have hb := hMP k n s d e π.V π.π hadm
  have h00 : (0 : π.V) ∈ fixed π.π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    first
      | exact Submodule.zero_mem _
      | exact fun _ => map_zero _
      | simp [fixed]
  exact hb.injOn hv h00 (by simpa using h0)

end GlobalTheory
