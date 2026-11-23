module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Reduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.HenselQuad

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

def SplitPair (D : Car) : Prop :=
  ∀ (N' : ℕ) (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N' → SD D L' → SD D L'' →
    ∀ n : 𝓞 D.host.E, n ≠ 0 → ∃ e : Matrix (Fin N') (Fin N') D.host.E,
      (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') ∧
      ∀ M ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
          (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)),
        ∀ y, (y ∈ L' ∨ y ∈ L'') → ∃ m, m ∈ L' ∧ m ∈ L'' ∧ M *ᵥ y = (n : D.host.E) • m

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
