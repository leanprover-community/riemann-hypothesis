module

public import Formalism.LocalToGlobal.Divisibility.JetBounds.IsExpansion
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Formalism.LocalToGlobal.Divisibility.ClassSum
public import Formalism.LocalToGlobal.ExponentGrids.IntegerShiftClosedExponent

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.AlgTh

open Formalism.DivisionValues (vw PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols)
open Formalism.L2.DIV (PathData EmbAt IsExpansion ColsInt RowsInt LastInt UnitsInt StabDvd)
open Formalism.AtG (PerBd colRhs)

def GAt {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem)
    (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (w : HeightOneSpectrum (𝓞 K)) (g : ℕ) [Fact g.Prime] (pb : K)
    (Dg : Bs.J → ℕ) (Rg : Bs.J → ℝ) : Prop :=
  ∃ (ι : K →+* ℂ_[g]) (X : PathData K g Bs.J (Fin (Dc.a u) → K) (Fin (Df.nV t) → K)) (D : ℕ) (j1 : Bs.J),
    EmbAt w g ι ∧ IsExpansion X ι (Dc.Pt u t) (Nu : Set (Fin (Dc.a u) → K)) (Df.Mt t : Set (Fin (Df.nV t) → K)) ∧
    ColsInt X w (Nu : Set (Fin (Dc.a u) → K)) ∧ RowsInt X w (Df.Mt t : Set (Fin (Df.nV t) → K)) ∧
    LastInt X ∧ UnitsInt X ∧ StabDvd X D j1 ∧ ¬ g ∣ D ∧
    ∀ π j, ‖X.e π j‖ * ‖ι pb‖ ^ (Dg j) * ‖(g : ℂ_[g])‖ ^ (Rg j) ≤ 1

end Formalism.L2.AlgTh
