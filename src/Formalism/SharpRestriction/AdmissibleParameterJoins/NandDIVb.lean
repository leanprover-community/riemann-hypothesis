module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVa
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem theta_injective_of_scalars (D : D7) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D) (hI : Rows.IsotInternal D.what₂)
    (i : D.nd.Loc) (hj : D.nd.j i ∈ SizeData₂.lifts D) :
    Function.Injective (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
  have hj' := Finset.mem_Icc.mp hj
  exact injective_of_scalars (D.what₂.isot (D.nd.j i)) (hI _ hj'.1 hj'.2) _ (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))
    (fun σ hσ => let ⟨lam, h0, hl⟩ := (h42 i σ hσ).1.1; ⟨(lam : ℂ), by exact_mod_cast h0.ne', hl⟩)

end Formalism.MainNotions.J

end
