module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermRegularConnected
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalParametrisation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParametrisationSheetsConnected
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
import Mathlib.Order.CompletePartialOrder
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem IrreducibleGermRegularConnected.proof (hpar : LocalParametrisation.Statement)
    (hsheets : ParametrisationSheetsConnected.Statement) :
    IrreducibleGermRegularConnected.Statement := by
  intro σ _ X w hX hirr U hU
  obtain ⟨d, A, B, D, δ, N, hBU, hP⟩ := hpar σ X w hX hirr U hU
  have hS := hsheets σ X w B d A D δ N hP hirr
  obtain ⟨hBo, hwXB, -, -, -, -, -, -, -, -, hchart, hdense⟩ := hP

  have hSreg : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ regLocus (X ∩ B) := by
    rintro x ⟨hxXB, hx⟩
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hchart x hxXB hx
    exact ⟨hxXB, d, A, O, V, g, hO, hV, hxV, hg, hAg, hXV⟩
  exact ⟨B, hBo, hwXB.2, hBU, hS.subset_closure hSreg ((regLocus_subset _).trans hdense)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
