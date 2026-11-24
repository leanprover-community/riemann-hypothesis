module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftConstantTermCompatibleWeilStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompatibleOfSameSplittingCharacterStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerConstTermObj

theorem towerConstTerm : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D := by

  intro D V V' W r C B hsplit ψ χS χT χT' ω ω' hω hω'
  have hcomp : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.Compatible ψ V V' W C B ω ω' :=
    GlobalTheory.T.weilCompatible_of_sameSplittingCharacter D V V' W r C B hsplit ψ χS χT χT' ω ω' hω hω'
  exact GlobalTheory.T.thetaLift_constantTerm_compatibleWeil D V V' W r C B hsplit ψ χS χT χS χT' ω ω' hω hω' hcomp

end GlobalTheory.TowerConstTermObj
