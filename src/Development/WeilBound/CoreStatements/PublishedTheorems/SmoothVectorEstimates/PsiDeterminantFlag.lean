module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatakeStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
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

open GlobalTheory.CuspRep

namespace PositivityTheory.jumpWindows

theorem mean_convergence_of : Smo → GlobalTheory.Published.CuspidalMultiplicityOne := by
  intro h E _ _ _ a π π' e
  refine congrArg CuspSub.V (h E a π π' ?_)
  filter_upwards [GlobalTheory.T.cuspidal_GL_local_components_eventually_satake CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π] with w hw
  obtain ⟨B, hB⟩ := hw
  exact ⟨B, hB, e ▸ (show (CG.mk π).HasSat w B from hB)⟩

end PositivityTheory.jumpWindows
