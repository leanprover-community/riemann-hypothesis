module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RInv2
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

noncomputable section

namespace UpperTheory.Gal.TP.Loc

theorem satInvT : SatInvT := by
  intro K _ _ w n V _ _ ρ B h
  refine UpperTheory.V.InvT.hasSatGL_invT (ρ := ρ) (LinearEquiv.refl ℂ V) (fun g x => ?_) h
  have hg : GlobalTheory.SplitFlip.invT g = GlobalTheory.CuspRep.invT n _ g := Units.ext rfl
  change ρ (GlobalTheory.SplitFlip.invT g) x = ρ (GlobalTheory.CuspRep.invT n _ g) x
  rw [hg]

end UpperTheory.Gal.TP.Loc

end
