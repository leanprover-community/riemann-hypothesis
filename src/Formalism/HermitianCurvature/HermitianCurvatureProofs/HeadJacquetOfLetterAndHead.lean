module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActOneVariableSmul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZOnly
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WordInd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem head_jacquet_of_letter_and_head (hHL : LevelPointCoordinates.HeadLetter) (hB : LevelPointCoordinates.HeadBridge) : LevelPointCoordinates.HeadJ :=
  LevelPointCoordinates.headJ_of (word_induction_of_parts hHL z_only rules_closed) hB

theorem radial_head_of_letter_and_head (hHL : LevelPointCoordinates.HeadLetter) (hB : LevelPointCoordinates.HeadBridge) : KB.RadHead :=
  pb_radHead_of_headJ (head_jacquet_of_letter_and_head hHL hB)

end Formalism.FourierDecayAlt.P
