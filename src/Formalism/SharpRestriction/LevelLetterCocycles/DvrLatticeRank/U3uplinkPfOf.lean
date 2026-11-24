module

public import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GamPiPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3upPfFilCAnti
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

namespace Formalism.MainNotions.N.Ln34

theorem u3uplink_pf_of (hW : WStep) : UpSlotOfModels := by
  intro D HW F Cm CA CB CK hA hMF
  exact u3upPf_ofR D HW hMF (hW D HW F Cm CA CB CK hA) (ninlam_pf D HW F Cm CA CB CK hA)
    (gamPiCondition D HW F Cm CA CB CK hA)

end Formalism.MainNotions.N.Ln34

end
