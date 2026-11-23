module

public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.WachRestrictionOfLiftingPackage
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

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem archimedean_signature_matching_of_liftingTheory (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA : ℝ) (CB : ℝ) (CK : ℝ) (C : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching D HW F CA CB CK := by
  unfold Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching
  exact lift_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_five_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm5 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm5
  exact wach_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_six_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm6 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm6
  exact lifting_local_of_package D HW F C CA CB CK h54

end Formalism.MainNotions.N
