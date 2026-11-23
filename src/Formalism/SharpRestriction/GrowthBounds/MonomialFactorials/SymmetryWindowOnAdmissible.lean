module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SymmetryWindowLevelDimOnAdmissible
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LvlDimCondition
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

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def SymmetryWindowConditions (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestSymm C0 CE1 CE2 X ∧ RestWin C0 CE1 CE2 X CM

def SymmetryWindowOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → SymmetryWindowConditions C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem windows_of_symmetric_dims (D : Formalism.BasicNotions.D7) (h : SymmetryWindowOnAdmissible D) : SymmetryWindowLevelDimOnAdmissible D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, b, (lvlDimCondition (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X))⟩) h

theorem closed_of_symmetric_dims (D : Formalism.BasicNotions.D7) (hF : RestFunY) (hO : OrthLat) (h : SymmetryWindowOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_symmetric_windows D hF hO (windows_of_symmetric_dims D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
