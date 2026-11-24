module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.TruncationHomExt
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FramedSite

theorem cohomology_subsingleton_of_frame_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}
    (E : Frame Φ 0) (F : C ⥤ ModuleCat.{0} R) (hD : Subsingleton (F.obj E.D)) (n : ℕ) :
    Subsingleton (CH.H F n) := by
  obtain ⟨-, -, hex0, hex⟩ := CrystallineSemistableComparison.P.initial F E.D (Frame.initial E)
  have key : ∀ x : CH.H F n, x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).2.1 a ha).2 ?_
    cases n with
    | zero =>
      obtain ⟨m, hm⟩ := hex0 a ha
      rw [one_smul] at hm
      have hm0 : m = 0 := Subsingleton.elim _ _
      rw [hm0, map_zero] at hm
      exact hm.symm
    | succ n =>
      obtain ⟨y, hy⟩ := hex n a ha
      rw [one_smul] at hy
      exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end GlobalTheory.CompanionTheory.FramedSite
