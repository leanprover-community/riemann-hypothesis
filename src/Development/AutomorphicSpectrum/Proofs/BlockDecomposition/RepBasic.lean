module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtEdge

theorem repBasic : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepBasic := by
  intro hExt hNat hIn
  unfold CrystallineSemistableComparison.E.InSch at hIn
  unfold CrystallineSemistableComparison.E.RepBasic
  intro R _ I X n
  unfold CrystallineSemistableComparison.E.Rep
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    exact ⟨_, α, rfl, rfl⟩
  · rintro x a ⟨α, -, rfl⟩ m
    by_cases hm : n + 1 = m
    · exact ((hIn R X I (n - 1) n m (by omega) hm).2 α).1
    · rw [HomologicalComplex.shape I n m (by simpa using hm)]
      simp [GlobalTheory.EtC.Sec.map]
  · rintro x y a b ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    have hs := (hExt R (sch.obj X) I n α β).2 0 n (by simp) X (𝟙 X : X ⟶ X)
    exact ⟨⟨α + β, rfl, hs.1⟩, ⟨α - β, rfl, hs.2.1⟩⟩
  · rintro a ⟨α, h0, rfl⟩ k hk
    exact ((hIn R X I k n (n + 1) hk rfl).2 α).2.1 h0
  · rintro Y f x a ⟨α, rfl, rfl⟩
    refine ⟨GlobalTheory.EtC.zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_⟩
    have h2 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) Y).2 (sch.obj Y) (sch.map f)
      (𝟙 Y : Y ⟶ Y)
    have h1 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) X).1 Y f (𝟙 X : X ⟶ X)
    have e : (Sx.map (sch.map f) (𝟙 Y : Y ⟶ Y) : Sx (sch.obj X) 0 Y) = Sx.res f (𝟙 X : X ⟶ X) := by
      show 𝟙 Y ≫ f = f ≫ 𝟙 X
      simp
    refine h2.trans ?_
    rw [e]
    exact h1

end GlobalTheory.CompanionTheory.EtEdge
