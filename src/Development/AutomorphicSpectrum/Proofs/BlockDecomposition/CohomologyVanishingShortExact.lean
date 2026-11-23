module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Mathlib.Algebra.Exact.Basic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cohomology

theorem subsingleton_H_of_ses {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
    {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃)
    (hi : ∀ T, Function.Injective (α.app T).hom)
    (he : ∀ T, Function.Exact (α.app T).hom (β.app T).hom)
    (hs : ∀ T, Function.Surjective (β.app T).hom)
    (h₂ : ∀ n, Subsingleton (CH.H F₂ n)) (h₃ : ∀ n, Subsingleton (CH.H F₃ n)) :
    ∀ n, Subsingleton (CH.H F₁ n) := by
  obtain ⟨c₁, c₂, c₃⟩ := CrystallineSemistableComparison.P.ses_cochains α β hi he hs
  obtain ⟨δ, -, hinj, -, -, hex⟩ :=
    CrystallineSemistableComparison.P.les (CH.Mor.ofNatTrans α).hom (CH.Mor.ofNatTrans β).hom c₁ c₂ c₃
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton ((CH.cx F₂).H 0) := h₂ 0
    exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
  | succ n =>
    haveI : Subsingleton ((CH.cx F₂).H (n + 1)) := h₂ (n + 1)
    haveI : Subsingleton ((CH.cx F₃).H n) := h₃ n
    have key : ∀ x : (CH.cx F₁).H (n + 1), x = 0 := fun x => by
      obtain ⟨y, rfl⟩ := (hex n x).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim y 0, map_zero]
    exact ⟨fun x y => (key x).trans (key y).symm⟩

end GlobalTheory.CompanionTheory.Cohomology
