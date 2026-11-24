module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Inj

theorem filR_anti {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) :
    Antitone (FilR p n) :=
  fun _ _ h => GlobalTheory.LogCris.fil_anti _ n h

theorem filR_zero {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) :
    FilR p n 0 = Set.univ :=
  GlobalTheory.LogCris.fil_zero _ n

theorem filR_pull {K : Type} [CommRing K] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of K)}
    {q : Y ⟶ Spec (CommRingCat.of K)} (u : X ⟶ Y) (hu : u ≫ q = p) (n r : ℕ) :
    ∀ x ∈ FilR q n r, pullR n u hu x ∈ FilR p n r := by
  rintro x ⟨z, rfl, hz⟩
  exact ⟨_, rfl, fun s => hz (s ⋙ (smMor u hu).functor)⟩

end CrystallineSemistableComparison.Inj
