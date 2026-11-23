module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem arcF_values_add_ker_onto : BrGtSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (A : ArcF D R F) (n : ℕ), 0 < n → (∀ a b, A.N.QEq (A.q n a * A.q n b) (A.q n (a + b))) ∧ (∀ a b, A.N.QEq (A.q n a) (A.q n b) ↔ ∃ e, a = b + n • e) ∧ ∀ p, ∃ a, A.N.QEq (A.q n a) p := by
  intro hG E _ _ _ H D R _ _ F _ _ _ A n hn
  obtain ⟨-, -, hadd, -, hQ⟩ := hG R A.D₀ A.even A.bimult F A.N A.ν
  refine ⟨fun a b => ?_, fun a b => ?_, fun q => ?_⟩
  · obtain ⟨p, h₁, h₂, h₃⟩ := A.I.add n hn a b
    obtain ⟨q, hq⟩ := ((hQ n).1 p).exists
    have e : q = A.q n a * A.q n b := by
      refine Subtype.ext (Prod.ext ?_ ((hadd _ _ _ _ _ _ (A.hq n a).2 (A.hq n b).2 hq.2).1 h₂))
      apply Multiplicative.toAdd.injective
      apply A.ν.eX.injective
      rw [hq.1, h₁, ← (A.hq n a).1, ← (A.hq n b).1, ← map_add (f := _)]
      rfl
    rw [← e]
    exact ((hQ n).2.2 _ _ _ _ hq (A.hq n _)).1 h₃
  · rw [← (hQ n).2.2 _ _ _ _ (A.hq n a) (A.hq n b)]
    exact A.I.ker n hn a b
  · obtain ⟨p₀, hp₀⟩ := (hQ n).2.1 q
    obtain ⟨a, ha⟩ := A.I.onto n hn p₀
    exact ⟨a, ((hQ n).2.2 _ _ _ _ (A.hq n a) hp₀).1 ha⟩

end GlobalTheory.Ex
