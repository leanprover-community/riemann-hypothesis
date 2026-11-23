module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Mon
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitLocus

theorem isUnit_of_basicOpen_eq_top' {Y : Scheme.{0}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) : IsUnit s :=
  Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Y.mem_basicOpen _ x hx).1 (h.ge hx)

theorem natCast_unit_locus (S' : Scheme.{0}) (d : ℕ) : ∃ U : S'.Opens,
    (∀ V : S'.Opens, V ≤ U → IsUnit ((d : ℕ) : Γ(V.toScheme, ⊤))) ∧
    ∀ (T : Scheme.{0}) (g : T ⟶ S'), IsUnit ((d : ℕ) : Γ(T, ⊤)) → Set.range g.base ⊆ (U : Set S') := by
  refine ⟨S'.basicOpen ((d : ℕ) : Γ(S', ⊤)), ?_, ?_⟩
  · intro V hV
    apply isUnit_of_basicOpen_eq_top'
    have e := Scheme.preimage_basicOpen_top V.ι ((d : ℕ) : Γ(S', ⊤))
    rw [map_natCast] at e
    rw [← e, eq_top_iff]
    intro x _
    show V.ι.base x ∈ S'.basicOpen _
    exact hV (show V.ι x ∈ (V : Set S') by rw [← Scheme.Opens.range_ι V]; exact ⟨x, rfl⟩)
  · intro T g hd
    rintro _ ⟨x, rfl⟩
    have e := Scheme.preimage_basicOpen_top g ((d : ℕ) : Γ(S', ⊤))
    rw [map_natCast, T.basicOpen_of_isUnit hd] at e
    have hx : x ∈ g ⁻¹ᵁ S'.basicOpen ((d : ℕ) : Γ(S', ⊤)) := by rw [e]; trivial
    exact hx

end GlobalTheory.UnitLocus
