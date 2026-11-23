module

public import Mathlib.AlgebraicGeometry.FunctionField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSectionOfPow
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : ℕ) [Fact p.Prime] [CharP Z.functionField p], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Type) (U : J → Z.Opens) (n : ∀ a b, Γ(Z, U a ⊓ U b)) (h : ∀ a, Γ(Z, U a)) (a₀ : J) [Nonempty (U a₀)], (∀ a b, n a b ^ p = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (h a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (h b)) → (∃ r : Z.functionField, r ^ p = (Z.germToFunctionField (U a₀)).hom (h a₀)) → ∃ s : ∀ a, Γ(Z, U a), ∀ a b, n a b = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (s a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (s b) := by
  intro Z _ p _ _ hN J U n h a₀ _ hn ⟨r, hr⟩
  have hg : genericPoint Z ∈ U a₀ := ((genericPoint_spec Z).mem_open_set_iff (U a₀).isOpen).mpr (by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty (U a₀)›
    exact ⟨z, trivial, hz⟩)
  haveI : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  have hp : (p : Γ(Z, ⊤)) = 0 := by
    apply Z.germToFunctionField_injective ⊤
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero _ p
  obtain ⟨s, hs⟩ := GlobalTheory.CechRoot.exists_root Z (fun b => (hN b).2) p hp J U h n
    (fun a b => (hn a b).symm) a₀ (genericPoint Z) hg (algebraMap Z.functionField _ r)
    (by rw [← map_pow, hr])
  exact ⟨s, fun a b => (hs a b).symm⟩
