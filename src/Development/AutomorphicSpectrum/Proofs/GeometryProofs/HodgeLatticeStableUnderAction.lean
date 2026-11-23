module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem hodgeAt_stable : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (R : Subring Ω) (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HL : Submodule R (Vs × Module.Dual Ω Vs)),
    (∀ a y, (ρH a y).1 = ρ a y.1) → HodgeAt ρH HL ℓ t →
    (∀ i, t i ∈ HL) ∧ (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) ∧ ∀ a i, ρ a (ℓ i) ∈ Submodule.span R (Set.range ℓ) := by
  intro E _ _ Ω Vs _ _ _ ρ ρH R g N ℓ t HL h1 h
  obtain ⟨⟨-, -, hX⟩, hmap, -⟩ := h
  have key : ∀ (c : 𝓞 E) (i : Fin N), ρH c (t i) ∈ HL := by
    intro c i

    rw [hX, ← (RingOfIntegers.basis E).sum_repr c, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _
  have stable : ∀ a, ∀ y ∈ HL, ρH a y ∈ HL := by
    intro a y hy
    rw [hX] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      rw [← Module.End.mul_apply, ← map_mul]
      exact key _ _
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul r x _ hx =>
      have e : ρH a (r • x) = r • ρH a x := map_smul (ρH a) (r : Ω) x
      rw [e]
      exact HL.smul_mem r hx
  refine ⟨fun i => ?_, stable, fun a i => ?_⟩
  · simpa using key 1 i
  · have hi : ℓ i ∈ HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) :=
      hmap ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy, e⟩ := hi
    rw [← hmap]
    refine ⟨ρH a y, stable a y hy, ?_⟩
    have e' : y.1 = ℓ i := e
    change (ρH a y).1 = _
    rw [h1, e']

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
