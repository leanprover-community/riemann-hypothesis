module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Data.Fintype.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfSumMem
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory

theorem eigen_components_mod_stable {k : Type} [Field k] {H : Type 1} [AddCommGroup H] [Module k H]
    {O : Type} [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H)
    (hF : ∀ c, ∀ x ∈ F, ρ c x ∈ F) {a : ℕ} (χ : Fin a → O → k)
    (hχ : ∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) (S : Finset (Fin a)) :
    ∀ u : Fin a → H, (∀ i ∈ S, ∀ c, ρ c (u i) - χ i c • u i ∈ F) →
      ∑ i ∈ S, u i ∈ F → ∀ i ∈ S, u i ∈ F := by
  first
  | exact @_root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem
  | exact _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem
  | (apply _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem ..)

theorem eigen_mod_stable : ∀ (k : Type) [Field k] (H : Type 1) [AddCommGroup H] [Module k H] (O : Type) [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H), (∀ c, ∀ x ∈ F, ρ c x ∈ F) → ∀ (a : ℕ) (χ : Fin a → O → k), (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → ∀ u : Fin a → H, (∀ i c, ρ c (u i) - χ i c • u i ∈ F) → ∑ i, u i ∈ F → ∀ i, u i ∈ F := by
  intro k _ H _ _ O _ ρ F hF a χ hχ u hu hs i
  exact eigen_components_mod_stable ρ F hF χ hχ Finset.univ u (fun i _ c => hu i c) hs i (Finset.mem_univ i)

end GlobalTheory
