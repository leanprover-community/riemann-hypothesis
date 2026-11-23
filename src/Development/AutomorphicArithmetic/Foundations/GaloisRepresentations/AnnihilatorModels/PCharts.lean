module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.charts_of :
    ChartsExist := by
  intro l Y hY J _ T y
  haveI : ∀ j, IsFinite (T j).p := fun j => (T j).fin
  let S : Set Y := {y} ∪ ⋃ j, (T j).r '' ((T j).p ⁻¹' {y})
  have hS : S.Finite := (Set.finite_singleton y).union
    (Set.finite_iUnion fun j => ((T j).p.finite_preimage_singleton y).image _)
  obtain ⟨V, hV, hSV⟩ := hY hS.toFinset
  have hSV' : ∀ x ∈ S, x ∈ V := fun x hx => hSV x (hS.mem_toFinset.mpr hx)
  have hclosed : IsClosed (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ) :=
    isClosed_iUnion_of_finite fun j => (T j).p.isClosedMap _ ((T j).r ⁻¹ᵁ V).isOpen.isClosed_compl
  let O : Y.Opens := ⟨(⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hyO : y ∈ O := by
    show y ∈ (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ
    rintro hy
    obtain ⟨j, z, hz, hzy⟩ := Set.mem_iUnion.mp hy
    apply hz
    show (T j).r z ∈ V
    exact hSV' _ (Or.inr (Set.mem_iUnion.mpr ⟨j, z, hzy, rfl⟩))
  obtain ⟨U, hU, hyU, hUO⟩ := exists_isAffineOpen_mem_and_subset hyO
  refine ⟨U, V, hU, hV, hyU, fun j z hz => ?_⟩
  by_contra h
  have hz' : (T j).p z ∈ (O : Set Y) := hUO hz
  exact hz' (Set.mem_iUnion.mpr ⟨j, z, h, rfl⟩)
