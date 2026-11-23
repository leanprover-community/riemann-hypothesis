module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotCompactCasimirOfTypes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotOfMemAdjoinCommuting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem algMod_add {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (A B : Module.End ℂ M)
    (hAB : A * B = B * A) (hA : AlgMod S ⊥ A) (hB : AlgMod S ⊥ B) : AlgMod S ⊥ (A + B) := by
  refine UpperTheory.algMod_bot_of_mem_adjoin_commuting M S {A, B} ?_ ?_ (A + B)
    (Subalgebra.add_mem _ (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp)))
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | rfl | exact hAB | exact hAB.symm
  · intro T hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
    rcases hT with rfl | rfl <;> assumption

theorem UpperTheory.exists_basis_algMod_laplacian_of_types_centre :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Types S → Centre S → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra), AlgMod S ⊥ (uAction (laplacianU K n b)) := by
  intro K _ _ n S hT hC
  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩ := exists_archCartanData K n
  refine ⟨d, b, ?_⟩
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hΩ : casimir b ε ∈ (isExpLieAlgebra K n).centerU := casimir_mem_center hε2 horth hsymm hinv
  rw [laplacianU_eq_casimir_add b ε, map_add (f := _)]
  refine algMod_add S _ _ (Zc_comm_uAction (uAction_mem_Zc hΩ) _).eq (hC _ hΩ) ?_
  refine UpperTheory.algMod_bot_compact_casimir_of_types K n S hT (Fin d) (fun i => b i) (fun i => 1 - ε i) fun i => ?_
  rcases hε i with e | e
  · exact Or.inl (by rw [e, sub_self])
  · exact Or.inr (hK i e)
