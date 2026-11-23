module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Formalism.RealPlaceAnalysis.StatementE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem eword_adjoint {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (w : List (Fin n × Fin n)) (x y : M) :
    inner ℂ ((w.map fun p => E p.1 p.2).prod x) y =
      (w.map fun p => adjSign ε p.1 p.2).prod *
        inner ℂ x (((w.reverse.map Prod.swap).map fun p => E p.1 p.2).prod y) := by
  induction w generalizing y with
  | nil => simp
  | cons p w ih =>
    simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append, List.prod_append,
      Module.End.mul_apply]
    rw [hU p.1 p.2, ih]
    simp only [List.map_nil, List.prod_nil, Prod.fst_swap, Prod.snd_swap, Module.End.one_apply]
    ring

def anyAdjWSum {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (l : List (ℂ × List (Fin n × Fin n))) : Module.End ℂ M :=
  (l.map fun c => c.1 • (c.2.map fun p => E p.1 p.2).prod).sum

theorem anyAdjWSum_append {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (l₁ l₂ : List (ℂ × List (Fin n × Fin n))) :
    anyAdjWSum E (l₁ ++ l₂) = anyAdjWSum E l₁ + anyAdjWSum E l₂ := by
  unfold anyAdjWSum
  rw [List.map_append, List.sum_append]

theorem anyAdjWSum_mul {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (l₁ l₂ : List (ℂ × List (Fin n × Fin n))) :
    anyAdjWSum E l₁ * anyAdjWSum E l₂ =
      anyAdjWSum E (l₁.flatMap fun c => l₂.map fun d => (c.1 * d.1, c.2 ++ d.2)) := by
  unfold anyAdjWSum
  induction l₁ with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.sum_cons, add_mul, ih, List.flatMap_cons, List.map_append, List.sum_append]
    congr 1
    rw [← List.sum_map_mul_left, List.map_map]
    congr 1
    refine List.map_congr_left fun d _ => ?_
    simp only [Function.comp_apply, List.map_append, List.prod_append, smul_mul_smul_comm]

def anyAdjWordAlg {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    Subalgebra ℂ (Module.End ℂ M) where
  carrier := {A | ∃ l, A = anyAdjWSum E l}
  mul_mem' := by
    rintro _ _ ⟨l₁, rfl⟩ ⟨l₂, rfl⟩
    exact ⟨_, anyAdjWSum_mul E l₁ l₂⟩
  add_mem' := by
    rintro _ _ ⟨l₁, rfl⟩ ⟨l₂, rfl⟩
    exact ⟨l₁ ++ l₂, (anyAdjWSum_append E l₁ l₂).symm⟩
  algebraMap_mem' r := ⟨[(r, [])], by simp [anyAdjWSum, Algebra.algebraMap_eq_smul_one]⟩

theorem qdet_eq_sum_words {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (u : ℂ) : ∃ l : List (ℂ × List (Fin n × Fin n)),
      Formalism.REAL.qdet E u = (l.map fun c => c.1 • (c.2.map fun p => E p.1 p.2).prod).sum := by
  have hE : ∀ a b : Fin n, E a b ∈ anyAdjWordAlg E := fun a b => ⟨[(1, [(a, b)])], by simp [anyAdjWSum]⟩
  have h : Formalism.REAL.qdet E u ∈ anyAdjWordAlg E := by
    unfold Formalism.REAL.qdet Formalism.REAL.qminor
    refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (intCast_mem _ _) ?_
    refine list_prod_mem fun x hx => ?_
    rw [List.mem_ofFn] at hx
    obtain ⟨k, rfl⟩ := hx
    unfold Formalism.REAL.Tm
    refine Subalgebra.add_mem _ ?_ (hE _ _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _
  obtain ⟨l, hl⟩ := h
  exact ⟨l, hl⟩

end ReciprocityTheory.ChartRestriction.DS
