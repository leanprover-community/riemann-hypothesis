module

public import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ZarPrincipal

theorem form_mul_comm {A : Type} [CommRing A] (I : Ideal A) (f : Module.Dual A ↥I)
    (y x : ↥I) : f y * (x : A) = f x * (y : A) := by
  have h : (x : A) • y = (y : A) • x := by
    ext; simp [mul_comm]
  have := congrArg f h
  simp only [map_smul, smul_eq_mul] at this
  rw [mul_comm, this, mul_comm]

theorem one_mem_span_values {A : Type} [CommRing A] (I : Ideal A) [Module.Invertible A ↥I] :
    (1 : A) ∈ Ideal.span {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} := by
  obtain ⟨t, ht⟩ := (Module.Invertible.bijective (R := A) (M := ↥I)).2 1
  rw [← ht]
  clear ht
  induction t with
  | tmul f y => exact Ideal.subset_span ⟨f, y, by simp [contractLeft_apply]⟩
  | add a b ha hb => rw [map_add (f := _)]; exact Ideal.add_mem _ ha hb

end GlobalTheory.BSP.ZarPrincipal


open GlobalTheory.BSP.ZarPrincipal in
theorem GlobalTheory.BSP.invertible_ideal_principal_on_cover :
    ∀ (A : Type) [CommRing A] (I : Ideal A), Module.Invertible A ↥I → ∃ (n : ℕ) (s t : Fin n → A),
      Ideal.span (Set.range s) = ⊤ ∧ ∀ i, t i ∈ I ∧ ∀ x ∈ I, ∃ c, s i * x = c * t i := by
  intro A _ I hI
  set S : Set A := {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} with hS
  have h1 : (1 : A) ∈ Ideal.span S := one_mem_span_values I
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hmem : ∀ a : T, ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = (a : A) := fun a => hTS a.2
  choose f y hfy using hmem
  let e := T.equivFin
  refine ⟨T.card, fun i => ((e.symm i : T) : A), fun i => (y (e.symm i) : A), ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    refine Submodule.span_mono ?_ hT
    intro a ha
    exact ⟨e ⟨a, ha⟩, by simp⟩
  · intro i
    refine ⟨(y (e.symm i)).2, fun x hx => ⟨f (e.symm i) ⟨x, hx⟩, ?_⟩⟩
    show ((e.symm i : T) : A) * x = _ * (y (e.symm i) : A)
    rw [← hfy (e.symm i)]
    exact form_mul_comm I (f (e.symm i)) (y (e.symm i)) ⟨x, hx⟩
