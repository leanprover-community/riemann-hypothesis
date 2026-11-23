module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyExistsIsUnitOfSpanRangeEqTop
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisStackProductOfInjectiveOfLocallyCov
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem isUnit_last_join {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A) (h : IsUnit (x.2.1 1)) :
    IsUnit ((Um.join x).1 (Fin.last N)) := by
  simpa [Um.join] using h

private theorem closedSubgroup_cutoff_exists {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A) (h : IsUnit (x.2.1 0)) :
    Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) = ⊤ := by
  obtain ⟨u, hu⟩ := h
  have e : (Um.join x).1 '' Set.range Fin.castSucc = (fun i => (u : A) * x.1.1 i) '' Set.univ := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, trivial, by simp [Um.join, hu]⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, by simp [Um.join, hu]⟩
  rw [e, span_scale, Set.image_univ]
  exact x.1.2

theorem UpperTheory.two_open_cover_of_map_incl_comap :
    ∀ (R : Type) [CommRing R] (N : ℕ) (E : Spc),
        Cover2 R (Sp.map E (incl ((Q1 N).comap (βC N)))) (Sp.map E (incl ((Q2 N).comap (βC N)))) := by
  intro R _ N E
  refine UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E _ _ (fun A => Subtype.val_injective) (fun A => Subtype.val_injective)
    (fun A => Function.bijective_id) (fun A => Function.bijective_id) ?_
  intro T x
  obtain ⟨S, hS, hP⟩ := UpperTheory.locally_exists_isUnit_of_span_range_eq_top T (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.1
    (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.2
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨i, hi⟩ := hP V g hg
  have hx : (show Um N Γ(V, ⊤) × Um 2 Γ(V, ⊤) from (BC N).D.map g.appTop x).2.1 i =
      g.appTop.hom ((show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.1 i) := rfl
  rw [← hx] at hi
  fin_cases i
  · exact Or.inr ⟨⟨_, closedSubgroup_cutoff_exists _ hi⟩, rfl⟩
  · exact Or.inl ⟨⟨_, isUnit_last_join _ hi⟩, rfl⟩
