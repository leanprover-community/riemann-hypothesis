module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrGraphQ_of :
    TrIdQ → WtLin → CorrGraphQ := by
  intro hT hW S Y f d
  refine ⟨⟨S, 𝟙 S, f, Wt.const S d, inferInstance, hW.2.2 (𝟙 S) d⟩, ?_, ?_, ?_⟩
  · intro B bY
    simp
  · intro Ω _ _ x y
    constructor
    · intro h
      have hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = {x} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
        constructor
        · exact fun hz => hz.1
        · rintro rfl
          exact ⟨rfl, h⟩
      change ∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = d
      rw [hs, finsum_mem_singleton]
      rfl
    · intro h
      have hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
        rintro ⟨rfl, h'⟩
        exact h h'
      change ∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = 0
      rw [hs, finsum_mem_empty]
  · intro l _ n i hl
    change (trHQ l (𝟙 S) (Wt.const S d) n i).comp (pullHQ l (sch.map f) n i) = _
    rw [hT l n i S d hl, LinearMap.smul_comp, LinearMap.id_comp]
