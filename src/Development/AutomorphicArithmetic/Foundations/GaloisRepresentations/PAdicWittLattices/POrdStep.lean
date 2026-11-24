module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem mem_range_diagonal_iff {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsOpenImmersion (pullback.diagonal s)]
    (Ω : Type) [Field Ω] (y : UpperTheory.Gal.G3.sp Ω ⟶ pullback s s) :
    y (IsLocalRing.closedPoint Ω) ∈ Set.range (pullback.diagonal s) ↔
      y ≫ pullback.fst s s = y ≫ pullback.snd s s := by
  constructor
  · rintro ⟨z, hz⟩
    have hsub : Set.range y ⊆ Set.range (pullback.diagonal s) := by
      rintro _ ⟨q, rfl⟩
      have hq : q = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
      rw [hq]
      exact ⟨z, hz⟩
    have hfac := IsOpenImmersion.lift_fac (pullback.diagonal s) y hsub
    rw [← hfac, Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
  · intro h
    refine ⟨(y ≫ pullback.fst s s) (IsLocalRing.closedPoint Ω), ?_⟩
    have hy : (y ≫ pullback.fst s s) ≫ pullback.diagonal s = y := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
    conv_rhs => rw [← hy]
    rfl

theorem UpperTheory.Gal.G3.pOrdStep :
    OrdStep := by
  intro Z Y W s _ _ c d σ hσ
  have hc : ∀ j, pullback.fst s c ≫ s = (pullback.snd s c ≫ σ j) ≫ s := fun j => by
    rw [Category.assoc, hσ j, pullback.condition]
  let φ : Fin d → (pullback s c ⟶ pullback s s) := fun j =>
    pullback.lift (pullback.fst s c) (pullback.snd s c ≫ σ j) (hc j)
  have hopen : ∀ j, IsOpen ((φ j) ⁻¹' Set.range (pullback.diagonal s)) := fun j =>
    (pullback.diagonal s).isOpenEmbedding.isOpen_range.preimage (φ j).continuous
  have hclosed : ∀ j, IsClosed ((φ j) ⁻¹' Set.range (pullback.diagonal s)) := fun j =>
    (pullback.diagonal s).isClosedEmbedding.isClosed_range.preimage (φ j).continuous
  refine ⟨⟨(⋃ j, (φ j) ⁻¹' Set.range (pullback.diagonal s))ᶜ,
    (isClosed_iUnion_of_finite hclosed).isOpen_compl⟩, (isOpen_iUnion hopen).isClosed_compl, ?_⟩
  intro Ω _ x
  have key : ∀ j, (x ≫ φ j) (IsLocalRing.closedPoint Ω) ∈ Set.range (pullback.diagonal s) ↔
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j := by
    intro j
    rw [mem_range_diagonal_iff s Ω (x ≫ φ j)]
    simp only [Category.assoc, φ, pullback.lift_fst, pullback.lift_snd]
  show x (IsLocalRing.closedPoint Ω) ∈ (⋃ j, (φ j) ⁻¹' Set.range (pullback.diagonal s))ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, not_exists]
  refine forall_congr' (fun j => ?_)
  exact (not_congr (key j)).trans ⟨fun h e => h e.symm, fun h e => h e.symm⟩
