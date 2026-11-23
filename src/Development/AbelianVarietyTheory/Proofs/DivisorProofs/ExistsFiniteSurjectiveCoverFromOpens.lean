module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinCover

theorem exists_finite_union {X : Scheme.{0}} {T : Type} (N : T → Scheme.{0}) (p : ∀ t, N t ⟶ X)
    (hp : ∀ t, IsFinite (p t)) (S : Finset T) :
    ∃ (Y : Scheme.{0}) (q : Y ⟶ X), IsFinite q ∧ (∀ t ∈ S, Set.range (p t) ⊆ Set.range q) ∧
      ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (t : T) (z : Sp K ⟶ N t), z ≫ p t = y' ≫ q := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨∅, Scheme.emptyTo X, inferInstance, by simp, fun K _ y' => ?_⟩
    exact (show PEmpty from y' (closedPoint K)).elim
  | insert a S _ ih =>
    obtain ⟨Y, q, hq, hr, hK⟩ := ih
    have := hp a
    refine ⟨N a ⨿ Y, coprod.desc (p a) q, inferInstance, fun t ht => ?_, fun K _ y' => ?_⟩
    · rintro _ ⟨x, rfl⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact ⟨(coprod.inl : N t ⟶ N t ⨿ Y) x, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
      · obtain ⟨y, hy⟩ := hr t ht ⟨x, rfl⟩
        exact ⟨(coprod.inr : Y ⟶ N a ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc, hy]⟩
    · have hsub : ∀ x : Sp K, x = closedPoint K := fun x =>
        Subsingleton.elim (α := PrimeSpectrum K) _ _
      have hc := (isCompl_range_inl_inr (N a) Y).sup_eq_top
      have hm : y' (closedPoint K) ∈ Set.range (coprod.inl : N a ⟶ N a ⨿ Y) ∪
          Set.range (coprod.inr : Y ⟶ N a ⨿ Y) := by
        have h : y' (closedPoint K) ∈ (⊤ : Set (N a ⨿ Y : Scheme.{0})) := trivial
        rw [← hc] at h
        exact h
      rcases hm with hm | hm
      · have hs : Set.range y' ⊆ Set.range (coprod.inl : N a ⟶ N a ⨿ Y) := by
          rintro _ ⟨x, rfl⟩; rw [hsub x]; exact hm
        refine ⟨a, IsOpenImmersion.lift _ y' hs, ?_⟩
        conv_rhs => rw [← IsOpenImmersion.lift_fac _ y' hs]
        rw [Category.assoc, coprod.inl_desc]
      · have hs : Set.range y' ⊆ Set.range (coprod.inr : Y ⟶ N a ⨿ Y) := by
          rintro _ ⟨x, rfl⟩; rw [hsub x]; exact hm
        obtain ⟨t, z, hz⟩ := hK K (IsOpenImmersion.lift _ y' hs)
        refine ⟨t, z, ?_⟩
        conv_rhs => rw [← IsOpenImmersion.lift_fac _ y' hs]
        rw [Category.assoc, coprod.inr_desc, hz]

theorem exists_finite_surjective_cover : ∀ (X Z : Scheme.{0}) (i : X ⟶ Z) (T : Type) [Finite T] (M : T → Scheme.{0}) (U : T → Z.Opens) (g : ∀ t, M t ⟶ (U t).toScheme), (∀ t, IsFinite (g t)) → (∀ t, Set.range i ⊆ (U t : Set Z)) → (∀ x : X, ∃ (t : T) (w : M t), (g t ≫ (U t).ι) w ⤳ i x) → ∃ (Y : Scheme.{0}) (q : Y ⟶ X), IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (t : T) (yM : Sp K ⟶ M t), yM ≫ g t ≫ (U t).ι = y' ≫ q ≫ i := by
  intro X Z i T _ M U g hg hU hx
  have hU' : ∀ t, Set.range i ⊆ Set.range (U t).ι := fun t => by
    rw [Scheme.Opens.range_ι]; exact hU t
  have := Fintype.ofFinite T
  let i' : ∀ t, X ⟶ (U t).toScheme := fun t => IsOpenImmersion.lift (U t).ι i (hU' t)
  have hi' : ∀ t, i' t ≫ (U t).ι = i := fun t => IsOpenImmersion.lift_fac _ _ _
  obtain ⟨Y, q, hq, hr, hK⟩ := exists_finite_union (fun t => pullback (g t) (i' t))
    (fun t => pullback.snd (g t) (i' t)) (fun t => by have := hg t; infer_instance) Finset.univ
  refine ⟨Y, q, hq, ⟨fun x => ?_⟩, fun K _ y' => ?_⟩
  · obtain ⟨t, w, hw⟩ := hx x
    have := hg t
    refine hr t (Finset.mem_univ t) ?_
    rw [Scheme.Pullback.range_snd]
    rw [← hi' t, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      (U t).ι.isOpenEmbedding.isInducing.specializes_iff] at hw
    exact hw.mem_closed (g t).isClosedMap.isClosed_range ⟨w, rfl⟩
  · obtain ⟨t, z, hz⟩ := hK K y'
    refine ⟨t, z ≫ pullback.fst (g t) (i' t), ?_⟩
    rw [Category.assoc, pullback.condition_assoc, hi' t, ← Category.assoc, hz, Category.assoc]

end GlobalTheory.FinCover
