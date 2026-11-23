module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Mathlib.Order.CompletePartialOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

namespace FunctorialResolution.EmbeddedResolution

private theorem isIso_restrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Opens)
    (h1 : IsIso (f ∣_ (g ⁻¹ᵁ V))) (h2 : IsIso (g ∣_ V)) : IsIso ((f ≫ g) ∣_ V) := by
  have := h1
  have := h2
  have h : IsIso (f ∣_ (g ⁻¹ᵁ V) ≫ g ∣_ V) := inferInstance
  rw [morphismRestrict_comp]
  exact h

private theorem isIso_restrict_projectionToBase_of_centersLieOver {X : Scheme.{u}} (s : SequenceOfBlowups X)
    (S : Set X) (U : X.Opens) (hU : Disjoint (U : Set X) S) (hs : s.CentersLieOver S)
    (i : ℕ) (hi : i ≤ s.length) :
    IsIso (s.projectionToBase i ∣_ U) := by
  revert hi
  induction i with
  | zero =>
    intro _
    show IsIso (s.projectionToBase 0 ∣_ U)
    have h0 : (homOfLE (Nat.zero_le 0) : (0 : ℕ) ⟶ 0).op = 𝟙 (op (0 : ℕ)) := rfl
    have : IsIso (s.projectionToBase 0) := by
      rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.transitionMap_def, h0, CategoryTheory.Functor.map_id,
        Category.id_comp]
      infer_instance
    infer_instance
  | succ i ih =>
    intro hi
    have hi' : i < s.length := hi
    have h2 : IsIso (s.projectionToBase i ∣_ U) := ih (Nat.le_of_succ_le hi)
    have hcomp : s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1) :=
      s.transitionMap_comp_projectionToBase (Nat.le_succ i)
    have hb : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowupAlongIdealSheaf_blowupMorphism i hi'
    have hres := hb.restrict (s.projectionToBase i ⁻¹ᵁ U)
    have htop : (s.center i).comap (s.projectionToBase i ⁻¹ᵁ U).ι = ⊤ := by
      apply Blowup.comap_eq_top_of_notMem_support
      intro x hx
      have h1 := hs i hi' ((s.projectionToBase i ⁻¹ᵁ U).ι.base x) hx
      have hxV : (s.projectionToBase i ⁻¹ᵁ U).ι.base x
          ∈ ((s.projectionToBase i ⁻¹ᵁ U : (s.schemeAt i).Opens) : Set (s.schemeAt i)) := by
        rw [← Scheme.Opens.range_ι]
        exact Set.mem_range_self x
      have h2' : (s.projectionToBase i).base ((s.projectionToBase i ⁻¹ᵁ U).ι.base x) ∈ (U : Set X) := hxV
      exact Set.disjoint_left.mp hU h2' h1
    rw [htop] at hres
    have h1 : IsIso (s.transitionMapSucc i ∣_ (s.projectionToBase i ⁻¹ᵁ U)) := hres.isIso_of_top
    have key : IsIso ((s.transitionMapSucc i ≫ s.projectionToBase i) ∣_ U) :=
      isIso_restrict_comp (s.transitionMapSucc i) (s.projectionToBase i) U h1 h2
    rw [hcomp] at key
    exact key

theorem isIso_restrict_lastStructMap_of_centersLieOver {X : Scheme.{u}} (s : SequenceOfBlowups X)
    (S : Set X) (U : X.Opens) (hU : Disjoint (U : Set X) S) (hs : s.CentersLieOver S) :
    IsIso (s.lastStructMap ∣_ U) := by
  rw [SequenceOfBlowups.lastStructMap_eq_projectionToBase]
  exact isIso_restrict_projectionToBase_of_centersLieOver s S U hU hs s.length le_rfl

theorem isIso_restrict_lastStructMap_smoothLocus {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f] (s : SequenceOfBlowups X)
    (hs : s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X)) :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by
  refine isIso_restrict_lastStructMap_of_centersLieOver s _ f.smoothLocus ?_ hs
  show Disjoint (f.smoothLocus : Set X) ((f.smoothLocus : Set X)ᶜ)
  exact disjoint_compl_right

end FunctorialResolution.EmbeddedResolution
