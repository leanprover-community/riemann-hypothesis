module

public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFiniteEtaleOfIsClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma UpperTheory.isPullback_whisker_fst {S : Scheme.{0}} {T T' G : Over S} (y : T' ⟶ T) :
    IsPullback (y ▷ G).left (fst T' G).left (fst T G).left y.left := by
  have h : IsPullback (y ▷ G) (fst T' G) (fst T G) y := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift s.snd (s.fst ≫ snd _ _)) ?_ ?_ ?_⟩⟩
    · intro s
      apply CartesianMonoidalCategory.hom_ext
      · simp [s.condition]
      · simp
    · intro s
      simp
    · intro s m h1 h2
      apply CartesianMonoidalCategory.hom_ext
      · simpa using h2
      · simp only [lift_snd]
        rw [← h1, Category.assoc, whiskerRight_snd]
  exact h.map (Over.forget S)

theorem UpperTheory.clopProj_finrank_pullback :
    ∀ {S : Scheme.{0}} {T T' G : Over S} (y : T' ⟶ T) (V : (T ⊗ G).left.Opens), IsFinite G.hom → Etale G.hom → IsClosed (V : Set (T ⊗ G).left) → ∀ t : T'.left, (UpperTheory.RepresentationRank.proj ((y ▷ G).left ⁻¹ᵁ V)).finrank t = (UpperTheory.RepresentationRank.proj V).finrank (y.left t) := by
  intro S T T' G y V hfin het hcl t
  obtain ⟨hF, hE⟩ := UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hcl
  have hsq := (isPullback_morphismRestrict (y ▷ G).left V).paste_vert (UpperTheory.isPullback_whisker_fst y)
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq t
