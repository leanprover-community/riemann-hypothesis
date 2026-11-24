module

public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopRepUnique
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfIsSplitOfRank
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepPullback
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsFiniteOfIsPullbackFpqc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.clopRep_finite_etale_of_constant_rank :
    ∀ {S : Scheme.{0}} (G Y : Over S) (U : (Y ⊗ G).left.Opens) (n : ℕ), IsFinite G.hom → Etale G.hom → (∀ s, G.hom.finrank s = n) → UpperTheory.RepresentationRank.Rep G Y U → IsFinite Y.hom ∧ Etale Y.hom := by
  intro S G Y U n hf he hn hR
  obtain ⟨S', t, h1, h2, h3, hs⟩ := GlobalTheory.FinEt.exists_isSplitOfRank_pullback G.hom hn
  obtain ⟨Y'', U'', hR'', hf'', he''⟩ := UpperTheory.exists_clopRep_of_isSplitOfRank ((Over.pullback t).obj G) n hs
  obtain ⟨U', hR'⟩ := UpperTheory.exists_clopRep_pullback t G Y U hR
  obtain ⟨e⟩ := UpperTheory.clopRep_unique _ _ _ _ _ hR' hR''
  have hcomp : pullback.snd Y.hom t = e.hom.left ≫ Y''.hom := (Over.w e.hom).symm
  have hiso : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hqf : IsFinite (pullback.snd Y.hom t) := by
    rw [hcomp]; infer_instance
  have hqe : Etale (pullback.snd Y.hom t) := by
    rw [hcomp]; infer_instance
  have hpb := IsPullback.of_hasPullback Y.hom t
  refine ⟨UpperTheory.isFinite_of_isPullback_fpqc _ _ _ _ hpb h3 inferInstance inferInstance hqf, ?_⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb.flip ⟨⟨h3, inferInstance⟩, inferInstance⟩ hqe
