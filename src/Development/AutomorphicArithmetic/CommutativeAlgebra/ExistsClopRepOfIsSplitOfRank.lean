module

public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfDisjointOpenCover
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepTrivial
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma tensor_fe {S : Scheme.{0}} (Y₁ Y₂ : Over S) (h1 : IsFinite Y₁.hom) (e1 : Etale Y₁.hom)
    (h2 : IsFinite Y₂.hom) (e2 : Etale Y₂.hom) :
    IsFinite (Y₁ ⊗ Y₂).hom ∧ Etale (Y₁ ⊗ Y₂).hom := by
  have hY : (Y₁ ⊗ Y₂).hom = pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom := rfl
  rw [hY]
  exact ⟨inferInstance, inferInstance⟩

private lemma rep_empty {S : Scheme.{0}} (G : Over S) (hG : IsEmpty G.left) :
    UpperTheory.RepresentationRank.Rep G (Over.mk (𝟙 S)) (⊥ : ((Over.mk (𝟙 S)) ⊗ G).left.Opens) := by
  refine ⟨by simp, fun T V _ => ?_⟩
  have hE : IsEmpty (T ⊗ G).left := ⟨fun x => hG.false ((CartesianMonoidalCategory.snd T G).left x)⟩
  have hV : V = ⊥ := by
    ext x
    exact hE.elim x
  subst hV
  refine ⟨Over.homMk T.hom (by simp), ?_, ?_⟩
  · ext x
    exact hE.elim x
  · intro y _
    ext
    simpa using Over.w y

theorem UpperTheory.exists_clopRep_of_isSplitOfRank :
    ∀ {S : Scheme.{0}} (G : Over S) (n : ℕ), GlobalTheory.FinEt.IsSplitOfRank G.hom n → ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U ∧ IsFinite Y.hom ∧ Etale Y.hom := by
  intro S G n
  induction n generalizing G with
  | zero =>
    intro h
    have hG : IsEmpty G.left := (GlobalTheory.FinEt.isSplitOfRank_zero_iff G.hom).1 h
    refine ⟨Over.mk (𝟙 S), ⊥, rep_empty G hG, ?_, ?_⟩
    · show IsFinite (𝟙 S)
      infer_instance
    · show Etale (𝟙 S)
      infer_instance
  | succ n ih =>
    intro h
    obtain ⟨σ, hσ, V, hσp, hrange, hV⟩ := h.exists_of_succ
    obtain ⟨Y₁, U₁, hR₁, hf₁, he₁⟩ := UpperTheory.exists_clopRep_trivial S
    obtain ⟨Y₂, U₂, hR₂, hf₂, he₂⟩ := ih (Over.mk (V.ι ≫ G.hom)) hV
    obtain ⟨U, hU⟩ := UpperTheory.exists_clopRep_of_disjoint_open_cover G (Over.mk (𝟙 S)) (Over.mk (V.ι ≫ G.hom)) Y₁ Y₂
      (Over.homMk σ hσp) (Over.homMk V.ι rfl) U₁ U₂ hσ (show IsOpenImmersion V.ι from inferInstance)
      (show Set.range σ = (Set.range V.ι)ᶜ by rw [hrange, compl_compl]) hR₁ hR₂
    exact ⟨Y₁ ⊗ Y₂, U, hU, tensor_fe Y₁ Y₂ hf₁ he₁ hf₂ he₂⟩
