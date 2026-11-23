module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem tm_archEmbed_mulVec_vec (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ]
    (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ)
    (C : LatEmb F) (γ : C.h.unitaryGroup) (x : Λ) (τ : Ψ) :
    C.tm (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ) τ *ᵥ C.vec x τ =
      fun i => embOf (F.σ τ)
        (((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) i) := by
  set b := Pi.basisFun E (Fin (j + j')) with hb
  set G : GL (Fin (j + j')) E := (unitaryGroupEquivMatrix C.h b γ).1 with hG
  have hGM : (G : Matrix (Fin (j + j')) (Fin (j + j')) E) =
      LinearMap.toMatrix b b (((γ : C.h.unitaryGroup) :
        (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) : (Fin (j + j') → E) →ₗ[E] (Fin (j + j') → E)) :=
    unitaryGroupEquivMatrix_apply C.h b γ
  have hact : ∀ v : Fin (j + j') → E, (G : Matrix (Fin (j + j')) (Fin (j + j')) E) *ᵥ v =
      ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) v := by
    intro v
    rw [hGM, hb, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_mulVec]
    rfl
  have htm : C.tm (archEmbed C.h b γ) τ =
      (G : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) := by
    have hw : ∀ w : InfinitePlace E,
        (((archEmbed C.h b γ : archUnitary C.h b) : InfinitePlace E → GL (Fin (j + j')) ℂ) w :
          Matrix (Fin (j + j')) (Fin (j + j')) ℂ) =
        (G : Matrix (Fin (j + j')) (Fin (j + j')) E).map w.embedding := fun w => rfl
    unfold LatEmb.tm tauMat
    split_ifs with h
    · rw [hw, h]
    · rw [hw]
      rcases InfinitePlace.embedding_mk_eq (embOf (F.σ τ)) with h' | h'
      · exact absurd h' h
      · have h'' : (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) := h'
        rw [h'']
        ext a c
        simp [ComplexEmbedding.conjugate_coe_eq]
  rw [htm]
  funext i
  have := RingHom.map_mulVec (embOf (F.σ τ)) (G : Matrix (Fin (j + j')) (Fin (j + j')) E) (C.e x) i
  rw [hact] at this
  rw [this]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
