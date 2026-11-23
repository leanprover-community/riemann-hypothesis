module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Mathlib.NumberTheory.NumberField.CMField
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.CMTypeRealEmb

theorem comp_isReal {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    ComplexEmbedding.IsReal (φ.comp (algebraMap (maximalRealSubfield E) E)) := by
  rw [ComplexEmbedding.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply]
  rw [← IsCMField.complexEmbedding_complexConj]
  congr 1
  exact IsCMField.complexConj_apply_eq_self E a

theorem exists_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E),
      φ i (a : E) = ((e i a : ℝ) : ℂ) := by
  set F := maximalRealSubfield E
  let ψ : I → F →+* ℂ := fun i => (φ i).comp (algebraMap F E)
  have hre : ∀ i, ComplexEmbedding.IsReal (ψ i) := fun i => comp_isReal (φ i)
  let e : I → Emb F := fun i => (hre i).embedding
  have he : ∀ i a, ((e i a : ℝ) : ℂ) = φ i (a : E) := fun i a =>
    (hre i).coe_embedding_apply a
  have hplace : ∀ i, (InfinitePlace.mk (φ i)).comap (algebraMap F E) = InfinitePlace.mk (ψ i) :=
    fun i => InfinitePlace.comap_mk _ _
  refine ⟨Equiv.ofBijective e ⟨?_, ?_⟩, fun i a => (he i a).symm⟩
  · intro i j hij
    have hψ : ψ i = ψ j := by
      ext a
      show φ i (a : E) = φ j (a : E)
      rw [← he, ← he, hij]
    have h1 : InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j) := by
      apply (IsCMField.equivInfinitePlace E).injective
      simp only [IsCMField.equivInfinitePlace_apply]
      rw [hplace, hplace, hψ]
    rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
    · obtain ⟨k, _, hk⟩ := hφ (φ j)
      exact (hk i (Or.inl h.symm)).trans (hk j (Or.inl rfl)).symm
    · obtain ⟨k, _, hk⟩ := hφ (φ j)
      exact (hk i (Or.inr h.symm)).trans (hk j (Or.inl rfl)).symm
  · intro f
    let fc : F →+* ℂ := Complex.ofRealHom.comp f
    have hfc : ComplexEmbedding.IsReal fc := by
      rw [ComplexEmbedding.isReal_iff]
      ext a
      simp [fc]
    let w : InfinitePlace E := (IsCMField.equivInfinitePlace E).symm (InfinitePlace.mk fc)
    obtain ⟨i, hi, _⟩ := hφ w.embedding
    have hmk : InfinitePlace.mk (φ i) = w := by
      rcases hi with h | h
      · rw [← h, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
    have h2 : InfinitePlace.mk (ψ i) = InfinitePlace.mk fc := by
      rw [← hplace, hmk]
      have := (IsCMField.equivInfinitePlace E).apply_symm_apply (InfinitePlace.mk fc)
      rw [IsCMField.equivInfinitePlace_apply] at this
      exact this
    have h3 : ψ i = fc := by
      rcases InfinitePlace.mk_eq_iff.mp h2 with h | h
      · exact h
      · rw [← h]; exact ((ComplexEmbedding.isReal_iff).mp (hre i)).symm
    refine ⟨i, ?_⟩
    ext a
    apply Complex.ofReal_injective
    rw [he]
    show ψ i a = fc a
    rw [h3]

end GlobalTheory.CMTypeRealEmb
