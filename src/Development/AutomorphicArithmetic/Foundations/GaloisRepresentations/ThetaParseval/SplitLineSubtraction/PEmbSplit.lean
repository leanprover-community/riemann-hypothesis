module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.embSplit_holds :
    EmbSplit := by
  intro E _ _ _ emb
  have hcj : ∀ (φ : E →+* ℂ), (ComplexEmbedding.conjugate φ).comp
      (algebraMap (maximalRealSubfield E) E) =
      ComplexEmbedding.conjugate (φ.comp (algebraMap (maximalRealSubfield E) E)) := by
    intro φ
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hinj : ∀ (w w' : InfinitePlace (maximalRealSubfield E)), w.embedding = w'.embedding → w = w' := by
    intro w w' h
    rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h]
  refine ⟨?_, ?_, ?_⟩
  · intro τ
    let w := InfinitePlace.mk (τ.comp (algebraMap (maximalRealSubfield E) E))
    refine ⟨w, ?_⟩
    have hw : (InfinitePlace.mk τ).comap (algebraMap (maximalRealSubfield E) E) =
        (InfinitePlace.mk (emb w).1).comap (algebraMap (maximalRealSubfield E) E) := by
      rw [InfinitePlace.comap_mk, InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
    have hmk : InfinitePlace.mk τ = InfinitePlace.mk (emb w).1 :=
      (IsCMField.equivInfinitePlace E).injective hw
    rcases InfinitePlace.mk_eq_iff.1 hmk with h | h
    · exact Or.inl h
    · right
      rw [← h]
      ext x
      simp [ComplexEmbedding.conjugate_coe_eq]
  · intro w w' h
    apply hinj
    rw [← (emb w).2, ← (emb w').2, h]
  · intro w w' h
    have h1 : w.embedding = ComplexEmbedding.conjugate w'.embedding := by
      rw [← (emb w).2, ← (emb w').2, h, hcj]
    have hww : w = w' := by
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h1,
        InfinitePlace.mk_conjugate_eq]
    subst hww
    apply IsTotallyComplex.complexEmbedding_not_isReal (emb w).1
    exact h.symm
