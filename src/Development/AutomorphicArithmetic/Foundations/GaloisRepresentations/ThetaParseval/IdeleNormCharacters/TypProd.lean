module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

private theorem pl_emb {E : Type} [Field E] [NumberField E] [IsCMField E]
    {w : InfinitePlace (maximalRealSubfield E)} (τ : EmbOver E w) : pl τ.1 = w := by
  unfold pl
  rw [InfinitePlace.comap_mk, τ.2, InfinitePlace.mk_embedding]

private theorem pl_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    pl (ComplexEmbedding.conjugate φ) = pl φ := by
  unfold pl
  rw [InfinitePlace.mk_conjugate_eq]

private theorem eq_or_conj_of_pl_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    {φ ψ : E →+* ℂ} (h : pl φ = pl ψ) : φ = ψ ∨ φ = ComplexEmbedding.conjugate ψ := by
  have hmk : InfinitePlace.mk φ = InfinitePlace.mk ψ :=
    (IsCMField.equivInfinitePlace E).injective (by
      simpa only [IsCMField.equivInfinitePlace_apply, pl] using h)
  rcases InfinitePlace.mk_eq_iff.1 hmk with h' | h'
  · exact Or.inl h'
  · right
    rw [← h']
    exact (star_star φ).symm

theorem UpperTheory.Gal.TP.Chr.typProd :
    UpperTheory.Gal.TP.Chr.TypVal → UpperTheory.Gal.TP.Chr.TypProd := by
  intro hv E _ _ _ emb a b x
  classical
  rw [← Finset.prod_fiberwise Finset.univ (pl (E := E))]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : (emb w).1 ≠ ComplexEmbedding.conjugate (emb w).1 := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal _ (ComplexEmbedding.isReal_iff.2 h.symm)
  have hfib : Finset.univ.filter (fun φ : E →+* ℂ => pl φ = w) =
      {(emb w).1, ComplexEmbedding.conjugate (emb w).1} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      exact eq_or_conj_of_pl_eq (h.trans (pl_emb (emb w)).symm)
    · rintro (rfl | rfl)
      · exact pl_emb _
      · rw [pl_conj, pl_emb]
  rw [hfib, Finset.prod_pair hne, (hv E emb a b w).1, (hv E emb a b w).2,
    ComplexEmbedding.conjugate_coe_eq]
