module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.TraceSumRealEmbeddings

open NumberField NumberField.InfinitePlace

theorem re_embedding_mk {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;> rw [h]
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

theorem sum_re_embeddings (F : Type) [Field F] [NumberField F] (x : F) :
    ∑ φ : F →+* ℂ, (φ x).re = ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  classical
  rw [← Finset.univ.sum_fiberwise (fun φ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hw : ∀ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (F →+* ℂ)), (φ x).re = (w.embedding x).re :=
    fun φ hφ => by rw [← (Finset.mem_filter.mp hφ).2, re_embedding_mk]
  rw [Finset.sum_congr rfl hw, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

theorem trace_eq_sum_re (F : Type) [Field F] [NumberField F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ => φ x) (fun σ => σ x) (fun φ => rfl),
      ← trace_eq_sum_embeddings]
    exact (eq_ratCast (algebraMap ℚ ℂ) _).symm
  rw [← Complex.re_sum, ← h2, Complex.ratCast_re]

theorem traceInf_algebraMap (F : Type) [Field F] [NumberField F] (x : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf F (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) x) =
      ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [trace_eq_sum_re, sum_re_embeddings]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  rw [InfiniteAdeleRing.algebraMap_apply]
  simpa using InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)

end GlobalTheory.TraceSumRealEmbeddings
