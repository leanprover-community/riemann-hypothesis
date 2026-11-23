module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.TraceRealEmbeddingSum

open NumberField

theorem re_embedding_mk {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;>
    simp [h, ComplexEmbedding.conjugate_coe_eq]

theorem trace_eq_sum_mult_mul_re {F : Type} [Field F] [NumberField F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) =
      ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  apply GlobalTheory.CompanionTheory.AdeleCharLocal.trace_eq_sum <;> assumption

end GlobalTheory.TraceRealEmbeddingSum
