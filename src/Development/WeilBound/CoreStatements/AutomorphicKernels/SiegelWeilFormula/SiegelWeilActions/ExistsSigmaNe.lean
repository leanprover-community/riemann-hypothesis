module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma_cm (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2 w.embedding, h.2.2.2 w.embedding, star_star]

theorem exists_sigma_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hne
  push_neg at hne
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc : w.IsComplex := h.2.1.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.2 hc
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  change star (w.embedding x) = w.embedding x
  rw [← h.2.2.2 w.embedding, hne]

theorem deltaEx' (h : IsCMExt F E σ) (ε : ℤˣ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -(((ε : ℤ) : E) * δ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · obtain ⟨x, hx⟩ := exists_sigma_ne h
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sigma_sigma_cm h]
    simp
  · exact ⟨1, one_ne_zero, by simp⟩

end PositivityTheory.SiegelWeilFormula.Act.CL

end
