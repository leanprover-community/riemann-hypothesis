module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.EquivReindex
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
import GroundTheory.HeightsAndTheta.Heights.HermitianLattice

@[expose] public section

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix MeasureTheory Module

open scoped Kronecker

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

section Real

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E)

namespace RealSpace

end RealSpace

end Real

open scoped Classical in
open Classical in
theorem det_basisMatrix_sq : (basisMatrix K).det ^ 2 = ((discr K : ℤ) : ℂ) := by
  exact (discr_eq_basisMatrix_det_sq K).symm

theorem basisMatrix_apply' (τ σ : K →+* ℂ) :
    basisMatrix K τ σ = σ ((RingOfIntegers.basis K (equivReindex K τ) : 𝓞 K) : K) := by
  simp [basisMatrix, canonicalEmbedding.latticeBasis_apply, integralBasis_apply,
    canonicalEmbedding.apply_at]

section Gram

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]

end Gram

section RiemannRoch

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]
  {s : ι → E}



end RiemannRoch

namespace HermitianExtension

variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')

end HermitianExtension

end

end GroundTheory.Heights₂.Heights
