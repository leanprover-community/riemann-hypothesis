module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianLatticeSelfDualSmulTransposeInert
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.skewHermitianLattice_selfDual_smul_transpose_inert : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s →
  ∀ {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∀ (t : F), t ≠ 0 → ∀ (s₁ s₂ : E), w.valuation E s₁ = 1 → w.valuation E s₂ = 1 →
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) →
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) →
  GlobalTheory.AdelicU.IsSelfDualAt σ (algebraMap F E t • W.Jᵀ) W.L v := by
  first | exact @GlobalTheory.SkewScaleInert.isSelfDualAt_smul_transpose | exact GlobalTheory.SkewScaleInert.isSelfDualAt_smul_transpose | (intros; apply GlobalTheory.SkewScaleInert.isSelfDualAt_smul_transpose <;> assumption)
