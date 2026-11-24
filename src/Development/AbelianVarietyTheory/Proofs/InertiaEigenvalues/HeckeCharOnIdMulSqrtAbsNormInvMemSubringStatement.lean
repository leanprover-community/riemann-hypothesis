module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharOnIdMulSqrtAbsNormInvMemSubring
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

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (O : Subring ℂ) (cc : Ideal (𝓞 L)), cc ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 L), cc ≤ P.asIdeal → (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) → (((χ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc) : ℝ) : ℂ))⁻¹ ∈ O := by
  first | exact @GlobalTheory.HeckeIdealValue.inv_mem | exact GlobalTheory.HeckeIdealValue.inv_mem | (intros; apply GlobalTheory.HeckeIdealValue.inv_mem <;> assumption)
