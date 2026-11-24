module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

theorem adicCompletionIntegers_norm_eq_one_of_mul_eq_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletionIntegers F) (h : x * y = 1) : ‖(x : Fv F v)‖ = 1 := by
  have hx : ‖(x : Fv F v)‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).mpr x.2
  have hy : ‖(y : Fv F v)‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).mpr y.2
  have hxy : ‖(x : Fv F v)‖ * ‖(y : Fv F v)‖ = 1 := by
    rw [← norm_mul]
    have : ((x : Fv F v) * (y : Fv F v)) = 1 := by
      have := congrArg (fun z : v.adicCompletionIntegers F => (z : Fv F v)) h
      simpa using this
    rw [this, norm_one]
  have h0 := norm_nonneg (x : Fv F v)
  have h0' := norm_nonneg (y : Fv F v)
  nlinarith

end GlobalTheory
