module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleFractionalIdealIntegralAvoidMaximals
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem _root_.GlobalTheory.T.exists_scale_fractionalIdeal_integral_avoid_maximals : ∀ (E : Type) [Field E] [NumberField E] (I : Submodule (𝓞 E) E), I.FG → I ≠ ⊥ →
    ∀ (ι : Type) [Fintype ι] (Q : ι → Ideal (𝓞 E)), (∀ i, (Q i).IsMaximal) →
    ∃ s : E, s ≠ 0 ∧ (∀ a ∈ I, IsIntegral ℤ (s * a)) ∧ ∀ i, ∃ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a ∧ o ∉ Q i := by
  first | exact @GlobalTheory.exists_scale_integral_not_le_maximal | exact GlobalTheory.exists_scale_integral_not_le_maximal | (intros; apply GlobalTheory.exists_scale_integral_not_le_maximal <;> assumption)
