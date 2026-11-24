module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIndicatorCosetSum
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

theorem _root_.GlobalTheory.T.scaled_indicator_coset_sum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 → ∀ m : 𝓞 F, m ≠ 0 →
    ∃ R : Finset (κ → F), (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) =
      ∑ ξ ∈ R, {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ (a * m)}.indicator
        (fun _ => (1 : ℂ)) := by
  first | exact @GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | exact GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | (intros; apply GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum <;> assumption)
