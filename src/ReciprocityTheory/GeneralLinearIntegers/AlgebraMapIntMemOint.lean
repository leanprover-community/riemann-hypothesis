module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  exact PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  first
  | exact Valued.isOpen_valuationSubring _

def Oint (F : Type) [Field F] [NumberField F] : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

theorem isOpen_Oint : IsOpen (Oint F) := by
  exact RestrictedProduct.isOpen_forall_mem fun v => isOpen_integers v

theorem algebraMap_int_mem_Oint (m : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) ∈ Oint F := by
  exact fun v => coe_algebraMap_mem (𝓞 F) F v m

end ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact
