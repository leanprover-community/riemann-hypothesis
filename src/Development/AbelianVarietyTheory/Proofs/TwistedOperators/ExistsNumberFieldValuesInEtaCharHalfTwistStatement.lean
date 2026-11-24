module

public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNumberFieldValuesInEtaCharHalfTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain Formalism.L2.Host

theorem _root_.GlobalTheory.T.exists_numberField_valuesIn_etaChar_halfTwist : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsEtaT H χ → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn (1 / 2) (algebraMap M ℂ) := by
  first | exact @GlobalTheory.EtaValsNumberField.etaVals | exact GlobalTheory.EtaValsNumberField.etaVals | (intros; apply GlobalTheory.EtaValsNumberField.etaVals <;> assumption)
