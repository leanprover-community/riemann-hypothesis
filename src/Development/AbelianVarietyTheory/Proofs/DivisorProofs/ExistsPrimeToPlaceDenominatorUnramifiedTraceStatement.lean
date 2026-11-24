module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPlaceDenominatorUnramifiedTrace
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.exists_prime_to_place_denominator_unramified_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (v : Pl (F := F)) (e : E),
    (∀ o : 𝓞 E, algebraMap F (Fv F v) (Algebra.trace F E ((o : E) * e)) ∈ v.adicCompletionIntegers F) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * e) := by
  first | exact @GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral | exact GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral | (intros; apply GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral <;> assumption)
