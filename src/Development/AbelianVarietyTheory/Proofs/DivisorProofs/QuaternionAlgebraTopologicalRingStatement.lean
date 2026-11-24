module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionAlgebraTopologicalRing
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.quaternion_algebra_topological_ring : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), IsTopologicalRing ℍ[R, a, b] ∧ Continuous (nrm : ℍ[R, a, b] → R) ∧ Continuous (fun x : ℍ[R, a, b] => x.re) ∧ (T2Space R → T2Space ℍ[R, a, b]) := by
  first | exact @GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 | exact GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 | (intros; apply GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 <;> assumption)
