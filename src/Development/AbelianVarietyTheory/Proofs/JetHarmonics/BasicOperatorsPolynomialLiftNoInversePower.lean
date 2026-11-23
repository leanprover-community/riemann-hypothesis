module

public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPolyDiffOpRadialPartEqShiftedOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MirrorTodaRadialOperatorPolynomialCoefficientLifStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftConjLastMinorMulRadialPairTermStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialLiftDualOperatorCombinationStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem mem_nfSpan_zero_zero_one_of_mem {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {P : M.Par}
    (d : Q.NFData P A) (T : Set A) {x : A} (hx : x ∈ T) : x ∈ nfSpan d T 0 0 1 := by
  refine Submodule.subset_span ⟨1, (bmon d).one_mem, [x], rfl, ?_, ?_⟩
  · intro h hh
    rw [List.mem_singleton] at hh
    exact hh ▸ hx
  · simp

theorem basicLiftAll_zero : BasicLiftAll (fun _ => 0) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN x hx
  obtain ⟨y, -, h | h | h | h⟩ := hx
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.exists_polyDiffOp_radialPart_eq_shiftedOperator Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.mirrorTodaRadialOperator_polynomialCoefficient_lift Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.polyLift_conjLastMinor_mul_radialPairTerm Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.polynomial_lift_dual_operator_combination Wp Wq P Bs X μ L st l0 d hD hN y)

end GlobalTheory.HatNF
