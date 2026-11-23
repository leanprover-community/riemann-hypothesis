module

public import GroundTheory.AutomorphicForms.GKModules.Casimir
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.casimir_eq_of_orthonormal_bases :
    ∀ (L : Type) [LieRing L] [LieAlgebra ℝ L] (B : LinearMap.BilinForm ℝ L) (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι ℝ L) (ε : ι → ℝ) (b' : Module.Basis ι' ℝ L) (ε' : ι' → ℝ), (∀ X Y, B X Y = B Y X) → (∀ i, ε i * ε i = 1) → (∀ i j, B (b i) (b j) = if i = j then ε i else 0) → (∀ i, ε' i * ε' i = 1) → (∀ i j, B (b' i) (b' j) = if i = j then ε' i else 0) → casimir b ε = casimir b' ε' := by
  intro L _ _ B ι ι' _ _ _ _ b ε b' ε' hs hε hb hε' hb'
  set u := UniversalEnvelopingAlgebra.ι ℝ (L := L) with hu
  have e1 : ∀ i, u (b i) = ∑ j, (ε' j * B (b' j) (b i)) • u (b' j) := by
    intro i
    conv_lhs => rw [eq_sum_of_orthogonal hε' hb' (b i)]

    simp only [map_sum, map_smul]
  have e2 : ∀ j, u (b' j) = ∑ i, (ε i * B (b i) (b' j)) • u (b i) := by
    intro j
    conv_lhs => rw [eq_sum_of_orthogonal hε hb (b' j)]

    simp only [map_sum, map_smul]
  simp only [casimir]
  calc ∑ i, ε i • (u (b i) * u (b i))
      = ∑ i, ∑ j, (ε i * (ε' j * B (b' j) (b i))) • (u (b i) * u (b' j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h : u (b i) * u (b i) = u (b i) * ∑ j, (ε' j * B (b' j) (b i)) • u (b' j) :=
          congrArg (fun x => u (b i) * x) (e1 i)
        rw [h, Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_smul_comm, smul_smul]
    _ = ∑ j, ∑ i, (ε i * (ε' j * B (b' j) (b i))) • (u (b i) * u (b' j)) := Finset.sum_comm
    _ = ∑ j, ε' j • (u (b' j) * u (b' j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have h : u (b' j) * u (b' j) = (∑ i, (ε i * B (b i) (b' j)) • u (b i)) * u (b' j) :=
          congrArg (fun x => x * u (b' j)) (e2 j)
        rw [h, Finset.sum_mul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, smul_smul, hs (b' j) (b i)]
        congr 1
        ring
