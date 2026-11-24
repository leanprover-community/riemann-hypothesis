module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIInfKerOfIsBaseChange
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

open Module

namespace GlobalTheory.BadCount

theorem finrank_iInf_ker_baseChange : ∀ (K L V W ι : Type) [Field K] [Field L] [Algebra K L]
    [Finite ι] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f →
    ∀ (a : ι → V →ₗ[K] V) (a' : ι → W →ₗ[L] W), (∀ i v, a' i (f v) = f (a i v)) →
      finrank L (⨅ i, LinearMap.ker (a' i) : Submodule L W) =
          finrank K (⨅ i, LinearMap.ker (a i) : Submodule K V) ∧
        (⨅ i, LinearMap.ker (a' i) : Submodule L W) =
          Submodule.span L (f '' ((⨅ i, LinearMap.ker (a i) : Submodule K V) : Set V)) := by
  intro K L V W ι _ _ _ _ _ _ _ _ _ _ _ f hf a a' ha
  refine ⟨GlobalTheory.finrank_iInf_ker_of_isBaseChange K L V W ι f a a' hf ha, ?_⟩
  rw [GlobalTheory.GaloisDescent.span_image_iInf hf]
  exact iInf_congr fun i =>
    (GlobalTheory.GaloisDescent.span_image_ker hf hf (a i) (a' i) (fun v => ha i v)).symm

end GlobalTheory.BadCount
