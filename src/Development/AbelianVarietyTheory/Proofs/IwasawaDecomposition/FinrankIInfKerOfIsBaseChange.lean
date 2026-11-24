module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open TensorProduct Module

namespace GlobalTheory

theorem finrank_iInf_ker_of_isBaseChange : ∀ (L Ω M M' ι : Type) [Field L] [Field Ω] [Algebra L Ω]
    [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module Ω M'] [Module L M']
    [IsScalarTower L Ω M'] (J : M →ₗ[L] M') (f : ι → M →ₗ[L] M) (f' : ι → M' →ₗ[Ω] M'),
    IsBaseChange Ω J → (∀ i x, f' i (J x) = J (f i x)) →
      finrank Ω ↥(⨅ i, LinearMap.ker (f' i)) = finrank L ↥(⨅ i, LinearMap.ker (f i)) := by
  intro L Ω M M' ι _ _ _ _ _ _ _ _ _ J f f' hJ hf
  have h1 : ⨅ i, LinearMap.ker (f' i) =
      Submodule.span Ω (J '' (⨅ i, LinearMap.ker (f i) : Submodule L M)) := by
    rw [GlobalTheory.GaloisDescent.span_image_iInf hJ]
    exact iInf_congr fun i =>
      (GlobalTheory.GaloisDescent.span_image_ker hJ hJ (f i) (f' i) (fun v => hf i v)).symm
  have h2 : Submodule.span Ω (J '' (⨅ i, LinearMap.ker (f i) : Submodule L M)) =
      ((⨅ i, LinearMap.ker (f i) : Submodule L M).baseChange Ω).map hJ.equiv.toLinearMap := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 2
    ext x
    simp [IsBaseChange.equiv_tmul]
  rw [h1, h2, LinearEquiv.finrank_map_eq, GlobalTheory.finrank_baseChange]

end GlobalTheory
