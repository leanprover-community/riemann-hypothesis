module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.expSub :
    ∀ (d d' : ℕ) (S : Subalgebra ℂ (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ))
      (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d') (Fin d') ℂ), (A, B) ∈ S → (NormedSpace.exp A, NormedSpace.exp B) ∈ S := by
  intro d d' S A B h
  have hc : IsClosed (S : Set (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule S)
  have hA : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • A ^ n) (NormedSpace.exp A) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hB : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • B ^ n) (NormedSpace.exp B) := by
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B
  refine hc.mem_of_tendsto (hA.prodMk hB) (Filter.Eventually.of_forall fun s => ?_)
  refine S.sum_mem fun n _ => ?_
  exact S.smul_mem (S.pow_mem h n) ((n.factorial : ℂ)⁻¹)
