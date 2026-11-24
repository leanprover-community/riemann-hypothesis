module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem dM_fin (t : (A ℚ)ˣ) (ht : (t : A ℚ).1 = 1) :
    finGL ℚ 2 (Matrix.GeneralLinearGroup.map (pFin ℚ) (dM t)) = dM t := by
  have h := TR.infGL_mul_finGL (dM t)
  have h1 : Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (dM t) = 1 := by
    have ht' : TR.pInf ℚ (t : A ℚ) = 1 := by
      change (TR.infEq ℚ).symm (t : A ℚ).1 = 1
      rw [ht]; exact map_one _
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht']
  rw [h1, map_one, one_mul] at h
  exact h

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.formBd :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.FormBd := by
  intro π hπ f hf
  have hL := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero ℚ π f hf).1
  refine ⟨⟨hL.1, hL.2, ?_, fun s x => hπ f hf s x⟩, fun t ht => ?_⟩
  · obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp (Fb.mem_range_ofCusp.2 (π.cusp f hf))
    obtain ⟨B₀, hB₀⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms φ.2
    subst hφ
    refine ⟨B₀, fun x => ?_⟩
    have h2 : (centralSection ℚ 2 (detModule ℚ 2 x))⁻¹ * x ∈ normOneGL (K := ℚ) (n := 2) := by
      rw [mem_normOneGL_iff_detModule, map_mul, map_inv, detModule_centralSection two_pos, inv_mul_cancel]
    have h3 := hπ _ hf (detModule ℚ 2 x) ((centralSection ℚ 2 (detModule ℚ 2 x))⁻¹ * x)
    rw [mul_inv_cancel_left] at h3
    rw [h3]
    exact hB₀ _ h2
  · have h := π.stable (.fin (Matrix.GeneralLinearGroup.map (pFin ℚ) (dM t))) f hf
    refine ⟨_, h, fun x => ?_⟩
    change f.1 (x * finGL ℚ 2 (Matrix.GeneralLinearGroup.map (pFin ℚ) (dM t))) = _
    rw [dM_fin t ht.1]
