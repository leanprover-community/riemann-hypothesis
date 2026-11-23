module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import GroundTheory.AutomorphicForms.CuspidalProjection.OrthogonalProjectionOntoCompSubtypeL
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
import GroundTheory.AutomorphicForms.SphericalLaurent

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem comp_integrated_of_left_inv {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (u : G) (f : CompactlySupportedContinuousMap G ℂ) (hf : ∀ x, f (u * x) = f x) :
    π u ∘L π.integrated μ (UnitaryRep.ccToL1 μ f) = π.integrated μ (UnitaryRep.ccToL1 μ f) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [ContinuousLinearMap.comp_apply, UnitaryRep.inner_map_right, CuspidalProjection.inner_integrated_ccToL1,
    CuspidalProjection.inner_integrated_ccToL1, ← integral_mul_left_eq_self (μ := μ) _ u⁻¹]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have h : f (u⁻¹ * x) = f x := by rw [← hf (u⁻¹ * x), mul_inv_cancel_left]
  rw [h, UnitaryRep.inner_map_left, inv_inv, UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply π u,
    mul_inv_cancel, UnitaryRep.map_one_apply]

theorem UpperTheory.rhoF_comp_Ofin_of_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
      (e : TF K n) (u : AdelicGLn.FiniteAdelicGL K n), (∀ x, e (u * x) = e x) → rhoF μ u ∘L Ofin μ m e = Ofin μ m e := by
  intro K _ _ n μ _ m _ e u hu
  exact comp_integrated_of_left_inv m ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n)
    MultiplicityOne.continuous_finProj) u e hu
