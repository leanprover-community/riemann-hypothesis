module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem integrable_slice {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β : TI K n) (a : archGroup K n) :
    Integrable (fun s => β (a * zInf K n s)) GroundTheory.Global.posRealMeasure := by
  have hc : Continuous fun s : {r : ℝ // 0 < r} => β (a * zInf K n s) :=
    β.continuous.comp (continuous_const.mul continuous_zInf)
  refine hc.integrable_of_hasCompactSupport ?_
  have hD : IsCompact ((fun r : {r : ℝ // 0 < r} => r * (detA K n a)⁻¹) '' (detA K n '' tsupport β)) :=
    (β.hasCompactSupport.isCompact.image continuous_detA).image (continuous_id.mul continuous_const)
  refine HasCompactSupport.intro hD fun s hs => ?_
  by_contra hne
  exact hs ⟨s * detA K n a, mem_of_kernel_ne_zero hn hne, by simp⟩

private theorem kbar_add {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β β' : TI K n) (a : archGroup K n) : kbar (β + β' : TI K n) a = kbar β a + kbar β' a := by
  simp only [kbar, CompactlySupportedContinuousMap.add_apply]
  exact integral_add (integrable_slice hn β a) (integrable_slice hn β' a)

private theorem kbar_smul {K : Type} [Field K] [NumberField K] {n : ℕ}
    (c : ℂ) (β : TI K n) (a : archGroup K n) : kbar (c • β : TI K n) a = c * kbar β a := by
  simp only [kbar, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

private theorem tensFun_support_bound {K : Type} [Field K] [NumberField K] {n : ℕ}
    (hn : 0 < n) (β : TI K n) (e : TF K n) :
    IsCompact (archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e) ∧
      Function.support (tensFun β e) ⊆
        archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e := by
  refine ⟨(β.hasCompactSupport.isCompact.image continuous_archP).mul
    (e.hasCompactSupport.isCompact.image MultiplicityOne.continuous_finProj), ?_⟩
  intro x hx
  let a := infPart K n (x : AdelicGLn.AdelicGL K n)
  let h := finPart K n (x : AdelicGLn.AdelicGL K n)
  change kbar β a * e h ≠ 0 at hx
  have he := right_ne_zero_of_mul hx
  obtain ⟨s, hs⟩ : ∃ s, β (a * zInf K n s) ≠ 0 := by
    by_contra h0
    simp only [not_exists, ne_eq, not_not] at h0
    exact left_ne_zero_of_mul hx (by simp [kbar, h0])
  have hproj : archP K n (a * zInf K n s) * MultiplicityOne.finProj K n h = x := by
    have hf : MultiplicityOne.finProj K n h = retractOne (finEmb K n h) := rfl
    rw [archimedeanProjection_mul_positiveScalar hn, hf, ← retract_infEmb, ← retractOne_mul]
    change retractOne (infEmb K n (infPart K n (x : AdelicGLn.AdelicGL K n)) *
      finEmb K n (finPart K n (x : AdelicGLn.AdelicGL K n))) = x
    rw [infEmb_infPart_mul_finEmb_finPart, retractOne_coe]
  rw [← hproj]
  exact Set.mul_mem_mul ⟨_, subset_tsupport _ hs, rfl⟩ ⟨_, subset_tsupport _ he, rfl⟩

private theorem tens_apply' {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β : TI K n) (e : TF K n) (x : normOneGL (K := K) (n := n)) : tens β e x = tensFun β e x := by
  have h1 : Continuous (tensFun β e) := by
    unfold tensFun
    exact ((continuous_kbar hn β.continuous β.hasCompactSupport).comp
      (continuous_infPart.comp continuous_subtype_val)).mul
      (e.continuous.comp (continuous_finPart.comp continuous_subtype_val))
  obtain ⟨hC, hS⟩ := tensFun_support_bound hn β e
  have h2 : HasCompactSupport (tensFun β e) :=
    hC.of_isClosed_subset isClosed_closure (closure_minimal hS hC.isClosed)
  have h : Continuous (tensFun β e) ∧ HasCompactSupport (tensFun β e) := ⟨h1, h2⟩
  rw [tens, dite_eq_left h]
  rfl

theorem UpperTheory.ConvolutionTheory.Tf.tensApply :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n), (∀ x, tens β e x = tensFun β e x) ∧
      (tsupport (tens β e) ⊆ archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e) ∧
      (∀ β', tens (β + β') e = tens β e + tens β' e) ∧ (∀ e', tens β (e + e') = tens β e + tens β e') ∧
      ∀ c : ℂ, tens (c • β) e = c • tens β e ∧ tens β (c • e) = c • tens β e := by
  intro K _ _ n hn β e
  refine ⟨tens_apply' hn β e, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hC, hS⟩ := tensFun_support_bound hn β e
    refine closure_minimal ?_ hC.isClosed
    intro x hx
    apply hS
    rwa [Function.mem_support, ← tens_apply' hn β e x]
  · intro β'
    ext x
    simp only [CompactlySupportedContinuousMap.add_apply, tens_apply' hn, tensFun, kbar_add hn, add_mul]
  · intro e'
    ext x
    simp only [CompactlySupportedContinuousMap.add_apply, tens_apply' hn, tensFun, mul_add]
  · intro c
    constructor
    · ext x
      simp only [CompactlySupportedContinuousMap.smul_apply, tens_apply' hn, tensFun, kbar_smul,
        smul_eq_mul, mul_assoc]
    · ext x
      simp only [CompactlySupportedContinuousMap.smul_apply, tens_apply' hn, tensFun, smul_eq_mul]
      ring
