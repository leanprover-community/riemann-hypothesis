module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import GroundTheory.AutomorphicForms.ReductionFinite
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.exists_open_compact_level_subgroup :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K) (J : ∀ i, Subgroup (Gw n (w i))), (∀ i, CO (J i)) →
          ∃ U : Subgroup (AdelicGLn.FiniteAdelicGL K n), (∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i) ∧
            IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) := by
  intro K _ _ n r w J hJ
  let U : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    { carrier := {h | h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, fun i => ?_⟩
        rw [map_mul, finAt_mul]
        exact mul_mem (ha' i) (hb' i)
      one_mem' := by
        refine ⟨one_mem _, fun i => ?_⟩
        rw [map_one, finAt_one]
        exact one_mem _
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, fun i => ?_⟩
        have h1 : finAt (w i) (finEmb K n a⁻¹) * finAt (w i) (finEmb K n a) = 1 := by
          rw [← finAt_mul, ← map_mul, inv_mul_cancel, map_one, finAt_one]
        rw [eq_inv_of_mul_eq_one_left h1]
        exact inv_mem (ha' i) }
  have hmem : ∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i :=
    fun h => Iff.rfl
  have hset : (U : Set (AdelicGLn.FiniteAdelicGL K n)) =
      (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) ∩
        ⋂ i, (fun h => finAt (w i) (finEmb K n h)) ⁻¹' (J i : Set (Gw n (w i))) := by
    ext h
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact hmem h
  have hopen : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    rw [hset]
    refine (AdelicGLn.isOpen_integralFiniteGL K n).inter (isOpen_iInter_of_finite fun i => ?_)
    exact (hJ i).2.preimage ((continuous_finAt (w i)).comp continuous_finEmb)
  refine ⟨U, hmem, hopen, ?_⟩
  exact (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen U hopen) fun _ h => h.1
