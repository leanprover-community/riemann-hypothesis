module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.JSWPosR

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem kernel_mem_bddForms {ω : HChar E} {F : GA E a → ℂ} (h : F ∈ bddForms E a ω) {X : Type} [MeasurableSpace X]
    (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : GlobalTheory.JSW.IsRapidInf ν k γ) :
    (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ∈ bddForms E a ω := by
  obtain ⟨C, hC⟩ := h.2.2.2
  have hki : Integrable (fun x => ‖k x‖) ν := by simpa using hk.2.2 0
  have hγ : Measurable γ := GlobalTheory.RSThetaM.measurable_gl_of_matrix hk.2.1
  have hm : ∀ g, AEStronglyMeasurable (fun x => k x * F (g * infGL E a (γ x))) ν := fun g =>
    (hk.1.mul ((h.1.comp ((continuous_const_mul g).comp GlobalTheory.CuspQuot.continuous_infGL)).measurable.comp hγ)).aestronglyMeasurable
  have hbd : ∀ g, ∀ᵐ x ∂ν, ‖k x * F (g * infGL E a (γ x))‖ ≤ ‖k x‖ * C := fun g =>
    .of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  refine ⟨?_, fun γ' g => ?_, fun z g => ?_, ∫ x, ‖k x‖ * C ∂ν, fun g => ?_⟩
  · set_option synthInstance.maxHeartbeats 200000 in
    exact continuous_of_dominated hm hbd (hki.mul_const C)
      (.of_forall fun x => continuous_const.mul (h.1.comp (continuous_id.mul continuous_const)))
  · simp only [mul_assoc, h.2.1]
  · simp only [mul_assoc, h.2.2.1]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  · exact norm_integral_le_of_norm_le (hki.mul_const C) (hbd g)

theorem mspanR_le_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (h : π.HasCentChar ω) :
    GlobalTheory.JSW.mspanR π ≤ bddForms E a ω := by
  refine sInf_le ⟨fun φ hφ => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω h hφ,
    fun F hF k => mul_right_mem_bddForms hF k, fun F hF X _ ν _ k γ hk => kernel_mem_bddForms hF ν k γ hk⟩

end GlobalTheory.JSWPosR
