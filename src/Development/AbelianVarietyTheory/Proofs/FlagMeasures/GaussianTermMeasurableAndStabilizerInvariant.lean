module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem mem_lamX_mul_right (I : AutInst) (x : Fin I.n → I.E) (g : I.Gf) (k : I.Gf) (hk : k ∈ I.Kset) :
    x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g) := by
  have h := (GlobalTheory.PointLattice.lamX_selfDual I (1, g)).2.2.2.2 (1, k) hk
  rw [Prod.mk_mul_mk, mul_one] at h
  rw [h]

theorem uMat_inv_eq {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : (uMat g)⁻¹ = uMat g⁻¹ :=
  (Matrix.coe_units_inv (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)).symm

theorem gaussAt_meas_inv : ∀ (I : AutInst) (x : Fin I.n → I.E), IsOpen {h : I.Gf | x ∈ lamX I (1, h)} ∧ (∀ v, Measurable fun g : Formalism.REAL.UJ (I.ε v) => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x))) ∧ (∀ h g : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → (x ∈ lamX I (1, h * g) ↔ x ∈ lamX I (1, g))) ∧ (∀ g : I.Gf, ∀ k ∈ I.Kset, x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g)) ∧ ∀ v (h g : Formalism.REAL.UJ (I.ε v)), uMat h *ᵥ infVec I v x = infVec I v x → (uMat (h * g))⁻¹ *ᵥ infVec I v x = (uMat g)⁻¹ *ᵥ infVec I v x := by
  intro I x
  refine ⟨?_, fun v => ?_, fun h g hh => ?_, fun g k hk => mem_lamX_mul_right I x g k hk, fun v h g hh => ?_⟩
  · rw [isOpen_iff_mem_nhds]
    intro g hg
    have hK : IsOpen I.Kset := (GlobalTheory.adelicStab_isCompact_isOpen I).2.1
    have hc : Continuous fun h : I.Gf => g⁻¹ * h := continuous_const.mul continuous_id
    have h1 : (1 : I.Gf) ∈ I.Kset := (Ksub I).one_mem
    refine Filter.mem_of_superset ((hK.preimage hc).mem_nhds (by simpa using h1)) fun h hh => ?_
    have := (mem_lamX_mul_right I x g (g⁻¹ * h) hh).2 hg
    rwa [mul_inv_cancel_left] at this
  · refine Continuous.measurable (ENNReal.continuous_ofReal.comp ?_)
    have hc : Continuous fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹ := by
      simp only [uMat_inv_eq]
      exact Units.continuous_coe_inv.comp continuous_subtype_val
    have hc2 := hc.matrix_mulVec (continuous_const (y := infVec I v x))
    unfold gauss
    refine Real.continuous_exp.comp (Continuous.neg (continuous_finsetSum _ fun i _ => ?_))
    exact (((continuous_apply i).comp hc2).norm).pow 2
  · rw [(GlobalTheory.PointLattice.lamX_selfDual I (1, h * g)).1, (GlobalTheory.PointLattice.lamX_selfDual I (1, g)).1]
    have h1 : I.fmat g⁻¹ = I.fmat (h * g)⁻¹ * I.fmat h := by
      have : g⁻¹ = (h * g)⁻¹ * h := by simp
      rw [this]; rfl
    change I.fmat (h * g)⁻¹ *ᵥ afVec I x ∈ I.Lf ↔ I.fmat g⁻¹ *ᵥ afVec I x ∈ I.Lf
    rw [h1, ← Matrix.mulVec_mulVec, hh]
  · rw [uMat_inv_eq, uMat_inv_eq]
    have h1 : uMat g⁻¹ = uMat (h * g)⁻¹ * uMat h := by
      have : g⁻¹ = (h * g)⁻¹ * h := by simp
      rw [this]; rfl
    rw [h1, ← Matrix.mulVec_mulVec, hh]

end GlobalTheory.StabUnfold
