module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

theorem UpperTheory.V.Sd.cuspOf :
    UpperTheory.V.Sd.CuspOf := by
  intro N k _ χ f hχ hv h0
  have hT : (1:ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    refine ⟨ModularGroup.T, ?_, ?_⟩
    · rw [SetLike.mem_coe, Gamma1_mem]
      simp [ModularGroup.T]
    · ext i j
      rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]
  have hinf : IsZeroAtImInfty f := by
    apply ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero f
    rw [← qExpansion_coeff_zero one_pos (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hT)
      (SlashInvariantFormClass.periodic_comp_ofComplex f hT)]
    exact h0
  refine ⟨⟨f.toSlashInvariantForm, f.holo', fun {c} hc => ?_⟩, rfl⟩
  have hc' : IsCusp c 𝒮ℒ := by
    rwa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc']
  intro γ _
  by_cases hd : (N:ℤ) ∣ γ 1 0
  · have hγ : γ ∈ Gamma0 N := Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hd)
    change IsZeroAtImInfty (⇑f ∣[(k:ℤ)] γ)
    rw [hχ γ hγ]
    exact hinf.smul _
  · exact hv γ hd
