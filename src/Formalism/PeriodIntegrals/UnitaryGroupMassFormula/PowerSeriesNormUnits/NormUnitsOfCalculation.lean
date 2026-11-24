module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffVar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsSubstitution
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.SimeqSubst1
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.StepUnitsOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TendstoCoeffOfCont
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TraceAt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

theorem stepTrace_of (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
    (hZ : CalcZpScale) : StepTrace := by
  intro p _ l ex ph S hH hA δ hδ
  obtain ⟨hex0, hinv, hp2, h22, hswap, -, -, hintS, hIA, htr, -, -, hB, hunit⟩ := hH
  have hU2 := hunit ((2 : ℂ_[p]), (2 : ℂ_[p])) h22 (norm_two_of hp2) (norm_two_of hp2)
  have hph := ph_const_of hU2 hex0 hinv
  obtain ⟨t, ht⟩ := htr δ hδ
  have h2inv : ∃ h : ℤ_[p], 2 * zc h = 1 := by
    obtain ⟨h, hh⟩ := zc_inv_of (2 : ℤ_[p]) (by rw [zc_two]; exact norm_two_of hp2)
    exact ⟨h, by rwa [zc_two] at hh⟩
  exact trace_at hE hSub hC hD hZ hex0 hinv hph hIA hB δ.1 δ.2 (hintS δ hδ) (hintS δ.swap (hswap δ hδ)) t ht
    (hA δ hδ) hU2 h2inv (Xv ()) (constantCoeff_var ()) (int_X ())

theorem stepSum_of (hE : CalcEquiv) (hSub : CalcSubst) : StepSum := by
  intro p _ l ex ph S hH hA hT α hα
  obtain ⟨hex0, hinv, -, -, hswap, -, hmul, hintS, -, -, -, hdec, -, hunit⟩ := hH
  obtain ⟨β, hβ, γ, hγ, hb1, hb2, hg1, hg2, rfl⟩ := hdec α hα
  exact sum_at hE hSub hex0 hinv β γ (hintS γ hγ) (hA β hβ) (hT (β.swap * γ) (hmul β.swap (hswap β hβ) γ hγ))
    (hunit β hβ hb1 hb2) (hunit γ hγ hg1 hg2)

theorem target_of_calc (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
    (hZ : CalcZpScale) : Target :=
  target_of_steps (stepUnits_of hE hSub hC hD) (stepAll_of hE hSub) (stepTrace_of hE hSub hC hD hZ)
    (stepSum_of hE hSub)

theorem norm_units_of_calculation : Target :=
  target_of_calc norm_units_equivalence norm_units_substitution norm_units_closed_form natCast_dense_p_adic norm_units_zp_scaling

end PI.PhNormUnits.UnitaryGroupMassFormula
