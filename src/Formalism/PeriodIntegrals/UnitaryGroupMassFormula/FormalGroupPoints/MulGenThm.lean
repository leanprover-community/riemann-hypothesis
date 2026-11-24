module

public import Formalism.PeriodIntegrals.FglPtW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.ConstantCoeffPsubst
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem

@[expose] public section

noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

theorem mulGen_thm : PI.FglPtW.MulGen := by
  intro K _ S l ex hex hl c hG σ a ha
  obtain ⟨haS, ha0⟩ := ha
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  have hsub : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero hex'

  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h1 := congrArg MvPowerSeries.constantCoeff hl
    rw [PowerSeries.constantCoeff_subst hsub,
      finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero])] at h1
    simpa using h1.trans (PowerSeries.constantCoeff_X (R := K))
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit K) = 0 := by simp
  have hXs : PowerSeries.HasSubst (MvPowerSeries.X () : MvPowerSeries Unit K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hX0
  have has : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  have hA0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_subst_eq_zero hX0 l hl0, mul_zero]
  have hAs := PowerSeries.HasSubst.of_constantCoeff_zero hA0

  have hinner : PowerSeries.subst a (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) =
      MvPowerSeries.C c * PowerSeries.subst a l := by
    rw [← PowerSeries.coe_substAlgHom has, map_mul, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_comp_subst_apply hXs has]
    congr 1
    · have h2 := (PowerSeries.substAlgHom has).commutes c
      rw [PowerSeries.coe_substAlgHom] at h2
      first
        | exact h2
        | simp
        | (simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h2
           exact h2)
    · congr 1
      exact PowerSeries.subst_X has
  have key : PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex =
      PowerSeries.subst a (PowerSeries.subst (MvPowerSeries.C c *
        PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex) := by
    rw [PowerSeries.subst_comp_subst_apply hAs has, hinner]
  rw [key]
  refine ⟨?_, ?_⟩
  · rw [serOver_iff]
    exact subst_mem_SerS S ha0 ((serOver_iff S a).mp haS) ((serOver_iff S _).mp hG)
  · exact PowerSeries.constantCoeff_subst_eq_zero ha0 _
      (PowerSeries.constantCoeff_subst_eq_zero hA0 ex hex)

end PI.FglPtW.Wk

end
