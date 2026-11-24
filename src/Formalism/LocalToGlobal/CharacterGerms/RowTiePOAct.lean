module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.LocalToGlobal.CharacterGerms.RowTiePLogExSt
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActLog
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSg

@[expose] public section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OAct

open PartialDerivEval LogEx OActLog OActSg

variable {C : Type} [Field C]

theorem tyS_smul (l : ℕ) (c : C) (a : ℕ → C) : tyS l (fun s => c * a s) = c • tyS l a := by
  ext n
  rw [PowerSeries.coeff_smul]
  simp only [tyS, PowerSeries.coeff_mk, smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero]

variable {dd : ℕ}

theorem uncurry_sub (f g : PS C 1 dd) : un1 (f - g) = un1 f - un1 g := by
  funext μ
  show MvPowerSeries.coeff _ (f - g) = MvPowerSeries.coeff _ f - MvPowerSeries.coeff _ g
  exact map_sub _ _ _

theorem uncurry_C_mul (c : C) (f : PS C 1 dd) : un1 (MvPowerSeries.C c * f) = MvPowerSeries.C c * un1 f := by
  funext μ
  show MvPowerSeries.coeff _ (MvPowerSeries.C c * f) = MvPowerSeries.coeff μ (MvPowerSeries.C c * un1 f)
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rfl

theorem uncurry_linear_combination (c : Fin dd → C) (f : Fin dd → PS C 1 dd) :
    un1 (∑ j, MvPowerSeries.C (c j) * f j) = ∑ j, MvPowerSeries.C (c j) * un1 (f j) := by
  funext μ
  show MvPowerSeries.coeff _ (∑ j, MvPowerSeries.C (c j) * f j) =
    MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (c j) * un1 (f j))

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rfl

theorem integralSeries_uncurry_one {V : VF C} {f : PS C 1 dd} (hf : IntS V f) : IntS V (un1 f) := fun _ => hf _

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem sgP_smul (Y : FBChart C V O dd) (c : C) (v : Fin dd → C) :
    Y.sgP (c • v) = MvPowerSeries.C c * Y.sgP v := by
  unfold FBChart.sgP
  rw [mul_neg, Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

end OAct

end Formalism.L2.FormalSeriesBounds
