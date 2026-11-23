module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementA
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

namespace Formalism.L2.Th1.B.Add1

open Formalism.InvariantFactorPaths.G7 (at1)

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [CharZero K]

def at1H {ι : Type} (x : ι) : PowerSeries K →ₐ[K] MvPowerSeries ι K :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.X x)

theorem triple_lintegral_eq {ι : Type} (x : ι) (f : PowerSeries K) : at1 x f = at1H x f := by
  simp only [Formalism.InvariantFactorPaths.G7.at1, at1H, PowerSeries.coe_substAlgHom]

theorem inVarAlgHom_C {ι : Type} (x : ι) (c : K) :
    at1H x (PowerSeries.C c) = (MvPowerSeries.C c : MvPowerSeries ι K) := by
  rw [← triple_lintegral_eq]
  exact PowerSeries.subst_C c

theorem cc_psubst {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha f hf

theorem constantCoeff_inVar_eq_zero {ι : Type} (x : ι) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (at1 x f) = 0 :=
  cc_psubst (MvPowerSeries.constantCoeff_X x) hf

theorem pd_mul {ι : Type} (i : ι) (x y : MvPowerSeries ι K) :
    pd i (x * y) = x * pd i y + y * pd i x := by
  simp only [Formalism.L2.Th1.B.pd, Derivation.leibniz, smul_eq_mul]

theorem pd_sub {ι : Type} (i : ι) (x y : MvPowerSeries ι K) : pd i (x - y) = pd i x - pd i y :=
  map_sub (MvPowerSeries.pderiv (R := K) i) x y

theorem fLog_one (h1 : ExpLogRules) {ι : Type} : fLog (1 : MvPowerSeries ι K) = 0 := by
  obtain ⟨hA, hB, -⟩ := h1 K ι
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries ι K) = 0 := map_zero _
  have hsq : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K) * Formalism.L2.Th1.B.fExp 0 = Formalism.L2.Th1.B.fExp 0 * 1 := by
    rw [← hA 0 0 h0 h0, add_zero, mul_one]
  have hu : IsUnit (Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K)) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [(hB 0 h0).1]; exact isUnit_one)
  have he : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K) = 1 := hu.mul_left_cancel hsq
  have hl := (hB 0 h0).2
  rw [he] at hl
  exact hl

end SlopeTestRemainingChoices


end Formalism.L2.Th1.B.Add1
