module

public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSo
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemWOfNorm
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section W

variable {p : ℕ} [Fact p.Prime]

theorem mem_W_of_norm (i0 : K0 p →+* ℂ_[p]) (hW : ∀ x : WW p, ‖i0 (algebraMap (WW p) (K0 p) x)‖ ≤ 1) (x : K0 p)
    (hx : ‖i0 x‖ ≤ 1) : ∃ w : WW p, algebraMap (WW p) (K0 p) w = x := by
  first | exact UpperTheory.Reformulated.B.Qi32.mem_W_of_norm .. | (apply UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW x hx | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW x | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p

theorem cc_Ex {ι K : Type} [Field K] [CharZero K] {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) :
    constantCoeff (Ex f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_Ex hf]
  simp

theorem cc_lgE (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (iC : Kc →+* ℂ_[p])
    (th : PowerSeries (WW p)) (th_zero : PowerSeries.constantCoeff th = 0) (lgE : PowerSeries ℂ_[p])
    (th_log : PowerSeries.subst
      (PowerSeries.map (iC.comp ((algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)))) th)
      (PowerSeries.map (iC.comp (algebraMap (K0 p) Kc)) (logF p)) = lgE) : PowerSeries.constantCoeff lgE = 0 := by
  rw [← th_log]
  exact PowerSeries.constantCoeff_subst_eq_zero (cc_pmap _ th_zero) _ (cc_pmap _ (cc_logF p))

theorem simeq_of {ι : Type} (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (Oc : Subring Kc)
    (witt_mem_integers_Cp : ∀ x : WW p, algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) x) ∈ Oc)
    (iC : Kc →+* ℂ_[p]) (iC_int : ∀ x : Kc, x ∈ Oc ↔ ‖iC x‖ ≤ 1)
    (th : PowerSeries (WW p)) (th_zero : PowerSeries.constantCoeff th = 0) (th_unit : IsUnit (PowerSeries.coeff 1 th))
    (lgE : PowerSeries ℂ_[p])
    (th_log : PowerSeries.subst
      (PowerSeries.map (iC.comp ((algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)))) th)
      (PowerSeries.map (iC.comp (algebraMap (K0 p) Kc)) (logF p)) = lgE)
    (f g : MvPowerSeries ι (K0 p)) (hfg : constantCoeff (f - g) = 0)
    (h : IntegralMv (expMv (subst (diagS lgE) (map (iC.comp (algebraMap (K0 p) Kc)) (f - g))))) :
    FormalGroupSystem.Simeq p f g := by
  have : CharZero Kc := charZero_of_injective_algebraMap (algebraMap (K0 p) Kc).injective
  have hl0 := cc_lgE Kc iC th th_zero lgE th_log
  refine ⟨hfg, ?_⟩
  obtain ⟨U, hU1, hU2⟩ := K1core Kc Oc witt_mem_integers_Cp iC iC_int th th_zero th_unit lgE th_log (f - g) hfg 1 (by
    have h1 : subst (diagS lgE) (1 : MvPowerSeries ι ℂ_[p]) = 1 := by
      rw [← coe_substAlgHom (hs_dg hl0), map_one]
    rw [map_one, h1, one_mul]
    exact h)
  have hU : U = map (algebraMap (K0 p) Kc) (Ex (f - g)) := by
    have h1 : map (algebraMap (K0 p) Kc) (Ex (f - g)) * (map (algebraMap (K0 p) Kc) (expS p (-(f - g))) * U) =
        map (algebraMap (K0 p) Kc) (Ex (f - g)) := by rw [← hU1, mul_one]
    rw [expS_eq_Ex p (by rw [map_neg, hfg, neg_zero]), ← mul_assoc, ← map_mul, mul_comm (Ex (f - g)), Ex_neg_mul hfg,
      map_one, one_mul] at h1
    exact h1
  have e0 : constantCoeff (inParam p (f - g)) = 0 :=
    constantCoeff_subst_eq_zero (hs_dg (cc_logF p)) (cc_dg (cc_logF p)) hfg
  have hP : inParamK p Kc U = map (algebraMap (K0 p) Kc) (expS p (inParam p (f - g))) := by
    rw [expS_eq_Ex p e0, hU]
    show subst (diagS (PowerSeries.map (algebraMap (K0 p) Kc) (logF p))) (map (algebraMap (K0 p) Kc) (Ex (f - g))) =
      map (algebraMap (K0 p) Kc) (Ex (subst (diagS (logF p)) (f - g)))
    rw [← subst_Ex (hs_dg (cc_logF p)) hfg, map_subst (hs_dg (cc_logF p))]
    congr 1
    funext i
    rw [map_dg]
  have hm : ∀ n, ∃ w : WW p, algebraMap (WW p) (K0 p) w = coeff n (expS p (inParam p (f - g))) := fun n =>
    mem_W_of_norm (iC.comp (algebraMap (K0 p) Kc)) (fun x => (iC_int _).mp (witt_mem_integers_Cp x)) _ (by
      have h3 := hU2 n
      rw [hP, coeff_map] at h3
      exact (iC_int _).mp h3)
  choose G hG using hm
  let Gs : MvPowerSeries ι (WW p) := G
  have hGs : map (algebraMap (WW p) (K0 p)) Gs = expS p (inParam p (f - g)) := by
    ext n
    rw [coeff_map]
    exact hG n
  refine ⟨Gs - 1, ?_, ?_⟩
  · have h4 : algebraMap (WW p) (K0 p) (constantCoeff Gs) = 1 := by
      rw [← constantCoeff_map, hGs, expS_eq_Ex p e0, cc_Ex e0]
    rw [map_sub, map_one, sub_eq_zero]
    exact IsFractionRing.injective (WW p) (K0 p) (by rw [h4, map_one])
  · rw [map_sub, map_one, add_sub_cancel, hGs]

end W

end Formalism.MainNotions.J
