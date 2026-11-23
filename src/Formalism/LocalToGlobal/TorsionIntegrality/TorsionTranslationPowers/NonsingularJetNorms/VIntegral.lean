module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementV
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.LubinTateLogIsArtinHasse
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Taylor0ConstMul
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace VAux

section An

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

theorem phCurve_eq :
    Formalism.L2.Th1.D.phCurve (ι L.g₂) (ι L.g₃) (ι (Formalism.L2.Th1.F.s2 L)) = phL l L ι := by
  unfold Formalism.L2.Th1.D.phCurve phL
  rw [← wpBridge l L ι]
  rfl

theorem subst_lgF_eq (ε : ℂ_[l]) (f : ℂ → ℂ) :
    (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 f)).subst
        (C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[l] l) =
      (inU l L ι f).subst (Formalism.L2.Th1.D.thetaS l (ι L.g₂) (ι L.g₃) ε) := by
  have hp : l.Prime := Fact.out
  have hθ0 := Formalism.L2.Th1.D.EAux.cc_theta hp.two_le (ι L.g₂) (ι L.g₃) ε
  have hlog := Formalism.L2.Th1.D.EAux.log_theta hp.two_le (ι L.g₂) (ι L.g₃) ε
  rw [← hlog]
  exact Formalism.L2.Th1.D.Pair.ps_comp (τ := Unit) hθ0 (Tor.cc_log l L ι) _

end An

theorem intS_subst {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {θ U : K⟦X⟧}
    (hθ0 : constantCoeff θ = 0) (hθ : IntS θ) (hU : IntS U) : IntS (U.subst θ) := by
  have hR := (intRules K).2.2.2.2.2.2.2.2.2
  have h := (substExpInt K Unit Unit (fun _ => θ) (fun _ => hθ0) (fun _ => (hR θ).1 hθ) 0 U
    (by simp) ((hR U).1 hU)).2.1
  exact (hR _).2 h

end VAux

open VAux

theorem v_integral_nonsingular_jet_norms : VIntegral := by
  intro l _ L ι hl2 hW ε hε hθ ω₀ hω hω2 s N hN hlN hNs
  have hp : l.Prime := Fact.out
  have hθ0 := Formalism.L2.Th1.D.EAux.cc_theta hp.two_le (ι L.g₂) (ι L.g₃) ε
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hθ0
  obtain ⟨hc, hI⟩ := Formalism.L2.Th1.D.phCompare ℂ_[l] l hp (ι L.g₂) (ι L.g₃) (ι (Formalism.L2.Th1.F.s2 L)) ε hε hθ
  rw [phCurve_eq] at hc hI
  have hcc : MvPowerSeries.constantCoeff
      (PowerSeries.subst (Formalism.L2.Th1.D.thetaS l (ι L.g₂) (ι L.g₃) ε) (phL l L ι) :
        MvPowerSeries Unit ℂ_[l]) = 0 :=
    Formalism.L2.Th1.D.Pair.cc_ps hθ0 (Tor.cc_phL l L ι)
  have e2 : Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.D.phFF l (ι L.g₂) (ι L.g₃) (ι (Formalism.L2.Th1.F.s2 L)) ε) =
      Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.D.phFF l (ι L.g₂) (ι L.g₃) (ι (Formalism.L2.Th1.F.s2 L)) ε -
        PowerSeries.subst (Formalism.L2.Th1.D.thetaS l (ι L.g₂) (ι L.g₃) ε) (phL l L ι)) *
      Formalism.L2.Th1.B.fExp
        (PowerSeries.subst (Formalism.L2.Th1.D.thetaS l (ι L.g₂) (ι L.g₃) ε) (phL l L ι)) := by
    rw [← Formalism.L2.Th1.B.fExp_add hc hcc, sub_add_cancel]
  have e3 : Formalism.L2.Th1.B.fExp
        (PowerSeries.subst (Formalism.L2.Th1.D.thetaS l (ι L.g₂) (ι L.g₃) ε) (phL l L ι)) =
      PowerSeries.subst (Formalism.L2.Th1.D.thetaS l (ι L.g₂) (ι L.g₃) ε)
        (Formalism.L2.Th1.B.fExp (phL l L ι)) :=
    Formalism.L2.Th1.D.Pair.ps_comp (τ := Unit) hθ0 (Tor.cc_phL l L ι) _
  rw [subst_lgF_eq, e2, e3, mul_assoc, ← PowerSeries.subst_mul hs]
  have hR := intRules ℂ_[l]
  refine hR.2.2.2.2.1 _ _ ((hR.2.2.2.2.2.2.2.2.2 _).2 hI) (intS_subst hθ0 hθ ?_)
  exact ((th0Analytic l L ι hl2 hW ω₀ hω hω2).2 s N hN hlN hNs).1

end Formalism.L2.Th1.E
