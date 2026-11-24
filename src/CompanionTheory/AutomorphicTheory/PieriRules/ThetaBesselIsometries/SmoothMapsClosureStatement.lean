module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesPropertiesStatement
import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosure, CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosureStatement

-- ===== clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosure =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosure", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesPropertiesStatement\nimport Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SmMapAct

open PI.UpqRep

variable {k r : ℕ}

def SemiBd (R : Rep k r) (f : R.H → ℝ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), 0 ≤ C ∧ (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ R.sm, f v ≤ C * (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum

theorem sum_norm_nonneg (R : Rep k r) (Ws : List (List (Mx k r))) (v : R.H) :
    0 ≤ (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum :=
  _root_.GlobalTheory.SmMapAct.sum_norm_nonneg R Ws v

theorem semiBd_of_cw {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp}
    (h : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B) : SemiBd R (fun v => ‖B v‖) :=
  _root_.GlobalTheory.SmMapAct.semiBd_of_cw R h

theorem cw_of_semiBd {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp} {f : R.H → ℝ}
    (h : SemiBd R f) (hle : ∀ v ∈ R.sm, ‖B v‖ ≤ f v) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B :=
  _root_.GlobalTheory.SmMapAct.cw_of_semiBd R h hle

theorem SemiBd.add {R : Rep k r} {f g : R.H → ℝ} (hf : SemiBd R f) (hg : SemiBd R g) :
    SemiBd R (fun v => f v + g v) :=
  _root_.GlobalTheory.SmMapAct.SemiBd.add hf hg

theorem SemiBd.mul {R : Rep k r} {f : R.H → ℝ} (hf : SemiBd R f) {a : ℝ} (ha : 0 ≤ a) :
    SemiBd R (fun v => a * f v) :=
  _root_.GlobalTheory.SmMapAct.SemiBd.mul hf ha

theorem semiBd_sum {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) (Ws : List (List (Mx k r)))
    (hWs : ∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) :
    SemiBd R (fun v => (Ws.map fun w => ‖dsigW (k := k) (r := r) R'.σ w (T v)‖).sum) :=
  _root_.GlobalTheory.SmMapAct.semiBd_sum hT Ws hWs

theorem cw_comp {Wp : Type} [NormedAddCommGroup Wp] {R R' : Rep k r} {T : R.H → R'.H} {Bm : R'.H → Wp}
    (hT : SmMap R R' T) (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) :=
  _root_.GlobalTheory.SmMapAct.cw_comp hT hB

theorem smMap_comp {R R' R'' : Rep k r} {T : R.H → R'.H} {T' : R'.H → R''.H}
    (hT : SmMap R R' T) (hT' : SmMap R' R'' T') : SmMap R R'' (fun v => T' (T v)) :=
  _root_.GlobalTheory.SmMapAct.smMap_comp hT hT'

section DS

variable {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}

theorem dsigW_mem (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W v ∈ R.sm :=
  _root_.GlobalTheory.SmMapAct.dsigW_mem hK (GlobalTheory.isDS_of_isDG hR) W hW hv

theorem dsig_lin (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {X : Mx k r} (hX : InLieHpk k r X) (a : ℂ)
    {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X (a • v + w) =
      a • dsig (k := k) (r := r) R.σ X v + dsig (k := k) (r := r) R.σ X w :=
  _root_.GlobalTheory.SmMapAct.dsig_lin hK (GlobalTheory.isDS_of_isDG hR) hX a hv hw

theorem dsigW_lin (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) (a : ℂ) {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • v + w) =
      a • dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w :=
  _root_.GlobalTheory.SmMapAct.dsigW_lin hK (GlobalTheory.isDS_of_isDG hR) W hW a hv hw

theorem inLie_conj {g X : Mx k r} (hg : g ∈ GG k r) (hX : InLieHpk k r X) : InLieHpk k r (g⁻¹ * X * g) :=
  _root_.GlobalTheory.SmMapAct.inLie_conj hg hX

theorem norm_sigma (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) (v : R.H) : ‖R.σ g v‖ = ‖v‖ :=
  _root_.GlobalTheory.SmMapAct.norm_sigma (GlobalTheory.isDS_of_isDG hR) hg v

theorem dsigW_sigma (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (R.σ g v) =
      R.σ g (dsigW (k := k) (r := r) R.σ (W.map fun X => g⁻¹ * X * g) v) :=
  _root_.GlobalTheory.SmMapAct.dsigW_sigma hK (GlobalTheory.isDS_of_isDG hR) hg W hW hv

theorem smMap_sigma (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) :
    SmMap R R (fun v => R.σ g v) :=
  _root_.GlobalTheory.SmMapAct.smMap_sigma hK (GlobalTheory.isDS_of_isDG hR) hg

theorem smMap_lin (hK : PI.KFinSmooth) {R₀ : Rep k r} (hR : R.IsDG ε mu) {T T' : R₀.H → R.H} (a : ℂ)
    (hT : SmMap R₀ R T) (hT' : SmMap R₀ R T') : SmMap R₀ R (fun v => a • T v + T' v) :=
  _root_.GlobalTheory.SmMapAct.smMap_lin hK (GlobalTheory.isDS_of_isDG hR) a hT hT'

end DS

theorem smMap_act : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → R''.IsDG ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) :=
  fun h1 k r ε mu mu' mu'' R R' R'' h2 h3 h4 =>
    _root_.GlobalTheory.SmMapAct.smMap_act h1 k r ε mu mu' mu'' R R' R'' (GlobalTheory.isDS_of_isDG h2) (GlobalTheory.isDS_of_isDG h3) (GlobalTheory.isDS_of_isDG h4)

end GlobalTheory.SmMapAct
end Gp91 -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosure =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosureStatement =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosureStatement", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosure\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.smooth_maps_closure : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → R''.IsDG ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  first | exact @GlobalTheory.SmMapAct.smMap_act
end Gp91 -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosureStatement =====
