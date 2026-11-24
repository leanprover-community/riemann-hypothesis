module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexifiedDerivedActionLieHomGramAdjoint

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionBracket, CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjoint, CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjointStatement

-- ===== clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionBracket =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionBracket", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Calculus.FDeriv.Symmetric\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionBracket\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset Filter Topology
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory.DerivedBracket

open PI.UpqRep PI.UnitaryGroupMassFormula.CapelliEig _root_.Gp91.GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fderiv_comm {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {x : E} (hF : ContDiffAt ℝ ∞ F x) (L M : E →L[ℝ] E) {a b c : E}
    (ha : M x = a) (hb : L x = b) (hc : L a - M b = c) :
    fderiv ℝ (fun g => fderiv ℝ F g (L g)) x a - fderiv ℝ (fun g => fderiv ℝ F g (M g)) x b =
      fderiv ℝ F x c :=
  _root_.GlobalTheory.DerivedBracket.fderiv_comm hF L M ha hb hc

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}

theorem lie_bracket {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) :
    InLieHpk k r (X * Y - Y * X) :=
  _root_.GlobalTheory.DerivedBracket.lie_bracket hX hY

theorem dsig_dsig (hσ : IsDSHpk k r ε mu σ) {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) {F : Mx k r → H} {U : Set (Mx k r)}
    (hU : IsOpen U) (h1 : (1 : Mx k r) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, inUH (Hpk k r) h → σ h v = F h) (L : Mx k r →L[ℝ] Mx k r) (hL : ∀ x, L x = x * Y) :
    dsig (k := k) (r := r) σ X (dsig (k := k) (r := r) σ Y v) =
      fderiv ℝ (fun g => fderiv ℝ F g (L g)) 1 X :=
  _root_.GlobalTheory.DerivedBracket.dsig_dsig hσ hX hY hv hU h1 hF hfF L hL

theorem dsig_bracket (hσ : IsDSHpk k r ε mu σ) {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X (dsig (k := k) (r := r) σ Y v) -
      dsig (k := k) (r := r) σ Y (dsig (k := k) (r := r) σ X v) = dsig (k := k) (r := r) σ (X * Y - Y * X) v :=
  _root_.GlobalTheory.DerivedBracket.dsig_bracket hσ hX hY hv

theorem derived_action_bracket : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ X Y, PI.UpqRep.InLieHpk k r X → PI.UpqRep.InLieHpk k r Y → ∀ v ∈ R.sm, PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsig (k := k) (r := r) R.σ Y v) - PI.UpqRep.dsig (k := k) (r := r) R.σ Y (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = PI.UpqRep.dsig (k := k) (r := r) R.σ (X * Y - Y * X) v :=
  fun h1 k r ε mu R h2 =>
    _root_.GlobalTheory.DerivedBracket.derived_action_bracket h1 k r ε mu R (GlobalTheory.isDS_of_isDG h2)

end GlobalTheory.DerivedBracket
end -- clump:auto
end Gp91 -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionBracket =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjoint =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjoint", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionBracket\nimport CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties\nimport Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexifiedDerivedActionLieHomGramAdjoint\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.ComplexifiedAction

open PI.UpqRep _root_.Gp91.GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gram_herm (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r :=
  _root_.GlobalTheory.ComplexifiedAction.gram_herm k r

theorem gram_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 :=
  _root_.GlobalTheory.ComplexifiedAction.gram_sq k r

theorem lie_iff {X : Mx k r} : InLieHpk k r X ↔ Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 :=
  _root_.GlobalTheory.ComplexifiedAction.lie_iff

theorem adj_of_lie {X : Mx k r} (hX : InLieHpk k r X) :
    Formalism.QuantumDeterminants.Hpk k r * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X :=
  _root_.GlobalTheory.ComplexifiedAction.adj_of_lie hX

theorem lie_of_adj {X : Mx k r} (h : Formalism.QuantumDeterminants.Hpk k r * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X) : InLieHpk k r X :=
  _root_.GlobalTheory.ComplexifiedAction.lie_of_adj h

theorem adj_adj (Y : Mx k r) :
    Formalism.QuantumDeterminants.Hpk k r * (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r = Y :=
  _root_.GlobalTheory.ComplexifiedAction.adj_adj Y

theorem lie_re (Y : Mx k r) :
    InLieHpk k r ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) :=
  _root_.GlobalTheory.ComplexifiedAction.lie_re Y

theorem lie_im (Y : Mx k r) :
    InLieHpk k r ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) :=
  _root_.GlobalTheory.ComplexifiedAction.lie_im Y

theorem exists_decomp (Y : Mx k r) : ∃ X₁ X₂, InLieHpk k r X₁ ∧ InLieHpk k r X₂ ∧ Y = X₁ + Complex.I • X₂ :=
  _root_.GlobalTheory.ComplexifiedAction.exists_decomp Y

theorem adj_decomp {X₁ X₂ : Mx k r} (h₁ : InLieHpk k r X₁) (h₂ : InLieHpk k r X₂) :
    Formalism.QuantumDeterminants.Hpk k r * (X₁ + Complex.I • X₂)ᴴ * Formalism.QuantumDeterminants.Hpk k r = -X₁ + Complex.I • X₂ :=
  _root_.GlobalTheory.ComplexifiedAction.adj_decomp h₁ h₂

theorem dC_decomp (R : Rep k r) {X₁ X₂ : Mx k r} (h₁ : InLieHpk k r X₁) (h₂ : InLieHpk k r X₂) (v : R.H) :
    R.dC (X₁ + Complex.I • X₂) v =
      dsig (k := k) (r := r) R.σ X₁ v + Complex.I • dsig (k := k) (r := r) R.σ X₂ v :=
  _root_.GlobalTheory.ComplexifiedAction.dC_decomp R h₁ h₂ v

theorem lie_zero : InLieHpk k r 0 :=
  _root_.GlobalTheory.ComplexifiedAction.lie_zero

theorem lie_add {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) : InLieHpk k r (X + Y) :=
  _root_.GlobalTheory.ComplexifiedAction.lie_add hX hY

theorem lie_smul (a : ℝ) {X : Mx k r} (hX : InLieHpk k r X) : InLieHpk k r (a • X) :=
  _root_.GlobalTheory.ComplexifiedAction.lie_smul a hX

theorem lie_neg {X : Mx k r} (hX : InLieHpk k r X) : InLieHpk k r (-X) :=
  _root_.GlobalTheory.ComplexifiedAction.lie_neg hX

theorem dsig_add_left (R : Rep k r) {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (X + Y) v =
      dsig (k := k) (r := r) R.σ X v + dsig (k := k) (r := r) R.σ Y v :=
  _root_.GlobalTheory.ComplexifiedAction.dsig_add_left R hX hY hv

theorem dsig_smul_left (R : Rep k r) (a : ℝ) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (a • X) v = (a : ℂ) • dsig (k := k) (r := r) R.σ X v :=
  _root_.GlobalTheory.ComplexifiedAction.dsig_smul_left R a hX hv

theorem dsig_neg_left (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (-X) v = -dsig (k := k) (r := r) R.σ X v :=
  _root_.GlobalTheory.ComplexifiedAction.dsig_neg_left R hX hv

theorem dC_lie (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    R.dC X v = dsig (k := k) (r := r) R.σ X v :=
  _root_.GlobalTheory.ComplexifiedAction.dC_lie R hX hv

theorem dC_lin_left (R : Rep k r) (Y Z : Mx k r) (a : ℂ) {v : R.H} (hv : v ∈ R.sm) :
    R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v :=
  _root_.GlobalTheory.ComplexifiedAction.dC_lin_left R Y Z a hv

theorem complexified_action : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → (∀ Y, ∀ v ∈ R.sm, R.dC Y v ∈ R.sm) ∧ (∀ Y (a : ℂ), ∀ v ∈ R.sm, ∀ w ∈ R.sm, R.dC Y (a • v + w) = a • R.dC Y v + R.dC Y w) ∧ (∀ Y Z (a : ℂ), ∀ v ∈ R.sm, R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v) ∧ (∀ X, PI.UpqRep.InLieHpk k r X → ∀ v ∈ R.sm, R.dC X v = PI.UpqRep.dsig (k := k) (r := r) R.σ X v) ∧ (∀ Y Z, ∀ v ∈ R.sm, R.dC Y (R.dC Z v) - R.dC Z (R.dC Y v) = R.dC (Y * Z - Z * Y) v) ∧ ∀ Y, ∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪R.dC Y v, w⟫_ℂ = ⟪v, R.dC ((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r)) w⟫_ℂ :=
  fun h1 k r ε mu R h2 =>
    _root_.GlobalTheory.ComplexifiedAction.complexified_action h1 k r ε mu R (GlobalTheory.isDS_of_isDG h2)

end GlobalTheory.ComplexifiedAction
end -- clump:auto
end Gp91 -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjoint =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjointStatement =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjointStatement", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjoint\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

end Gp91 -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjointStatement =====
