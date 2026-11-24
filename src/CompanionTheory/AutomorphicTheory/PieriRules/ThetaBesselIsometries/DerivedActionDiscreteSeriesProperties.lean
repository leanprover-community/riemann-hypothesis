module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset Filter Topology
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory.DerivedAction

open PI.UpqRep PI.UnitaryGroupMassFormula.CapelliEig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}

theorem exp_mem {X : Mx k r} (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) :=
  _root_.GlobalTheory.DerivedAction.exp_mem hX t

theorem one_mem : (1 : Mx k r) ∈ UH (Hpk k r) :=
  _root_.GlobalTheory.DerivedAction.one_mem

theorem lie_conj {X g : Mx k r} (hX : InLieHpk k r X) (hg : g ∈ UH (Hpk k r)) :
    InLieHpk k r (g⁻¹ * X * g) :=
  _root_.GlobalTheory.DerivedAction.lie_conj hX hg

theorem lie_conj' {X g : Mx k r} (hX : InLieHpk k r X) (hg : g ∈ UH (Hpk k r)) :
    InLieHpk k r (g * X * g⁻¹) :=
  _root_.GlobalTheory.DerivedAction.lie_conj' hX hg

theorem hasDerivAt_local {X g : Mx k r} (hX : InLieHpk k r X) {f F : Mx k r → H} {U : Set (Mx k r)}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUH (Hpk k r) h → f h = F h)
    (hg : g ∈ UH (Hpk k r)) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 :=
  _root_.GlobalTheory.DerivedAction.hasDerivAt_local hX hU hgU hF hfF hg

theorem exists_lin {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    ∃ L : Mx k r →L[ℝ] H, ∀ X, InLieHpk k r X → dsig (k := k) (r := r) σ X v = L X ∧
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig (k := k) (r := r) σ X v) 0 :=
  _root_.GlobalTheory.DerivedAction.exists_lin hv

theorem hasDerivAt_dsig {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig (k := k) (r := r) σ X v) 0 :=
  _root_.GlobalTheory.DerivedAction.hasDerivAt_dsig hX hv

theorem hasDerivAt_apply {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    (T : H →L[ℂ] H) :
    HasDerivAt (fun t : ℝ => T (σ (NormedSpace.exp ((t : ℂ) • X)) v)) (T (dsig (k := k) (r := r) σ X v)) 0 :=
  _root_.GlobalTheory.DerivedAction.hasDerivAt_apply hX hv T

theorem dsig_zero (X : Mx k r) : dsig (k := k) (r := r) σ X (0 : H) = 0 :=
  _root_.GlobalTheory.DerivedAction.dsig_zero X

theorem dsig_add {X : Mx k r} (hX : InLieHpk k r X) {v w : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X (v + w) = dsig (k := k) (r := r) σ X v + dsig (k := k) (r := r) σ X w :=
  _root_.GlobalTheory.DerivedAction.dsig_add hX hv hw

theorem dsig_smul {X : Mx k r} (hX : InLieHpk k r X) (a : ℂ) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X (a • v) = a • dsig (k := k) (r := r) σ X v :=
  _root_.GlobalTheory.DerivedAction.dsig_smul hX a hv

theorem dsig_smooth (hσ : IsDSHpk k r ε mu σ) {X : Mx k r} (hX : InLieHpk k r X) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X v ∈ smoothVecs (k := k) (r := r) σ :=
  _root_.GlobalTheory.DerivedAction.dsig_smooth hσ hX hv

theorem dsig_conj (hσ : IsDSHpk k r ε mu σ) {X g : Mx k r} (hX : InLieHpk k r X) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (hg : g ∈ UH (Hpk k r)) :
    σ g (dsig (k := k) (r := r) σ X v) = dsig (k := k) (r := r) σ (g * X * g⁻¹) (σ g v) :=
  _root_.GlobalTheory.DerivedAction.dsig_conj hσ hX hv hg

theorem dsig_kfin [CompleteSpace H] (hK : PI.KFinSmooth) (hmu : IsHCParam mu) (hσ : IsDSHpk k r ε mu σ)
    {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : IsKFinHpk (k := k) (r := r) σ v) :
    IsKFinHpk (k := k) (r := r) σ (dsig (k := k) (r := r) σ X v) :=
  _root_.GlobalTheory.DerivedAction.dsig_kfin hK hmu hσ hX hv

theorem dsig_skew (hσ : IsDSHpk k r ε mu σ) {X : Mx k r} (hX : InLieHpk k r X) {v w : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    ⟪dsig (k := k) (r := r) σ X v, w⟫_ℂ = -⟪v, dsig (k := k) (r := r) σ X w⟫_ℂ :=
  _root_.GlobalTheory.DerivedAction.dsig_skew hσ hX hv hw

theorem dsig_TK (hK : PI.KFinSmooth) (R : Rep k r) (hR : R.IsDG ε mu) {X : Mx k r} (hX : InLieHpk k r X) :
    ∀ v ∈ R.TK, v ∈ R.sm ∧ dsig (k := k) (r := r) R.σ X v ∈ R.TK :=
  _root_.GlobalTheory.DerivedAction.dsig_TK hK R (GlobalTheory.isDS_of_isDG hR) hX

theorem derived_action : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ X, PI.UpqRep.InLieHpk k r X → (∀ v ∈ R.sm, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.sm ∧ HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) 0) ∧ (∀ v ∈ R.sm, ∀ g ∈ GG k r, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = PI.UpqRep.dsig (k := k) (r := r) R.σ (g * X * g⁻¹) (R.σ g v)) ∧ (∀ v, R.KFin v → R.KFin (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) ∧ (∀ v ∈ R.TK, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.TK) ∧ (∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ X v, w⟫_ℂ = -⟪v, PI.UpqRep.dsig (k := k) (r := r) R.σ X w⟫_ℂ) :=
  fun h1 k r ε mu R h2 =>
    _root_.GlobalTheory.DerivedAction.derived_action h1 k r ε mu R (GlobalTheory.isDS_of_isDG h2)

end GlobalTheory.DerivedAction
