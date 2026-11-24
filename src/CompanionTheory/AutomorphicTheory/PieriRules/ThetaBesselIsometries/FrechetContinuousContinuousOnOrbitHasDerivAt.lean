module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.AnaHpartUnique
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesPropertiesStatement
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CWDeriv

open Filter Topology PI.UpqRep
open scoped ContDiff

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothOnH_continuousOn {H : Matrix (Fin n) (Fin n) ℂ} {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) : ContinuousOn f (Formalism.QuantumDeterminants.UH H) :=
  _root_.GlobalTheory.CWDeriv.smoothOnH_continuousOn hf

theorem left_hasDerivAt {H : Matrix (Fin n) (Fin n) ℂ} (hH : AAInvW.HInvol H)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g X : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hg : g ∈ U) (hgH : inUH H g) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, inUH H x → f x = F x) (hX : AAInvW.inLH H X) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (fderiv ℝ F g (X * g)) 0 :=
  _root_.GlobalTheory.CWDeriv.left_hasDerivAt hH hU hg hgH hF hfF hX

theorem left_smooth {H : Matrix (Fin n) (Fin n) ℂ} (hH : AAInvW.HInvol H)
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} {X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hX : AAInvW.inLH H X)
    (hf' : ∀ g, inUH H g → ∀ D, HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) D 0 → D = f' g) :
    SmoothOnH H f' ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (f' g) 0 :=
  _root_.GlobalTheory.CWDeriv.left_smooth hH hf hX hf'

end Smooth

section Rep

variable {k r : ℕ}

def DerFacts (R : Rep k r) : Prop :=
  ∀ X, InLieHpk k r X →
    (∀ v ∈ R.sm, dsig (k := k) (r := r) R.σ X v ∈ R.sm ∧
      HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig (k := k) (r := r) R.σ X v) 0) ∧
    ∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪dsig (k := k) (r := r) R.σ X v, w⟫_ℂ = -⟪v, dsig (k := k) (r := r) R.σ X w⟫_ℂ

theorem hInvol (k r : ℕ) : AAInvW.HInvol (Hpk k r) :=
  _root_.GlobalTheory.CWDeriv.hInvol k r

theorem dsigW_mem {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X) :
    ∀ u ∈ R.sm, dsigW (k := k) (r := r) R.σ W u ∈ R.sm :=
  _root_.GlobalTheory.CWDeriv.dsigW_mem hD W hW

theorem dsigW_append {R : Rep k r} (W : List (Mx k r)) (Y : Mx k r) (u : R.H) :
    dsigW (k := k) (r := r) R.σ (W ++ [Y]) u =
      dsigW (k := k) (r := r) R.σ W (dsig (k := k) (r := r) R.σ Y u) :=
  _root_.GlobalTheory.CWDeriv.dsigW_append W Y u

theorem dsigW_adjoint {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X) :
    ∀ w ∈ R.sm, ∃ w' : R.H, ∀ u ∈ R.sm, ⟪w, dsigW (k := k) (r := r) R.σ W u⟫_ℂ = ⟪w', u⟫_ℂ :=
  _root_.GlobalTheory.CWDeriv.dsigW_adjoint hD W hW

theorem eq_zero_of_closure {R : Rep k r} {x : R.H} (hx : x ∈ closure R.sm) (h : ∀ w ∈ R.sm, ⟪w, x⟫_ℂ = 0) :
    x = 0 :=
  _root_.GlobalTheory.CWDeriv.eq_zero_of_closure hx h

theorem sm_comb {R : Rep k r} (a : ℂ) {x y z : R.H} (hx : x ∈ R.sm) (hy : y ∈ R.sm) (hz : z ∈ R.sm) :
    a • (x - y) - z ∈ R.sm :=
  _root_.GlobalTheory.CWDeriv.sm_comb a hx hy hz

theorem dsigW_comb {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (a : ℂ) {x y z : R.H} (hx : x ∈ R.sm) (hy : y ∈ R.sm) (hz : z ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • (x - y) - z) =
      a • (dsigW (k := k) (r := r) R.σ W x - dsigW (k := k) (r := r) R.σ W y) - dsigW (k := k) (r := r) R.σ W z :=
  _root_.GlobalTheory.CWDeriv.dsigW_comb hD W hW a hx hy hz

theorem dsigW_deriv_eq {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    {c : ℝ → R.H} {c' D : R.H} (hc : ∀ t, c t ∈ R.sm) (hc' : c' ∈ R.sm) (hd : HasDerivAt c c' 0)
    (hD' : HasDerivAt (fun t => dsigW (k := k) (r := r) R.σ W (c t)) D 0) :
    D = dsigW (k := k) (r := r) R.σ W c' :=
  _root_.GlobalTheory.CWDeriv.dsigW_deriv_eq hD W hW hc hc' hd hD'

theorem dsigW_orbit {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDG ε mu) (hD : DerFacts R) {v : R.H} (hv : v ∈ R.sm) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X)
    (hs : SmoothOnH (Hpk k r) (fun g => dsigW (k := k) (r := r) R.σ W (R.σ g v)))
    (Y : Mx k r) (hY : InLieHpk k r Y) :
    SmoothOnH (Hpk k r)
        (fun g => dsigW (k := k) (r := r) R.σ W (dsig (k := k) (r := r) R.σ Y (R.σ g v))) ∧
      ∀ g, inUH (Hpk k r) g → HasDerivAt
        (fun t : ℝ => dsigW (k := k) (r := r) R.σ W (R.σ (NormedSpace.exp ((t : ℂ) • Y) * g) v))
        (dsigW (k := k) (r := r) R.σ W (dsig (k := k) (r := r) R.σ Y (R.σ g v))) 0 :=
  _root_.GlobalTheory.CWDeriv.dsigW_orbit (GlobalTheory.isDS_of_isDG hR) hD hv W hW hs Y hY

theorem dsigW_orbit_smooth {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDG ε mu) (hD : DerFacts R) {v : R.H} (hv : v ∈ R.sm) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) :
    SmoothOnH (Hpk k r) (fun g => dsigW (k := k) (r := r) R.σ W (R.σ g v)) :=
  _root_.GlobalTheory.CWDeriv.dsigW_orbit_smooth (GlobalTheory.isDS_of_isDG hR) hD hv W hW

theorem cw_tendsto {R : Rep k r} {V : Type} [NormedAddCommGroup V] {Bm : R.H → V}
    (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm) {α : Type} {l : Filter α} {u : α → R.H}
    (hu : ∀ᶠ a in l, u a ∈ R.sm)
    (h : ∀ W : List (Mx k r), (∀ X ∈ W, InLieHpk k r X) →
      Tendsto (fun a => dsigW (k := k) (r := r) R.σ W (u a)) l (𝓝 0)) :
    Tendsto (fun a => Bm (u a)) l (𝓝 0) :=
  _root_.GlobalTheory.CWDeriv.cw_tendsto hB hu h

theorem lin_comb {R : Rep k r} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Bm : R.H → V}
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v)
    (a : ℂ) {x y z : R.H} (hx : x ∈ R.sm) (hy : y ∈ R.sm) (hz : z ∈ R.sm) :
    Bm (a • (x - y) - z) = a • (Bm x - Bm y) - Bm z :=
  _root_.GlobalTheory.CWDeriv.lin_comb ha hs a hx hy hz

end Rep

end GlobalTheory.CWDeriv

namespace GlobalTheory

open Filter Topology CWDeriv

theorem cwCont_continuousOn_hasDerivAt : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ v ∈ R.sm, ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → HasDerivAt (fun t : ℝ => Bm (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) (Bm (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) 0 :=
  fun h1 k r ε mu R h2 =>
    _root_.GlobalTheory.cwCont_continuousOn_hasDerivAt h1 k r ε mu R (GlobalTheory.isDS_of_isDG h2)

end GlobalTheory

end
