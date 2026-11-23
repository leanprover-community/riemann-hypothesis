module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionBracket
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.StatementKT
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

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
