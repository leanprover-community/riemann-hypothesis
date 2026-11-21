import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhNormOfUnits
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeOfTwoIdentities
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SimeqPdInt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BiaddZpLin
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormUnits
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormLimit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BeDiagZp

section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def SimeqGroup : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), Simeq f 0 → Simeq g 0 →
    Simeq (f + g) 0 ∧ Simeq (-f) 0

def SimeqZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : MvPowerSeries σ ℂ_[p]), Simeq f 0 →
    ∀ n : ℤ_[p], Simeq (MvPowerSeries.C (zc n) * f) 0

def SimeqSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Fintype σ] [Fintype τ] (f : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (s i) = 0) → (∀ i, IntegralMv (s i)) →
    Simeq f 0 → Simeq (MvPowerSeries.subst s f) 0

def SimeqLimit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : ℕ → MvPowerSeries σ ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]),
    (∀ α, Filter.Tendsto (fun k => MvPowerSeries.coeff α (f k)) Filter.atTop (nhds (MvPowerSeries.coeff α F))) →
    (∀ k, Simeq (f k) 0) → Simeq F 0

def SimeqPd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) [DecidableEq σ] (f : MvPowerSeries σ ℂ_[p]), Simeq f 0 →
    ∀ k : σ, IntegralMv (pd k f)

def BiaddZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    ∀ n : ℤ_[p], Simeq (g.be (g.mulBy (zc n) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (zc n) * g.be (Xv 0) (Xv 1))

end Formalism.MainNotions.Ext.CutA
end

section
namespace Formalism.MainNotions.Ext.CutA



theorem phNormOfUnits_holds : PhNormOfUnits := by
  intro p _ g S hok
  exact phase_norm_units p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

theorem phNormClosed_holds : PhNormClosed := by
  intro p _ g S hok
  exact phase_norm_limit_target p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

theorem beDiagG_holds : BeDiagG :=
  fun p _ g S hOk => diagonal_zp_identity p g.l g.ex g.ph S hOk.2.2.1 hOk.2.2.2

end Formalism.MainNotions.Ext.CutA
end
