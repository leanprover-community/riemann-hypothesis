import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatMvPowerSeries
import BuildAid.ForwardExisting

section
open IsLocalRing TensorProduct

namespace GlobalTheory.FiniteHeight

theorem flat_mvPowerSeries_of_isNoetherianRing :
    ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type),
      Module.Flat T (MvPowerSeries σ T) :=
  GlobalTheory.PowerSeriesFlat.flat_mvPowerSeries

end GlobalTheory.FiniteHeight
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_flat_mvPowerSeries_of_isNoetherianRing : ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type), Module.Flat T (MvPowerSeries σ T) := by
  atlas_forward_decl GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing
