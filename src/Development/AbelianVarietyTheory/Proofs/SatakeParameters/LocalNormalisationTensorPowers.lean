import Mathlib
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormPow
import BuildAid.ForwardExisting

section
namespace GlobalTheory

theorem locNormPow_tensorPowers : Formalism.L2.AlgTh.LocNormPow := Formalism.L2.AlgTh.local_norm_power

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalisation_tensorPowers : Formalism.L2.AlgTh.LocNormPow := by
  atlas_forward_decl GlobalTheory.locNormPow_tensorPowers
