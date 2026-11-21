import Mathlib
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormInter
import BuildAid.ForwardExisting

section
namespace GlobalTheory

theorem locNormInter : Formalism.L2.AlgTh.LocNormInter := Formalism.L2.AlgTh.local_norm_intertwiner

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalisation_intertwiner_prime_index : Formalism.L2.AlgTh.LocNormInter := by
  atlas_forward_decl GlobalTheory.locNormInter
