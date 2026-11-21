import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.SameFormAllLevels

section
noncomputable section

namespace PI.Dv.GLatHermW

open Matrix
open scoped ComplexOrder




end PI.Dv.GLatHermW
end
end

section
noncomputable section

namespace PI.Dv.GLatHermW

open PI.Dv

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

def cf (T : GoodSet K G) (g : G) : K :=
  ∑ s, ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s g⁻¹)

theorem eG_eq (T : GoodSet K G) : eG T = ∑ g : G, cf T g • MonoidAlgebra.of K G g := by
  unfold eG eS cf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_smul]



end PI.Dv.GLatHermW
end
end

section
noncomputable section

namespace PI.Dv.GLatHermW

open PI.Dv Formalism.BasicNotions

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]










end PI.Dv.GLatHermW
end
end
