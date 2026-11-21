import Formalism.HermitianCurvature.StatementX

namespace Formalism.FourierDecayAlt.P

open Matrix

namespace X



theorem two_sum (l : ℕ) : 2 * (∑ a ∈ Finset.range l, a) = l * (l - 1) := by
  rw [mul_comm, Finset.sum_range_id_mul_two]

end X






end Formalism.FourierDecayAlt.P
