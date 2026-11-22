module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

@[expose] public section

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

theorem ordCompl_q : ordCompl[H.q] H.condN = H.QS * H.d := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  rw [condN_eq_q]
  apply ordCompl_mul_prime hq
  have hqd : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).mpr (by omega)
  exact Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right H.q H.d) H.QS_coprime) hqd

variable {H}

end HostRaw

namespace HostAx

variable {φ : Frame} (H : HostAx φ)

end HostAx

end Formalism.HC

end
