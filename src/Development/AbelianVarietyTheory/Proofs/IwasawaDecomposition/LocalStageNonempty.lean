import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_prime_ainf : ∀ (l : ℕ) [Fact l.Prime], ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) := by
  first | exact @GlobalTheory.MemLoc.exists_locPrime_tied | exact GlobalTheory.MemLoc.exists_locPrime_tied | (intros; apply GlobalTheory.MemLoc.exists_locPrime_tied <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Mem

theorem nonempty_locStage : Nonempty GlobalTheory.Mem.LocStage := by
  classical
  have h := GlobalTheory.T.exists_local_prime_ainf
  choose P AI hT using h
  exact ⟨{ loc := fun l _ => P l, locA := fun l _ => AI l, locT := fun l _ => (hT l).some }⟩

end GlobalTheory.Mem
end
