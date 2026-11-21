import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

section
open Formalism Formalism.BasicNotions
namespace GlobalTheory.MemLoc

theorem exists_locTheory_tied : ∃ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)),
    Nonempty (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) := by
  choose P A h using exists_locPrime_tied
  exact ⟨fun l _ => P l, fun l _ => A l, ⟨fun l _ => (h l).some⟩⟩
end GlobalTheory.MemLoc
end

section
open Formalism Formalism.BasicNotions
namespace GlobalTheory.MemLoc

theorem localGap_nonempty : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R),
    Nonempty (Formalism.BasicNotions.Examples₂.LocalGap H) := by
  intro R H
  obtain ⟨L, A, ⟨T⟩⟩ := exists_locTheory_tied
  exact ⟨⟨L, A, T⟩⟩

theorem record_nonempty : Nonempty Formalism.BasicNotions.D7 :=
  Formalism.BasicNotions.Examples₂.record_nonempty_of_localGap (localGap_nonempty _)

end GlobalTheory.MemLoc
end
