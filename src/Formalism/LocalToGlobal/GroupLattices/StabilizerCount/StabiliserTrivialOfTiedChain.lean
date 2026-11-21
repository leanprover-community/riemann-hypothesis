import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.G.StabilizerCardinality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Stab0Used (D : D7) : Prop :=
  (∀ u c, Nat.card ((D.mem u).C.stab 0 c) = 1) ∧
    ∀ u μ, DV.Used D μ → ∀ c, Nat.card ((D.chTw u μ).stab 0 c) = 1

def TwStab0Tie (D : D7) : Prop :=
  ∀ u μ, DV.Used D μ → μ ≠ D.what₂.mu0 → ∃ e : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0,
    ∀ c, Nonempty ((D.mem u).C.stab 0 c ≃* (D.chTw u μ).stab 0 (e c))

theorem card_stab0_mem (D : D7) (lev : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    Nat.card ((D.mem u).C.stab 0 c) = 1 := by
  have := Formalism.L2.G.Triv.stabZero_rec D lev u c
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩









end Formalism.L2.G.StabilizerCardinality

end
