module

public import Formalism.LocalToGlobal.CharacterGerms.FirstPartialLawAtPoints

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

variable (Y : FBChart C V O dd)

theorem addOf_eq' {n : ℕ} (a b : Pt C n dd) : addOf Y.B.G.F a b = addAt Y a b := by
  unfold addAt
  unfold addOf
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; unfold P2; rfl)
  | (congr 1; funext q; unfold P2; obtain ⟨j, k⟩ := q; fin_cases j <;> simp)

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Formalism.L2.FormalSeriesBounds
