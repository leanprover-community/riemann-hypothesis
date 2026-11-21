import Formalism.LocalToGlobal.CharacterGerms.TripleSubstSecondCoordinate

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

namespace VP

theorem Aterm_eq (Y : FBChart C V O dd) (π : Orb → Fin 2 → Fin dd → PS C 1 dd)
    (hπ0 : ∀ o g i, MvPowerSeries.constantCoeff (π o g i) = 0) (s s' : Orb × Fin 2) :
    Aterm Y π s s' = mvExp ((Y.k : C) • hAt Y (π s.1 s.2) (actAt Y Y.w0 (π s'.1 s'.2))) := by
  unfold Aterm
  rw [eval_two_points_eq_subst _ _ _ rfl, compose_one_action_eq_actAt]
  exact expS_eq _ (cc_smul _ (cc_hAt Y (hπ0 _ _) (cc_actAt Y _ (hπ0 _ _))))


end VP



end Formalism.L2.FormalSeriesBounds
