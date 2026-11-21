import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem secTw_add_chart : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N),
    (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  intro R _ _ A N σ t t' t'' h j
  show GlobalTheory.FieldBaseChange.pullFn _ _ (t''.f j) =
    GlobalTheory.FieldBaseChange.pullFn _ _ (t.f j) + GlobalTheory.FieldBaseChange.pullFn _ _ (t'.f j)
  rw [h j]
  exact map_add _ _ _

end GlobalTheory.Mum.Conj
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  atlas_forward_decl GlobalTheory.Mum.Conj.secTw_add_chart
