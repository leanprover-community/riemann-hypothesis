import Formalism.SharpRestriction.CuspSpanNormBounds.LocSplitType
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Cyc

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def IsCycT (h : V →ₗ⋆[E] V →ₗ[E] E) (T : ℕ) (L : Submodule (𝓞 E) V) : Prop :=
  Submodule.IsLattice E L ∧ IsIntegralLat h L ∧
    ∃ w₁ ∈ dual h L, (∀ w ∈ dual h L, ∃ a : 𝓞 E, w + a • w₁ ∈ L) ∧
      ∀ a : 𝓞 E, a • w₁ ∈ L ↔ ((T : ℕ) : 𝓞 E) ∣ a

theorem cyc_star_int (o : 𝓞 E) : star (algebraMap (𝓞 E) E o) ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E o)) :=
    (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩



end Cyc

def CycGenus : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (T : ℕ), T.Prime → 3 ≤ T → Formalism.MainNotions.S.SplitsCompl E T →
    ∀ L M : Submodule (𝓞 E) S.V, IsCycT S.hT T L → IsCycT S.hT T M → M ∈ genus S.hT L

def CycSplitAt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (T : ℕ), T.Prime → 3 ≤ T → Formalism.MainNotions.S.SplitsCompl E T →
    ∀ L : Submodule (𝓞 E) S.V, IsCycT S.hT T L →
    ∀ p : Ideal (𝓞 E), p.IsMaximal → ((T : ℕ) : 𝓞 E) ∈ p → conjIdeal (K := E) p ≠ p ∧ LocTypeAt S.hT p L


section Rows

open Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar




end Rows

end Formalism.MainNotions.BridgeRowsGenus

end
