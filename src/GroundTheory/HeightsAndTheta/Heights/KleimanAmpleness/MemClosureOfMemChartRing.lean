import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ObjectsAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def StepEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω), IsGraphGen Q n s →
    ∀ (d : ℕ) (r : ℚ) (a : ℕ) (mm : ℤ) (c₁ : ℕ) (σ : Ω),
      (∃ T : Kleiman.StepData k x, T.M = Q ∧ T.d + 1 = d ∧ T.t - T.s' = r ∧ T.p = a ∧ T.m = mm ∧
          T.c₁ = c₁ ∧ T.si = σ) ↔
        (1 ≤ d ∧ IndefiniteRowSideFullHecke.Kleiman2.IsStepData k (graphVec x s) baseBlock d (graphDeg n) r a mm c₁ σ)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def ZeroIdealEq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (D : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω), (∃ i, x i ≠ 0) → IsGraphGen D n s →
    ∀ σ : Ω, Kleiman.zeroIdeal D.toSubSystem σ =
      (IndefiniteRowSideFullHecke.Kleiman2.divIdeal S (graphVec x s) (graphDeg n) σ).comap
        (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ k, graphIdx N m k))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Points

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}

theorem chartRingOver_oneBlock (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) (hi : x (c ()) ≠ 0) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c = Kleiman.chartRing S x (Kleiman.singleChart hi) := by
  rw [← TranslateEq.chartRing.equiv S x hi]
  unfold chartRingOver ReciprocityTheory.ChartRestriction.G.Geo.chartRing
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

end Points

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
