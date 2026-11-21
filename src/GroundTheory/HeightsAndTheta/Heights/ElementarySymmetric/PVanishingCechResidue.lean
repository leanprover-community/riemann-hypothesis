import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauIIsBasisOf
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.ResidueChartModel
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqCech

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

def VanishingCechResidue.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a : ℕ), 3 ≤ a → ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ b : ℕ, b < a → ∃ c₀ : ℕ, ∀ c, c₀ ≤ c → ∀ (q : ℕ) (φ : Finset (Fin (r + 1)) → P.Fn),
      P.IsCocycle a (b + a * c) (q + 1) x φ → P.IsCoboundary a (b + a * c) q x φ

end

end GroundTheory.Heights₂.Heights.KeyFormula
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

def ResidueFiniteModel.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a : ℕ), 3 ≤ a → ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ b : ℕ, b < a → Nonempty (ResidueChartModel P a b x)



end

end GroundTheory.Heights₂.Heights.KeyFormula
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman (Poly GradedMod gradedH gradedSys cechC cechZ)

noncomputable section

open RigSymForm

def ResidueChartTransport.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a b r : ℕ) (x : Fin (r + 1) → P.Fn) (𝓜 : ResidueChartModel P a b x) (c₀ : ℤ),
    (∀ i : ℕ, 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton (gradedH ℂ r 𝓜.M 𝓜.G i c)) →
    ∀ c : ℕ, c₀ ≤ c → ∀ (q : ℕ) (φ : Finset (Fin (r + 1)) → P.Fn),
      P.IsCocycle a (b + a * c) (q + 1) x φ → P.IsCoboundary a (b + a * c) q x φ

end

end GroundTheory.Heights₂.Heights.KeyFormula
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

theorem serreVanishing_graded_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof).1
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.full.{0, 0}

theorem VanishingCechResidue.proof (hM : ResidueFiniteModel.Statement)
    (hT : ResidueChartTransport.Statement) : VanishingCechResidue.Statement := by
  intro P a ha r x hx b hb
  obtain ⟨𝓜⟩ := hM P a ha r x hx b hb
  obtain ⟨c₀, hc₀⟩ := serreVanishing_graded_holds ℂ r 𝓜.M 𝓜.G 𝓜.finite
  refine ⟨c₀.toNat, fun c hc q φ hφ => hT P a b r x 𝓜 c₀ hc₀ c ?_ q φ hφ⟩
  have := Int.self_le_toNat c₀
  omega

end

end GroundTheory.Heights₂.Heights.KeyFormula
end
