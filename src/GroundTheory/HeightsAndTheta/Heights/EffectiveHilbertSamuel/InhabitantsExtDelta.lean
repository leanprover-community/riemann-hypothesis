import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Inhabitants
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtDelta
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtCompact
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtNonInt
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.ObjectsExtDelta

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace ExtInhabitants

def c0 : Fin (flatAtlas 1).n := ⟨0, Nat.one_pos⟩






def exZdz : Fin (flatAtlas 1).n → (Fin 1 → ℂ) → ℂ := fun _ y => y 0

end ExtInhabitants

open ExtInhabitants




end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def ExtTwist.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (j : ℕ), 1 ≤ D → 2 ≤ j →
    ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      (∀ k, X.A.SmoothOn (X.A.chart k).source (fun y => extPsi Z j δ k y + extPhi Z ε k y)) ∧
      (∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extPhi Z ε k ∘ (X.A.chart k).symm)
        (X.A.chart k).target) ∧
      (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source,
        extPsi Z j δ k x = extPsi Z j δ l x + Real.log (‖X.L₂.g k l x * X.L.g k l x ^ (D + j)‖ ^ 2) ∧
          extPhi Z ε k x = extPhi Z ε l x) ∧
      (∀ k, ∀ y ∈ (X.A.chart k).target, ∀ ξ : Fin D → ℂ,
        extTheta ε (extEv Z k ((X.A.chart k).symm y)) * extOmega Z ε k y ξ ≤
          levi ((fun x => extPsi Z j δ k x + extPhi Z ε k x) ∘ (X.A.chart k).symm) y ξ) ∧
      (∀ k, ∀ y ∈ (X.A.chart k).target, ∀ ξ : Fin D → ℂ,
        ‖dbarPair (fun z => (extPhi Z ε k ((X.A.chart k).symm z) : ℂ)) y ξ‖ ^ 2 =
          (curvK (extX ε (extEv Z k ((X.A.chart k).symm y))) /
            curvEta (extX ε (extEv Z k ((X.A.chart k).symm y)))) ^ 2 * extOmega Z ε k y ξ)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def ExtShell.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (m : ℕ), 1 ≤ D →
    ∀ (g : X.U → ℂ) (W : Set X.U) (gt : Fin X.A.n → X.U → ℂ), IsOpen W → Z.S ⊆ W →
      (∀ k, ContinuousOn (gt k ∘ (X.A.chart k).symm)
        ((X.A.chart k).target ∩ (X.A.chart k).symm ⁻¹' W)) →
      (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source ∩ W,
        gt k x = jac X.A k l x * X.L₂.g k l x * X.L.g k l x ^ (D + m) * gt l x) →
      (∀ x ∈ Z.S, gt (chartIdx X.A x) x = g x * sJac X.A Z.s (chartIdx X.A x) x) →
      Tendsto (fun ε : ℝ => chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * ‖gt k y‖ ^ 2 *
          Real.exp (-X.wt (D + m) k y) * (extEv Z k y ^ D)⁻¹ * extShell ε (extEv Z k y))))
        (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (Real.log 2 / 2 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt m) g)))

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def ExtCutoff.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (j : ℕ), 1 ≤ D → 2 ≤ j →
    ∀ (g : X.U → ℂ) (θ : ℝ), 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ (F₀ : Fin X.A.n → X.U → ℂ) (G : Fin X.A.n → X.U → ℝ),
        (∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F₀ k ∘ (X.A.chart k).symm)
          (X.A.chart k).target) ∧
        (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source,
          F₀ k x = jac X.A k l x * X.L₂.g k l x * X.L.g k l x ^ (D + j) * F₀ l x) ∧
        (∀ k, ∀ x ∉ (X.A.chart k).source, F₀ k x = 0) ∧
        (∀ x ∈ Z.S, res X.A Z.s F₀ x = g x) ∧
        topNormSq X.A (X.wt (D + j)) F₀ ≤ ENNReal.ofReal θ ∧
        (∀ k, ContinuousOn (G k ∘ (X.A.chart k).symm) (X.A.chart k).target) ∧
        (∀ k y, 0 ≤ G k y) ∧
        (∀ k, ∀ y ∈ (X.A.chart k).target, ∀ ξ : Fin D → ℂ,
          ‖dbarPair (F₀ k ∘ (X.A.chart k).symm) y ξ‖ ^ 2 ≤
            9 * extShell ε (extEv Z k ((X.A.chart k).symm y)) * G k ((X.A.chart k).symm y) *
              ‖dbarPair (fun z => (extEv Z k ((X.A.chart k).symm z) : ℂ)) y ξ‖ ^ 2 / ε ^ 4) ∧
        72 * chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * G k y *
            Real.exp (-X.wt (D + j) k y) * (extEv Z k y ^ D)⁻¹ * extShell ε (extEv Z k y))) ≤
          ENNReal.ofReal (36 * Real.log 2 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g + θ)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def BergmanProj.Statement : Prop :=
  ∀ (D : ℕ) (U : Type) [TopologicalSpace U] [T2Space U] (A : FinHolAtlas D U)
    (L₂ L : HolLineBundle A) (m : ℕ) (ψ : Fin A.n → U → ℝ) (F₀ : Fin A.n → U → ℂ),
    (∀ k, ContinuousOn (ψ k ∘ (A.chart k).symm) (A.chart k).target) →
    (∀ k l, ∀ x ∈ (A.chart k).source ∩ (A.chart l).source,
      ψ k x = ψ l x + Real.log (‖L₂.g k l x * L.g k l x ^ m‖ ^ 2)) →
    (∀ k, ContinuousOn (F₀ k ∘ (A.chart k).symm) (A.chart k).target) →
    (∀ k l, ∀ x ∈ (A.chart k).source ∩ (A.chart l).source,
      F₀ k x = jac A k l x * L₂.g k l x * L.g k l x ^ m * F₀ l x) →
    topNormSq A ψ F₀ < ⊤ →
    ∃ F ∈ topSections A L₂ L m, topNormSq A ψ F < ⊤ ∧
      ∀ G ∈ topSections A L₂ L m, topNormSq A ψ G < ⊤ → chartInner A ψ (F₀ - F) G = 0

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

open ExtInhabitants




end

end GroundTheory.Heights₂.Heights.EffectiveHS
end
