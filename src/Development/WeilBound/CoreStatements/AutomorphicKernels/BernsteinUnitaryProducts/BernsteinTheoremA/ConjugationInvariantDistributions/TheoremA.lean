import Mathlib
import GroundTheory.AutomorphicForms.WhittakerCriterion
import GroundTheory.AutomorphicForms.ContragredientTranspose.GelfandKazhdan
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker GlobalTheory.BZMir

namespace PositivityTheory.PfBern.ThmA

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def ConjInvariant (H : Subgroup G) (D : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ)) : Prop :=
  ∀ h ∈ H, ∀ f : locallyConstantCompactSupport G ℂ ℂ, D (biTranslL h h f) = D f

theorem ConjInvariant.mono {H K : Subgroup G} (hHK : H ≤ K)
    {D : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ)} (hD : ConjInvariant K D) :
    ConjInvariant H D :=
  fun h hh f => hD h (hHK hh) f

def deltaOne : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ) :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : G => ℂ) (1 : G)).comp (locallyConstantCompactSupport G ℂ ℂ).subtype


def BernsteinTheoremA : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (D : Module.Dual ℂ (locallyConstantCompactSupport (GL (Fin (n + 1)) k) ℂ ℂ)),
    ConjInvariant (Mir k n) D → ConjInvariant ⊤ D

def BernsteinTheoremA' : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (D : Module.Dual ℂ (locallyConstantCompactSupport (GL (Fin (n + 1)) k) ℂ ℂ)),
    (∀ p : GL (Fin (n + 1)) k, p ∈ Mir k n → ∀ f, D (biTranslL p p f) = D f) →
    ∀ (g : GL (Fin (n + 1)) k) f, D (biTranslL g g f) = D f




end PositivityTheory.PfBern.ThmA

end
