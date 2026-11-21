import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Fintype
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfPowRealises
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def ModelTwistMulSecs.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (β : K → ℤ)
      (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      ∀ (p : ℕ) (m : ℤ),
        (Kleiman.twistMul Q.toSubSystem p m).secs = secOver F y (p • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelTwistMulSecs.of_modelMulSecs (h : ModelMulSecs.Statement) : ModelTwistMulSecs.Statement :=
  fun F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ p m => h F K ι Ω y k₀ N e hmod β Q hQ p m

theorem ModelTwistMulSecs.proof (hT : TensorRealises.Statement) : ModelTwistMulSecs.Statement :=
  ModelTwistMulSecs.of_modelMulSecs (ModelMulSecs.proof hT BaseRealises.proof)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
