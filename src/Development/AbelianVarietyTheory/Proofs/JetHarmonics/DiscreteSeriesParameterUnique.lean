module

import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.BetaAtInfinityZero
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory
namespace DSInequiv

open PI.DSInfCharCap

section
variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def toReal (V : H ≃L[ℂ] H') : H ≃L[ℝ] H' :=
  { V.toLinearEquiv.restrictScalars ℝ with
    continuous_toFun := V.continuous
    continuous_invFun := V.symm.continuous }

lemma dsig_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Formalism.REAL.inG ε X) (v : H) :
    V (PI.PhMeasCore.dsig τ X v) = PI.PhMeasCore.dsig τ' X (V v) := by
  unfold PI.PhMeasCore.dsig
  have e : (fun t : ℝ => τ' (NormedSpace.exp ((t : ℂ) • X)) (V v)) =
      (toReal V) ∘ (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • X)) v) := by
    funext t
    exact (hV _ (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t) v).symm
  rw [e]
  unfold deriv
  rw [ContinuousLinearEquiv.comp_fderiv]
  rfl

open scoped Matrix.Norms.Elementwise

end

end DSInequiv
end GlobalTheory
