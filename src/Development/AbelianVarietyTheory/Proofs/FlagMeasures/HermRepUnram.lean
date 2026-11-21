import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositive

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.binaryHermitianForm_represents_totallyPositive : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ a b n : K, star a = a → star b = b → star n = n → (∀ φ : K →+* ℂ, 0 < (φ a).re) → (∀ φ : K →+* ℂ, 0 < (φ b).re) → (∀ φ : K →+* ℂ, 0 < (φ n).re) → ∃ s t : K, a * (s * star s) + b * (t * star t) = n := by
  first | exact @GlobalTheory.BinaryRep.represents_totallyPositive | exact GlobalTheory.BinaryRep.represents_totallyPositive | (intros; apply GlobalTheory.BinaryRep.represents_totallyPositive <;> assumption)
end

section
namespace GlobalTheory

theorem hermRepUnram : Formalism.HermitianLattices.Ext.L3.HermRepUnram := GlobalTheory.T.binaryHermitianForm_represents_totallyPositive

instance : Fact (Formalism.HermitianLattices.Ext.L3.HermRepUnram) := ⟨hermRepUnram⟩

end GlobalTheory
end
