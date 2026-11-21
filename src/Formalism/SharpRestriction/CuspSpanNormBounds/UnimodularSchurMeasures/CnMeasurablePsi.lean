import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnMeasurableSetReg

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma



def cn_hT (f n0 j : ℕ) : ℝ → ℝ :=
  (Set.Ioo (0 : ℝ) (1 / 2)).indicator fun s : ℝ => s ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / s)



def cn_hL (f j : ℕ) (ts : ℝ) : ℝ → ℝ := (Set.Ico ts (1 / 2)).indicator fun s : ℝ => 2 * (f : ℝ) * j / s







def cn_Psi {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (de ts : ℝ) : (Fin a → ℝ) → ℝ≥0∞ := fun t =>
  ENNReal.ofReal (cn_cnt j n0 f de t) * ({t : Fin a → ℝ | ∀ x, ts ≤ t x}.indicator 1 t)





namespace CSize

variable {X : CData} (S : CSize X)





end CSize

end Formalism.MainNotions.LeviCoordinates

end
