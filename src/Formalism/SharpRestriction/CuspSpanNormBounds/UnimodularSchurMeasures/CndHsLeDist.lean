import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

abbrev cnd_V (n : ℕ) : Type := EuclideanSpace ℂ (Fin n × Fin n)

def cnd_vec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : cnd_V n := WithLp.toLp 2 fun p => M p.1 p.2





def cnd_pt (X : CData) (x : X.I.GA) (γ : X.I.GFset) (v : InfinitePlace X.I.F) : Matrix (Fin X.I.n) (Fin X.I.n) ℂ :=
  umat ((x⁻¹ * (γ : X.I.GA) * x).1 v)

def CSize.SepStep {X : CData} (S : CSize X) : Prop :=
  ∀ (x : X.I.GA) (γ γ' : X.I.GFset), γ ≠ γ' → X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 → X.φ (x⁻¹ * (γ' : X.I.GA) * x) ≠ 0 →
    S.tau1 x ^ 2 ≤ (∏ v, Real.sqrt (Formalism.REAL.hs (cnd_pt X x γ v - cnd_pt X x γ' v))) ^
      ((1 : ℝ) / (Fintype.card (InfinitePlace X.I.F) : ℝ))


end Formalism.MainNotions.LeviCoordinates

end
