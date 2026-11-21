import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnMeasurablePsi

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (dimN Vsph)

def cn_kapBd (Cv : ℝ) {a : ℕ} (j : Fin a → ℕ) (p q n0 f : ℕ) (v res : ℝ) : ℝ :=
  ((Cv ^ dimN j n0 * (Vsph p * Vsph q / (Vsph (p - ∑ x, j x) * Vsph (q - ∑ x, j x) * ∏ x, Vsph (j x)))) ^ f *
      (Cv * v) ^ ((f : ℝ) * (dimN j n0 : ℝ) / 2) * ∏ x, ((Cv * v) ^ (j x ^ 2 * f) * res * Cv ^ f)) *
    (v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * (f : ℝ) / 2) * Cv ^ ((p + q) * f))


def cn_res (X : CData) : ℝ := NumberField.dedekindZeta_residue X.I.E

def cn_ResBound (X : CData) (Cres : ℝ) : Prop := cn_res X ≤ (Cres * Real.log X.I.rd) ^ (2 * X.I.f)

def CSize.KappaVol {X : CData} (S : CSize X) (Cv : ℝ) : Prop :=
  ∀ (J : ℕ) (c : Composition J), 1 ≤ J → J ≤ X.qq →
    S.kap J c ≤ cn_kapBd Cv c.blocksFun (X.I.n - X.qq) X.qq (X.I.n - 2 * J) X.I.f (X.I.rd / 2) (cn_res X)



end Formalism.MainNotions.LeviCoordinates

end
