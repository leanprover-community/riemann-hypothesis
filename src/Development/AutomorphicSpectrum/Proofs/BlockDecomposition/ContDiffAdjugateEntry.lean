import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeSqrtMulSum

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp GlobalTheory.CompanionTheory.WaveCp.Rep
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Mol

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Dm (n : ℕ) : Set (Mat n × Mat n) := GLs n ×ˢ GLs n

def Ldp (X : Mat n) (K : Mat n × Mat n → V) : Mat n × Mat n → V := fun p => fderiv ℝ K p (0, X * p.2)

def Hw (w : List (Bool × Fin n × Fin n)) (K : Mat n × Mat n → V) : Mat n × Mat n → V :=
  w.foldr (fun p h => Ldp (bs p) h) K

def Hf (f : Mat n → V) : Mat n × Mat n → V := fun p => f (p.1⁻¹ * p.2)

@[simp] theorem Hw_nil (K : Mat n × Mat n → V) : Hw [] K = K := rfl



def fld (X : Mat n) : (Mat n × Mat n) →L[ℝ] (Mat n × Mat n) :=
  (ContinuousLinearMap.inr ℝ (Mat n) (Mat n)).comp ((GlobalTheory.CompanionTheory.RCalc.mulL X).comp (ContinuousLinearMap.snd ℝ (Mat n) (Mat n)))






end GlobalTheory.CompanionTheory.WaveCp.Rep.Mol
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp GlobalTheory.CompanionTheory.WaveCp.Rep GlobalTheory.CompanionTheory.WaveCp.Rep.Mol
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y i j) :=
  contDiff_apply_apply ℝ ℂ i j

theorem contDiff_det {n : ℕ} {M : Mat n → Mat n} (hM : ∀ i j, ContDiff ℝ ∞ (fun y => M y i j)) :
    ContDiff ℝ ∞ (fun y => (M y).det) := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => hM _ _

theorem contDiff_adjugate_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ∞ (fun y : Mat n => y.adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det fun a b => ?_
  by_cases h : a = j
  · subst h
    simpa [Matrix.updateRow_self] using contDiff_const
  · simpa [Matrix.updateRow_ne h] using contDiff_entry a b

theorem contDiffOn_inv {n : ℕ} : ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹) (GLs n) := by
  have hd : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹) (GLs n) :=
    (contDiff_det (M := id) contDiff_entry).contDiffOn.inv (fun y hy => hy)
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  refine (hd.mul (contDiff_adjugate_entry i j).contDiffOn).congr fun y _ => ?_
  simp [Matrix.inv_def, Ring.inverse_eq_inv]

end GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth
end
end
