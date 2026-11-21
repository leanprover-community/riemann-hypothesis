import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair

section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.PolyRep

theorem lie_sum {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R]
    (A : Mat m R) :
    (ρ.sum σ).lie A = blockSum (ρ.lie A) (σ.lie A) := by
  ext i j
  simp only [lie, Matrix.of_apply]
  change Fin (ρ.M + σ.M) at i j
  change ∑ v : EntIx m, aeval (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2)
      (pderiv v (blockSum ρ.ent σ.ent i j)) * A v.1 v.2.1 v.2.2 = _
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rcases x with x | x <;> rcases y with y | y <;> simp [lie, sum, blockSum]

end GlobalTheory.GoodMetric.PolyRep
end
end

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_directSum : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), (ρ.sum σ).lie A = blockSum (ρ.lie A) (σ.lie A) := by
  atlas_forward_decl GlobalTheory.GoodMetric.PolyRep.lie_sum
