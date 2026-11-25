module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFormEqHighPowerSection

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_homogeneousForm_eq_highPowerSection : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) R, F.IsHomogeneous t ∧ ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F := by
  first | exact @GlobalTheory.AbLaw.exists_form_eq_sec_pw
