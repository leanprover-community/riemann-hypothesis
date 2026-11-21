import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.EqZeroIffSubsingleton
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.QuotientTiedToDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InhabitedAndRefines

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem evenDefect_one_iff (D : DegPre R) : EvenDefect D (fun _ => 1) ↔ D.PsiEven := by
  have e : unitOn (1 : (FractionRing R)ˣ) = 1 := map_one _
  constructor
  · intro h χ
    refine corr_of_val D.P.isLB fun y J hJ => ?_
    have := h χ y J hJ
    rw [e, map_one, _root_.one_mul] at this
    rw [val_mul hJ, val_pull hJ, Category.id_comp]
    exact this
  · intro h χ z J hJ
    have := val_corr hJ (h χ) (𝟙 _)
    rw [val_mul hJ, val_pull hJ, Category.id_comp] at this
    rw [e, map_one, _root_.one_mul]
    exact this

theorem evenDefect_rescale (D : DegPre R) (h g : D.X → (FractionRing R)ˣ) (H : EvenDefect D h) :
    EvenDefect (rescale D g) (fun χ : D.X => h χ * g (-χ) * (g χ)⁻¹) := by
  intro χ z J hJ
  have := H χ z J hJ
  have a : ∀ χ : D.X, val ((rescale D g).psi χ) (𝟙 (TK R).left) z J =
      gm (𝟙 (TK R).left) z ⊤ (unitOn (g χ)) * val (D.psi χ) (𝟙 (TK R).left) z J := fun χ =>
    GlobalTheory.UU.val_scaleGen (Y := (TK R).left) (L := D.P.L) (unitOn (g χ)) (D.psi χ) (𝟙 _) hJ
  let u : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
    (gm (𝟙 (TK R).left) z ⊤).comp (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom.toMonoidHom)
  have key : ∀ (χ : D.X) (p m s : ((TK R).left.presheaf.stalk z)ˣ), m * s = u (h χ) * p →
      u (g (-χ)) * m * s = u (h χ * g (-χ) * (g χ)⁻¹) * (u (g χ) * p) := fun χ p m s e => by
    rw [_root_.mul_assoc, e, map_mul, map_mul, map_inv]
    generalize u (h χ) = A, u (g (-χ)) = B, u (g χ) = C
    rw [_root_.mul_assoc (A * B), inv_mul_cancel_left, mul_left_comm, _root_.mul_assoc]
  exact (congrArg (fun q => q * val D.sym (D.xK χ) z J) (a (-(show D.X from χ)))).trans
    ((key χ _ _ _ this).trans (congrArg (fun q => u (h χ * g (-(show D.X from χ)) * (g χ)⁻¹) * q) (a χ).symm))





end GlobalTheory.PolDeg
