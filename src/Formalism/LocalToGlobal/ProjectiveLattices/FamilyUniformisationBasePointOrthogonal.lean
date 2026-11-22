module

public import Formalism.LocalToGlobal.ProjectiveLattices.CoreExists
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem rdU_mem (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x : Frame (U.X k).Ψ r} (h : x ∈ (U.X k).dom) :
    rdU U f k x = toC (evR Xo c f (U.un k ⟨x, h⟩)) := by
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h]

instance (σ : c.F →+* ℂ) : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)

end Fam

section Dict2

variable {Comp : Type}

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def DetRootMul (V : HSp D) : Prop :=
  ∀ g g' x x', IsDetRoot V g x → IsDetRoot V g' x' → IsDetRoot V (g * g') (x * x')

theorem detRootMul_holds (V : HSp D) : DetRootMul V := by
  intro g g' x x' hx hx'
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

end Dict2

section Base

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

end Base

section Inv

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

end Inv

section Rows

variable {D : D7}

def XiConst (D : D7) : Prop := ∀ τ : D.host.E →+* ℂ, ‖τ D.host.xi0‖ = xiR D

theorem xiConst_holds (D : D7) : XiConst D := by
  intro τ
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, sq_emb, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

end Rows

section Collected

variable {D : D7}

variable {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q}

end Collected

section J

variable {D : D7}

variable {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q}
  {chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle}

end J

end Formalism.L2.Pj
