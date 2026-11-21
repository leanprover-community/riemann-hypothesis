import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInfEmbUnique

noncomputable section

namespace GlobalTheory.LettersCheck

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem isInfEmb_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (h' : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ') :
    θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem xiR_pos (D : D7) : 0 < xiR D := by
  unfold xiR
  refine norm_pos_iff.2 ((map_ne_zero _).2 ?_)
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have h1 := sq_emb D D.host.φ₀
    rw [h, map_zero] at h1
    have h2 : (D.host.d : ℂ) = 0 := by linear_combination h1
    have h3 := D.host.qd_big.2
    have h4 : D.host.d = 0 := by exact_mod_cast h2
    omega
  show -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) ≠ 0
  exact div_ne_zero (by simp) (mul_ne_zero (normK_ne_zero D) hs)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


theorem psgn_sq (p0 i : ℕ) : psgn p0 i * psgn p0 i = 1 := by
  unfold psgn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sgn
  split_ifs <;> norm_num

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = P.transpose * (G.map τ * P.map (starRingEnd ℂ)) := by
  ext a b
  simp [gram, hermC, col, Matrix.mul_apply, Finset.mul_sum, mul_assoc]


variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}

theorem relab_val (c : Coeff l) (τ : E →+* ℂ) : relab c c.F.val.toRingHom τ = τ := by
  ext a
  rfl

end GlobalTheory.LettersCheck
