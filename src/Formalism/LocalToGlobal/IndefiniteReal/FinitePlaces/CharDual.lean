import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharStd
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharCompl

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Topology Filter
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tate

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


end Tate

section Matrix

variable {D : D7} (S T : HSp D)

theorem embedding_xi_zero_ne_zero : D.host.xi0 ≠ 0 := by
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hdpos : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hd
    have : (Real.sqrt D.host.d : ℂ) = 0 := by
      rcases mul_eq_zero.1 hd.symm with h | h
      · exact absurd h Complex.I_ne_zero
      · exact h
    exact (Real.sqrt_pos.2 hdpos).ne' (by exact_mod_cast this)
  have hN : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  unfold Host.xi0
  exact div_ne_zero (neg_ne_zero.2 one_ne_zero) (mul_ne_zero hN hs)

def hE (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  ∑ a, ∑ b, ∑ c, ∑ d, S.gram⁻¹ a b * star (γ c b) * T.gram c d * e d a

def betaO (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.F :=
  Algebra.trace D.host.F D.host.E (D.host.xi0 * hE S T e γ)

theorem symplO_ratW_ratW (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplO S T (ratW T S e) (ratW T S γ) = algebraMap D.host.F (AF D.host.F) (betaO S T e γ) := by
  have h : hO S T (ratW T S e) (ratW T S γ) = incA D (hE S T e γ) := by
    unfold hO hE
    simp only [map_sum, map_mul, ratW, Matrix.map_apply, Brg.cA_inc]
  unfold symplO betaO
  rw [h, ← map_mul, trace_incA]

theorem symplO_smul_left (c : AF D.host.F) (x y : WO S T) : symplO S T (c • x) y = c * symplO S T x y := by
  have h : hO S T (c • x) y = algebraMap (AF D.host.F) (AE D) c * hO S T x y := by
    unfold hO
    simp only [Matrix.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring
  unfold symplO
  rw [h, mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

def symplLin (y : WO S T) : WO S T →ₗ[AF D.host.F] AF D.host.F where
  toFun x := symplO S T x y
  map_add' x x' := symplO_add_left S T x x' y
  map_smul' c x := symplO_smul_left S T c x y

theorem betaO_add_right (e γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    betaO S T e (γ + γ') = betaO S T e γ + betaO S T e γ' := by
  unfold betaO hE
  rw [← map_add, ← mul_add]
  congr 2
  simp only [Matrix.add_apply, star_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hE_smul_right (q : D.host.F) (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hE S T e (q • γ) = algebraMap D.host.F D.host.E q * hE S T e γ := by
  unfold hE
  have h : ∀ c b, star ((q • γ) c b) = algebraMap D.host.F D.host.E q * star (γ c b) := fun c b => by
    rw [Matrix.smul_apply, Algebra.smul_def, star_mul', Eqv.star_algebraMapF, mul_comm]
  simp only [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem hE_smul_left (q : D.host.F) (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hE S T (q • e) γ = algebraMap D.host.F D.host.E q * hE S T e γ := by
  unfold hE
  simp only [Matrix.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem trace_alg_mul (q : D.host.F) (z : D.host.E) :
    Algebra.trace D.host.F D.host.E (D.host.xi0 * (algebraMap D.host.F D.host.E q * z)) =
      q * Algebra.trace D.host.F D.host.E (D.host.xi0 * z) := by
  rw [mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem betaO_smul_right (q : D.host.F) (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    betaO S T e (q • γ) = q * betaO S T e γ := by
  unfold betaO; rw [hE_smul_right, trace_alg_mul]



def epsO (a : Formalism.IndefR.PHeisTh.Ix T S) : Matrix (Fin T.rank) (Fin S.rank) D.host.E :=
  Matrix.single a.1 a.2.1 (Module.finBasis D.host.F D.host.E a.2.2)



def LamO : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F] (Formalism.IndefR.PHeisTh.Ix T S → D.host.F) where
  toFun γ a := betaO S T (epsO S T a) γ
  map_add' γ γ' := by funext a; exact betaO_add_right S T _ γ γ'
  map_smul' q γ := by funext a; exact betaO_smul_right S T q _ γ







end Matrix

end Formalism.IndefR.Fin

end
