import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Psi

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem psi_norm (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ‖ψ a‖ = 1 := hψ.1.2.1 a

theorem psi_ne (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have h1 := psi_norm hψ a
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem psi_conj (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : conj (ψ a) = ψ (-a) := by
  have h1 : ψ a * conj (ψ a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, psi_norm hψ a]
    simp
  have h2 : ψ a * ψ (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  exact mul_left_cancel₀ (psi_ne hψ a) (h1.trans h2.symm)

theorem psi_rat (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (ratW T S a) (ratW T S b)) = 1 := by
  obtain ⟨q, hq⟩ := symplO_rat (S := S) (T := T) a b
  rw [hq]
  exact hψ.1.2.2.1 q

theorem psi_cont (hψ : IsStdChar D ψ (-1)) : Continuous ψ := hψ.1.1

end Psi

section Cont

variable (S T : HSp D)

theorem cont_trace : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
  IsModuleTopology.continuous_of_linearMap _

def cAlin (D : D7) : AE D →ₗ[AF D.host.F] AE D where
  toFun := cA D
  map_add' := map_add _
  map_smul' := Formalism.IndefR.PHeisTh.cA_smul

theorem cont_cA : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap (cAlin D)

theorem cont_hO : Continuous fun p : MO S T × MO S T => hO S T p.1 p.2 := by
  have hcA : Continuous (cA D) := cont_cA
  delta hO
  fun_prop

theorem cont_symplO : Continuous fun p : MO S T × MO S T => symplO S T p.1 p.2 := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := cont_trace
  have hh := cont_hO S T
  delta symplO
  first
    | exact ht.comp (continuous_const.mul hh)
    | fun_prop


theorem cont_symplO_left (w : MO S T) : Continuous fun z : MO S T => symplO S T z w := by
  have h : Continuous (Function.uncurry (symplO S T)) := cont_symplO S T
  exact h.uncurry_right w

theorem cont_symplOH_left (w : MO S T) : Continuous fun z : MO S T => symplOH S T z w := by
  delta symplOH
  exact continuous_const.mul (cont_symplO_left S T w)

end Cont

section Per

variable (S T : HSp D)

theorem exists_rat_shift (z : MO S T) : ∃ a : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
    ratW T S a + z ∈ Formalism.IndefR.PHeisFC.FD T S := by
  classical
  have hq : ∀ i j k, ∃ q : D.host.F, algebraMap D.host.F (AF D.host.F) q +
      Formalism.IndefR.PHeisFC.Phi T S z i j k ∈ Formalism.IndefR.PHeisFC.F0 D.host.F :=
    fun i j k => (Formalism.IndefR.PHeisFC.ad_exU (F := D.host.F) _).exists
  choose q hq using hq
  have hc : ∀ (e : D.host.E) (k : Fin (Module.finrank D.host.F D.host.E)),
      Formalism.IndefR.PHeisFC.cE D.host.F D.host.E (incA D e) k =
        algebraMap D.host.F (AF D.host.F) ((Module.finBasis D.host.F D.host.E).repr e k) := by
    intro e k
    show (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).repr ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) k = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp
  refine ⟨fun i j => ∑ k, q i j k • Module.finBasis D.host.F D.host.E k, ?_⟩
  intro i j k
  show Formalism.IndefR.PHeisFC.cE D.host.F D.host.E
    (incA D (∑ k', q i j k' • Module.finBasis D.host.F D.host.E k') + z i j) k ∈ _
  rw [map_add, Pi.add_apply, hc, Module.Basis.repr_sum_self]
  exact hq i j k

theorem bdd_of_periodic {E' : Type*} [NormedAddCommGroup E'] (g : MO S T → E') (hg : Continuous g)
    (hp : ∀ a z, ‖g (ratW T S a + z)‖ = ‖g z‖) : ∃ C, ∀ z, ‖g z‖ ≤ C := by
  obtain ⟨K, hK, hFK⟩ := Formalism.IndefR.PHeisFC.FD_sub_compact T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun z => ?_⟩
  obtain ⟨a, ha⟩ := exists_rat_shift S T z
  rw [← hp a z]
  exact hC _ (hFK ha)



end Per

section Theta

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)



theorem cont_heis (hψ : IsStdChar D ψ (-1)) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (v : MO S T) :
    Continuous (heisO ψ S T v f) := by
  delta heisO
  exact ((psi_cont hψ).comp (cont_symplOH_left S T v)).mul (hf.3.comp (continuous_add_right v))



theorem theta_zero : IsThetaFunO ψ S T 0 := by
  exact ⟨fun γ w => by simp, ⟨⊤, by simp, fun u _ _ => by funext z; simp [heisO]⟩, continuous_zero,
    fun k L _ _ _ => contDiff_const⟩

theorem theta_add {f g : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by
  obtain ⟨hq1, ⟨U1, hU1, hl1⟩, hc1, hs1⟩ := hf
  obtain ⟨hq2, ⟨U2, hU2, hl2⟩, hc2, hs2⟩ := hg
  refine ⟨fun γ w => ?_, ⟨U1 ⊓ U2, ?_, fun u hu h0 => ?_⟩, hc1.add hc2,
    fun k L hL h0 w => (hs1 k L hL h0 w).add (hs2 k L hL h0 w)⟩
  · simp only [Pi.add_apply, hq1 γ w, hq2 γ w, mul_add]
  · rw [AddSubgroup.coe_inf]
    exact hU1.inter hU2
  · have e1 := hl1 u hu.1 h0
    have e2 := hl2 u hu.2 h0
    funext z
    have z1 := congrFun e1 z
    have z2 := congrFun e2 z
    simp only [heisO, Pi.add_apply, Pi.zero_apply] at z1 z2 ⊢
    rw [mul_add, z1, z2]

theorem theta_smul (c : ℂ) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
  obtain ⟨hq1, ⟨U1, hU1, hl1⟩, hc1, hs1⟩ := hf
  refine ⟨fun γ w => ?_, ⟨U1, hU1, fun u hu h0 => ?_⟩, hc1.const_smul c,
    fun k L hL h0 w => (hs1 k L hL h0 w).const_smul c⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hq1 γ w]
    ring
  · have e1 := hl1 u hu h0
    funext z
    have z1 := congrFun e1 z
    simp only [heisO, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at z1 ⊢
    rw [mul_left_comm, z1]

end Theta


theorem polar_pt (u v : ℂ) : u * conj v = (1 / 4) * ((((‖u + v‖ ^ 2 : ℝ) : ℂ) - ((‖u - v‖ ^ 2 : ℝ) : ℂ)) +
    Complex.I * ((‖u + Complex.I * v‖ ^ 2 : ℝ) : ℂ) - Complex.I * ((‖u - Complex.I * v‖ ^ 2 : ℝ) : ℂ)) := by
  have key : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [key, key, key, key]
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * (u * conj v - v * conj u) * Complex.I_sq

section Svn

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)




end Svn

end Formalism.IndefR.Fin

end
