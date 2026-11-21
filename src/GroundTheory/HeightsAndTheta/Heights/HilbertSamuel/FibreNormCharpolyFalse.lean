import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormCharpoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormCharpoly

theorem aeval_mul_of_isHomogeneous {σ' Ω : Type*} [Field Ω] [CharZero Ω] {p : MvPolynomial σ' ℚ} {d : ℕ}
    (hp : p.IsHomogeneous d) (μ : Ω) (f : σ' → Ω) :
    aeval (fun j => μ * f j) p = μ ^ d * aeval f p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring


end FibreNormCharpoly

namespace ProjLine

open ProjLine

def swapIx : (Σ k, GlobalTheory (Fin 2) k) → (Σ k, GlobalTheory (Fin 2) k) := fun p => ⟨(), Fin.rev p.2⟩

theorem swapIx_injective : Function.Injective swapIx := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  have : Fin.rev i = Fin.rev j := by simpa [swapIx] using h
  rw [Fin.rev_inj] at this
  rw [this]

theorem swap_injective :
    Function.Injective ((algebraMap (MRing (GlobalTheory (Fin 2))) Kfr).comp (rename swapIx).toRingHom) :=
  (IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr).comp (rename_injective _ swapIx_injective)

def swapK : Kfr →+* Kfr := IsFractionRing.lift swap_injective

theorem swapK_Xk (i : Fin 2) : swapK (Xk i) = Xk (Fin.rev i) := by
  simp [swapK, Xk, IsFractionRing.lift_algebraMap, swapIx]

theorem swapK_u : swapK u = u⁻¹ := by
  rw [u, map_div₀, swapK_Xk, swapK_Xk, inv_div]
  rfl

theorem closure_le_comap_swapK :
    Subfield.closure ({u} : Set Kfr) ≤ (Subfield.closure ({u} : Set Kfr)).comap swapK := by
  rw [Subfield.closure_le]
  rintro _ rfl
  show swapK u ∈ Subfield.closure ({u} : Set Kfr)
  rw [swapK_u]
  exact inv_mem (Subfield.subset_closure rfl)

def swapF : FnField →+* FnField :=
  (swapK.comp incl).codRestrict (Subfield.closure ({u} : Set Kfr)) fun x => closure_le_comap_swapK x.2




def Lc : Fin 2 → MRing (GlobalTheory (Fin 2)) :=
  ![X ⟨(), 0⟩ * X ⟨(), 1⟩, X ⟨(), 0⟩ ^ 2 + X ⟨(), 1⟩ ^ 2]

theorem Lc_zero : Lc 0 = X ⟨(), 0⟩ * X ⟨(), 1⟩ := rfl








end ProjLine

namespace FibreNormCharpoly

open ProjLine


end FibreNormCharpoly

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
