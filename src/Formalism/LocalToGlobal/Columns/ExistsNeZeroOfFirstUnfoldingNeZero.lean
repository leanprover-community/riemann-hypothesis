import Formalism.LocalToGlobal.Columns.ChainTwAux
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwE1J

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem isUnit_reduction_mul_iff₂ {u y : E} (hu0 : u ≠ 0) (hu : IntAt P u) (hu' : IntAt P u⁻¹) :
    IsUnit (redP P (y * u)) ↔ IsUnit (redP P y) := by
  have hru : IsUnit (redP P u) := by
    have h1 : redP P u * redP P u⁻¹ = 1 := by rw [← reduction_mul hu hu', mul_inv_cancel₀ hu0, redP_one]
    exact isUnit_iff_exists_inv.2 ⟨_, h1⟩
  by_cases hy : IntAt P y
  · rw [reduction_mul hy hu, IsUnit.mul_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hru⟩⟩
  · have hyu : ¬ IntAt P (y * u) := fun h => hy (by
      have e : y = (y * u) * u⁻¹ := by field_simp
      rw [e]; exact h.mul hu')
    rw [reduction_eq_zero_of_not_integral P hy, reduction_eq_zero_of_not_integral P hyu]





end TwE1J

section TwE1JMain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}


def twOmS (c : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (g : AutY X R (i + 1)) : X.K :=
  muAt Ch sel mu c i P (LinearEquiv.det hal : X.Eˣ) * (muAt Ch sel mu c i P (LinearEquiv.det g : X.Eˣ))⁻¹ *
    c.sq P ^ (-(LocE.vP P.1 (qOf P.1) (LinearEquiv.det hal : X.Eˣ)) * ((R.N (i + 1) + cOf R (i + 1) : ℕ) : ℤ)) *
    c.sq P ^ (LocE.vP P.1 (qOf P.1) (LinearEquiv.det g : X.Eˣ) * ((R.N i + cOf R i : ℕ) : ℤ))



variable (Ch sel mu cst) in

def UnfoldingNonvanishingLeftCoset (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h r : AutY X R (i + 1)),
    r ∈ Loc.R1 X.E (R.N (i + 1)) (cOf R (i + 1)) → TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 h →
      TwBdd (Pr := Pr) (i + 1) P.1 (r * h) → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal (r * h)


end TwE1JMain

end Formalism.L2.Col
