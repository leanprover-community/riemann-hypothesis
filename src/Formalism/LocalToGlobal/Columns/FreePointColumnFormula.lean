import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingEquivalence.CompSymmComp

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Reps

open Classical

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}




end Reps

section Perm


end Perm

section Alg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n' n c : ℕ}









def freeCoordinatesTransform (y : HomE E n' n) (r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))) (t : Loc.FC n' (c + 1) n c → E) :
    Loc.FC n' (c + 1) n c → E :=
  fun p => (Loc.xx1 y t ∘ₗ r.toLinearMap) (Pi.single p.1.2 1) p.1.1



end Alg

section An

open Classical

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {n' n c : ℕ}








def clS_phi (y : HomE E n' n) (r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))) (t : Loc.FC n' (c + 1) n c → E)
    (p : Loc.FC n' (c + 1) n c) : E :=
  ∑ s' : Fin (n' + (c + 1)), if s'.1 < p.1.2.1 then r (Pi.single p.1.2 1) s' * Loc.xx1 y t (Pi.single s' 1) p.1.1 else 0





end An

section Main

open Classical

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {K : Type} [Field K] {n' n c : ℕ}




def clS_G (psi : E → K) (Ψ : Loc.SF E K (n' + (c + 1)) (n + c)) (yj : HomE E n' n) (u : Loc.FC n' (c + 1) n c → E) : K :=
  Ψ (Loc.xx1 yj u) * psi (-Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 yj u))



def clS_rp (P : HeightOneSpectrum (𝓞 E)) (q A B : ℕ) (v : E) : E :=
  if h : ∃ u ∈ LocE.valsQ E q A B, IntAt P ((v - u) / (q : E) ^ B) then h.choose else 0





end Main

end Formalism.L2.Col
