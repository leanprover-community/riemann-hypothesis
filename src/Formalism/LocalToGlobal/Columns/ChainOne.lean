import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def oneIdx (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (m2 : ℕ) : ChIdx X Pr R Q where
  β j := {_u : Unit // j ≤ m2 + 1}
  h _ _ _ := 1
  levG j _ := Λ j
  levQ j _ := LevQFam.top X.E X.K (R.N j) Q

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

open Classical in

structure OneCosetSym (m2 : ℕ) : Prop where
  surj : ∀ i, i < m2 → ∀ hh : rowSG Pr sel mu → AutY X R (i + 1),
    (∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → hh P ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1)) →
    (∀ P, FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 (hh P)) → ∀ P, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 1 (hh P)
  grpG : ∀ j, j ≤ m2 + 1 → ∀ (w : {w // w ∈ Pr.vGs}) (hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)),
    hbar ∈ (Λ j w).H ↔ ∃ g ∈ prCat (Pr := Pr) cst.sharp j w.1 (1 : AutY X R j),
      ∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (g x) = hbar.1.mulVec (redV w.1 x)
  chrG : ∀ j, j ≤ m2 + 1 → ∀ (w : {w // w ∈ Pr.vGs}) (hbar : ↥(Λ j w).H) (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (r : AutY X R j),
    r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) (1 : AutY X R j) →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) →
    (∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (g x) = hbar.1.1.mulVec (redV w.1 x)) →
    (((Λ j w).lam hbar : X.Kˣ) : X.K) = chiInv Ch sel mu cst j ⟨w.1, Finset.mem_union_left _ w.2⟩ (1 : AutY X R j) r

def OneYbSym (m2 : ℕ) : Prop :=
  ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    PsiAt Ch sel mu cst m2 P 1 x₀ y' ≠ 0 →
      ∀ l : Fin (R.N (m2 + 1)), IntAt P.1 ((qOf P.1 : X.E) * y' l) ∧ redP P.1 ((qOf P.1 : X.E) * y' l) = if l.1 = R.k then 1 else 0

def NonVanSym (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 1

variable {Ch sel mu cst Λ}


end One

end Formalism.L2.Col
