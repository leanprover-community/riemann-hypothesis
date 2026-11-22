module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.Columns.HeckeSp

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

namespace RowPar

variable {R : Ranks} (S : RowPar R)

end RowPar

namespace Wts

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

end Wts

section Forms

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

@[reducible] def wmGSD (P : LevFam X.E X.K R.r Pr.vGs) : GSD X.K :=
  formGSD (wmVal W (rowSG Pr sel mu)) (wmTy sel mu P).inv

end Forms

section Data

variable {E : Type} [Field E] [NumberField E] [StarRing E]

variable {SG : Finset (HeightOneSpectrum (𝓞 E))}

end Data

section Dist

variable (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (a b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (V V' : Type) [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

variable {E K a b SG V V'}

end Dist

section Theta

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Theta

section Z

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Z

section NbFun

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]

def nbFun (P : Ideal (𝓞 E)) (i : ℕ) : (DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → V) →ₗ[K] (DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → V) where
  toFun ψ d := ∑ d₁ ∈ d.heckeNb P i, ψ d₁
  map_add' ψ ψ' := by
    funext d
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext d
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

end NbFun

section Rel

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Rel

end Formalism.L2.Col
