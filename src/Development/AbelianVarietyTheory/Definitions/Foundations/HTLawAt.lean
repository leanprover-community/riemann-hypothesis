module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.KumValUnique
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def htv (j : Ω →+* Qbar l) (ζ : Ω) {ι : Type} [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) (b : ℕ) : Qbar l :=
  ∑ i, o i * j (ζ ^ b * (Polynomial.derivative (P i)).eval (ζ ^ b) / (P i).eval (ζ ^ b))

def tval (L : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) : Qbar l := ∑ n ∈ Finset.range N, L.coeff n * (z - 1) ^ n

def mass (L : PowerSeries (Qbar l)) (r : ℕ) (ξ : Qbar l) (x : ℕ) : Qbar l :=
  ∑ k ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (k * x) % l ^ r) * tval L (l ^ (3 * r)) (ξ ^ k)

end GlobalTheory.KZ
