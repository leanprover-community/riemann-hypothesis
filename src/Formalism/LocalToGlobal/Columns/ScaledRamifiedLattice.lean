module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.ColForms
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section MovesA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end MovesA

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

def diamondOperatorOnForms' (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofMap (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _) (fun d => DecoSet.dia1 P c d) LinearMap.id
    (fun g d => DecoSet.dia_smul _ (FormG.incl Λ g) d) (fun _ _ => rfl)).op

def NmG (P : ST) : Module.End X.K (formGSD C Λ).EqFun :=
  letI : Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := Fintype.ofFinite _
  ∑ c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ, diamondOperatorOnForms' C Λ P c

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def diaOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    Module.End X.K (ColV W Ch u j) :=
  diamondOperatorOnForms' (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P c

def NmOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  NmG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P

end Cols

section Cols2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

def ColRamV (u : Pr.Word) (j : ℕ) : Submodule X.K (ColV W Ch u j) :=
  ⨅ P : {P // P ∈ Pr.vT u}, LinearMap.ker (NmOp W Ch u j P)

def ColRamL (u : Pr.Word) (j : ℕ) : Submodule (𝓞 X.K) (ColRamV W Ch u j) :=
  (ColL W Ch u j).comap ((ColRamV W Ch u j).subtype.restrictScalars (𝓞 X.K))

abbrev MramV (u : Pr.Word) : Submodule X.K (MfV W Ch u) := ColRamV W Ch u 0

def MramL (u : Pr.Word) : Submodule (𝓞 X.K) (MramV W Ch u) := ColRamL W Ch u 0

def ramIncl (u : Pr.Word) : MramV W Ch u →ₗ[X.K] MfV W Ch u := (MramV W Ch u).subtype

end Cols2

section Seen

variable {X : Fields}

def Fields.embO (X : Fields) (τ : X.Tau) : 𝓞 X.E →+* 𝓞 X.K := RingOfIntegers.mapRingHom (X.emb τ)

def pullW (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := w.asIdeal.comap (X.embO τ)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have h1 : ((prW w : ℕ) : 𝓞 X.E) ∈ w.asIdeal.comap (X.embO τ) := by
      rw [Ideal.mem_comap, map_natCast]
      exact natCast_prW_mem w
    rw [h, Ideal.mem_bot] at h1
    exact (prW_prime w).ne_zero (by exact_mod_cast h1)

def SeesP (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : HeightOneSpectrum (𝓞 X.E)) : Prop := pullW τ w = P

def SeesPbar (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : HeightOneSpectrum (𝓞 X.E)) : Prop :=
  pullW τ w = conjPrime₂ P

variable (Pr : Primes X)

def seenC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Prop := ∀ τ, X.embO τ (Pr.piT u) ∈ w.asIdeal

def seenBarC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Prop :=
  ∀ τ, X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal

end Seen

section Nlam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Nlam

end Formalism.L2.Col
