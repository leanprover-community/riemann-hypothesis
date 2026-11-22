module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
public import Formalism.LocalToGlobal.Columns.GSetLemmas
public import Formalism.LocalToGlobal.Columns.ColFormsLemmas

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section DiaMoves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

instance diaAction : MulAction (DiaG (E := E) (ST := ST)) (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) where
  smul c d := d.dia c
  one_smul := DecoSet.dia_one
  mul_smul c c' d := DecoSet.dia_mul c c' d

end DiaMoves

section OpsL

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end OpsL

section ColsL

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColsL

section SeenL

variable {X : Fields} {Pr : Primes X}

theorem mem_pullW (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) (x : 𝓞 X.E) :
    x ∈ (pullW τ w).asIdeal ↔ X.embO τ x ∈ w.asIdeal := Iff.rfl

theorem pullW_mem_vT (hPr : Pr.Ok) (u : Pr.Word) (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) :
    pullW τ w ∈ Pr.vT u ↔ X.embO τ (Pr.piT u) ∈ w.asIdeal :=
  mem_divs (hPr.piT_ne_zero u) _

theorem embO_of_Kq {x : 𝓞 X.E} (hx : (x : X.E) ∈ X.Kq) (τ τ' : X.Tau) : X.embO τ x = X.embO τ' x :=
  RingOfIntegers.ext (hx τ τ')

theorem conjO_mem_Kq (hX : X.Ok) {x : 𝓞 X.E} (hx : (x : X.E) ∈ X.Kq) : ((X.conjO x : 𝓞 X.E) : X.E) ∈ X.Kq := by
  intro τ τ'
  show X.emb τ (star (x : X.E)) = X.emb τ' (star (x : X.E))
  rw [hX.emb_star, hX.emb_star, hx τ τ']

theorem seenC_iff (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    seenC Pr u w ↔ ∀ τ, pullW τ w ∈ Pr.vT u :=
  forall_congr' fun τ => (pullW_mem_vT hPr u τ w).symm

theorem seenC_or_seenBarC (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K))
    (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) : seenC Pr u w ∨ seenBarC Pr u w := by
  by_cases hne : Nonempty X.Tau
  · obtain ⟨τ₀⟩ := hne
    have h1 : X.embO τ₀ (Pr.piT u) * X.embO τ₀ (X.conjO (Pr.piT u)) ∈ w.asIdeal := by
      rw [← map_mul, hPr.piT_norm u, map_natCast]
      exact hw
    rcases w.isPrime.mem_or_mem h1 with h | h
    · left
      intro τ
      rw [embO_of_Kq (hPr.piT_Kq u) τ τ₀]
      exact h
    · right
      intro τ
      rw [embO_of_Kq (conjO_mem_Kq hX (hPr.piT_Kq u)) τ τ₀]
      exact h
  · left
    intro τ
    exact absurd ⟨τ⟩ hne

variable {R : Ranks} (W : Wts X Pr.Word R)

end SeenL

end Formalism.L2.Col
