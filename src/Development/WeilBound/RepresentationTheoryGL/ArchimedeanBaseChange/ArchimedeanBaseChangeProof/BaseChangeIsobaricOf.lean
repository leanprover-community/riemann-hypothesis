module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB

structure Datum (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, IsCsdGL (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def SplitAt (π : Submodule ℂ (UA E n → ℂ)) (D : Datum E n) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w)) ∧
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ

def SatAt (D : Datum E n) (w : HeightOneSpectrum (𝓞 E)) (B : Fin D.c → Multiset ℂˣ) : Prop :=
  ∀ i, GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (n := (D.N i))) ∧ GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ (B i)

def Weak (π : Submodule ℂ (UA E n → ℂ)) (D : Datum E n) : Prop :=
  (∀ τ lam, HasWeightAt π τ lam → ∑ i, D.m i τ = infOfWeight lam) ∧
    {w | IsSplitAt w ∧ ¬ SplitAt π D w}.Finite

def Unr (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal

def RunSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ D : Datum E n, Weak π D ∧
    (∀ w ∈ S, IsSplitAt w → SplitAt π D w) ∧ ∀ w, IsUnramU π w → ¬ IsSplitAt w → ∃ B, SatAt D w B

def RunInert : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w, IsUnramU π w → ¬ IsSplitAt w → ∃ D : Datum E n, Weak π D ∧
    ∀ B, SatAt D w B → ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
      ∀ α, HasSatAt π w s ϖ q α → ∑ i, B i = GlobalTheory.LGrp.bcParam n α

def Rigid : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ D D' : Datum E n, Weak π D → Weak π D' → ∀ w,
    (∀ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D'.h w (D'.σ · w)) →
      GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w))) ∧
    ∀ B, SatAt D w B → ∃ B', SatAt D' w B' ∧ ∑ i, B i = ∑ i, B' i

end PositivityTheory.Rg.BcB

end
