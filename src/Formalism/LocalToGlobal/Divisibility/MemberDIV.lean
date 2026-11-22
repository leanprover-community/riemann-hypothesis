module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.ColPins
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV.Member

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Rows Formalism.L2.Col Formalism.L2.DIV

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

section Fam

variable {X : Fields} {e : X.Tau → (X.E →+* D.what₂.LL)} {Pr : Primes (fieldsLL D X e)}
  (W : Wts (fieldsLL D X e) Pr.Word D.R) (Ch : Chars (fieldsLL D X e) Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (hX : (fieldsLL D X e).Ok)
  (v0 : InfinitePlace D.what₂.LL) (TU : Finset (Tup X.F X.E D.what₂.LL Sg))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs D.R.r → D.what₂.LL))
  (xiVal : Tup X.F X.E D.what₂.LL Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ)
  (trIv : Fin D.R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL)

end Fam

section Cols

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (Gc : ChGlob X R.m) (m2 : ℕ) (Mem : Type)

end Gen

variable {X : Fields} {e : X.Tau → (X.E →+* D.what₂.LL)} {Pr : Primes (fieldsLL D X e)}
  (W : Wts (fieldsLL D X e) Pr.Word D.R) (Ch : Chars (fieldsLL D X e) Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (Gc : ChGlob (fieldsLL D X e) D.R.m) (m2 : ℕ)

variable {W Ch sel Gc m2} (F : ColFam W Ch sel Sg Gc m2 D.what₂.Word) (hX : (fieldsLL D X e).Ok)
  (v0 : InfinitePlace D.what₂.LL) (TU : Finset (Tup X.F X.E D.what₂.LL Sg))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs D.R.r → D.what₂.LL))
  (xiVal : Tup X.F X.E D.what₂.LL Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ)
  (trIv : Fin D.R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL)

end Cols

section IndefiniteRowSideFullHecke

structure ExtendedDataRemainder {G Pl0 I0 Tt : Type} [Group G] [Fintype G] (ex : Extra D L hT Gi Gl Kc Y cX)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) Tt D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* D.what₂.LLˣ) (Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)) : Type 1 where
  Zs : DefSub A3.fam3.amb3
  S0 : IndefData (A3.side3 P0 ψ0 Zs)
  S1 : IndefData (A3.side3 P1 ψ1 Zs)
  C : ColData (Dcf Zs) (Spf Zs) S1
  NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin ((Dcf Zs).a u) → D.what₂.LL)
  I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 P1 ψ1 Zs S0 S1 ex.p0 (Dcf Zs)
  JA : AmbIds D A3.A ex.p0.s ex.amb0 P0 ψ0 I.tup
  JM : MjHIds D A3.A Y (A3.indefDown S0)
  tied : BaseDivisionAmbientCompatibilityFamily D A3 Y ex.p0 ex.amb0 P0 ψ0 P1 ψ1 Zs S0 S1 C NuC I JA JM

variable {G Pl0 I0 Tt : Type} [Group G] [Fintype G] {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) Tt D.R.m} {P0 : Subgroup G}
  {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ} {Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)}

def ExtendedDataRemainder.extendedDatum (R : ExtendedDataRemainder ex A3 P0 ψ0 P1 ψ1 Dcf Spf) : RowSideFamily ex :=
  ⟨G, Pl0, I0, Tt, A3, P0, ψ0, P1, ψ1, R.Zs, R.S0, R.S1, Dcf R.Zs, Spf R.Zs, R.C, R.NuC, R.I, R.JA, R.JM, R.tied⟩

end IndefiniteRowSideFullHecke

section K

variable {X : Fields} {e : X.Tau → (X.E →+* D.what₂.LL)} {Pr : Primes (fieldsLL D X e)}
  {W : Wts (fieldsLL D X e) Pr.Word D.R} {Ch : Chars (fieldsLL D X e) Pr D.R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ} {Gc : ChGlob (fieldsLL D X e) D.R.m} {m2 : ℕ}
  (F : ColFam W Ch sel Sg Gc m2 D.what₂.Word) (hX : (fieldsLL D X e).Ok)
  (v0 : InfinitePlace D.what₂.LL) (TU : Finset (Tup X.F X.E D.what₂.LL Sg))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs D.R.r → D.what₂.LL))
  (xiVal : Tup X.F X.E D.what₂.LL Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ)
  (trIv : Fin D.R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL)
  (hE : ∀ x, (evGSD W Ch sel ((famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.base3.μ0 : TupF (X := fieldsLL D X e) TU).1
      (rPsymF (R := D.R) Ch) (F.wd x)).Ok)
  (ev : ∀ (Zs : DefSub (famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.amb3) (t : TupF (X := fieldsLL D X e) TU),
      (Fin (((famM W Ch sel hX v0 TU Xg xiVal trIv).side3 (rPsymF (R := D.R) Ch).grp (rPsymF (R := D.R) Ch).chr Zs).nV t) →
        D.what₂.LL) →ₗ[D.what₂.LL] V0X W Ch sel t.1 Xg (rPsymF (R := D.R) Ch))
  (Sp : ∀ Zs, SPer ((colM F hX v0 TU Xg xiVal trIv hE ev).face Zs))

variable {F hX v0 TU Xg xiVal trIv hE ev Sp} (T : TiedDataSK ex) (R : RestM F hX v0 TU Xg xiVal trIv hE ev Sp ex)

end K

section Pins

variable {T : TiedDataSK ex} {P : RowSideFamily ex}

variable {X : Fields} {e : X.Tau → (X.E →+* D.what₂.LL)} {Pr : Primes (fieldsLL D X e)}
  {W : Wts (fieldsLL D X e) Pr.Word D.R} {Ch : Chars (fieldsLL D X e) Pr D.R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ} {Gc : ChGlob (fieldsLL D X e) D.R.m} {m2 : ℕ}
  {F : ColFam W Ch sel Sg Gc m2 D.what₂.Word} {hX : (fieldsLL D X e).Ok}
  {v0 : InfinitePlace D.what₂.LL} {TU : Finset (Tup X.F X.E D.what₂.LL Sg)}
  {Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs D.R.r → D.what₂.LL)}
  {xiVal : Tup X.F X.E D.what₂.LL Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ}
  {trIv : Fin D.R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL}
  {hE : ∀ x, (evGSD W Ch sel ((famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.base3.μ0 : TupF (X := fieldsLL D X e) TU).1
      (rPsymF (R := D.R) Ch) (F.wd x)).Ok}
  {ev : ∀ (Zs : DefSub (famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.amb3) (t : TupF (X := fieldsLL D X e) TU),
      (Fin (((famM W Ch sel hX v0 TU Xg xiVal trIv).side3 (rPsymF (R := D.R) Ch).grp (rPsymF (R := D.R) Ch).chr Zs).nV t) →
        D.what₂.LL) →ₗ[D.what₂.LL] V0X W Ch sel t.1 Xg (rPsymF (R := D.R) Ch)}
  {Sp : ∀ Zs, SPer ((colM F hX v0 TU Xg xiVal trIv hE ev).face Zs)}
  {R : RestM F hX v0 TU Xg xiVal trIv hE ev Sp ex}
  {hKer : ColTieT T R.extendedDatum X e (colM F hX v0 TU Xg xiVal trIv hE ev)} {hwU : ∀ u, HEq (R.I.wU u) u}
  {hsg : F.Am.σ₀ = D.what₂.embLL} {hH : ColHyp3 W Ch sel v0 TU Xg ∅}

end Pins

end Formalism.L2.DIV.Member

end
