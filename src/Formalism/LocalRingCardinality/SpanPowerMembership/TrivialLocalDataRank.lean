import Formalism.LocalRingCardinality.SpanPowerMembership.TrivialColumnsRamifiedTop
import Formalism.LocalRingCardinality.SpanPowerMembership.GPlacesExampleNatAct

noncomputable section

namespace Formalism.BasicNotions.Examples₂.ND

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Rows

variable (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R0.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)

abbrev rows1 : Rows.Data R0 :=
  { toyRowsOfNumberField LL embLL P Tau hTau Dst sha hsha cg hcg with
    Mu := fun _ => ℂ
    instMu := fun _ => inferInstance
    instMui := fun _ => inferInstance
    instMuf := fun _ => inferInstance
    perCol := fun _ _ _ _ => 0
    Bu := fun _ _ _ => 0 }

end Rows

section Div

variable (K : Type) [Field K] [NumberField K] [StarRing K]

abbrev div1 : DivData K Unit :=
  { toyZeroLatticeDatum K with
    Nu := fun _ => oneHLat K
    Bk := fun _ => 0
    h := fun _ => 0
    HH := sFrame (fun _ : Unit => oneHLat K) (fun _ => 0) + (zeroHLat K).muMax
    HH_ge := le_refl _ }


end Div

section S

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E) {Word Tau : Type} [Subsingleton Word] (hc : Word → Tau → HCParam R)

abbrev sData1 (Del : ℚ) (hDel : 0 < Del)
    (hgap : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l + 1 < R.k - 1),
      (hc w τ).v ⟨l, by omega⟩ - (hc w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (hlet : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l < R.k - 2),
      (hc w τ).u ⟨l + 1, by omega⟩ = (hc w τ).v ⟨l, by omega⟩ - 1 / 2)
    (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc :=
  { toySData sig hc Del hDel hgap hlet loc with
    Cu := fun _ => ℂ
    cuN := fun _ => inferInstance
    cuI := fun _ => inferInstance
    cuF := fun _ => inferInstance
    Pu := fun _ => 0
    aTerm := fun _ _ t => t.elim }

end S

section G

open Formalism.MainNotions.G

def gLevel1 (p : ℕ) : Level (emptyPlaces p) where
  Γ := Unit
  act := fun v => v.elim0
  χ := 1



def trivialLocalData (p : ℕ) : GAtP p where
  O := ℤ_[3]
  Kf := ℚ_[3]
  P := emptyPlaces p
  comp := Unit
  lev := fun _ => gLevel1 p
  e := 0


end G

end Formalism.BasicNotions.Examples₂.ND
