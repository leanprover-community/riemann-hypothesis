module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.S.LocalSplitGroups

open NumberField IsDedekindDomain Formalism.MainNotions.S ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : Formalism.BasicNotions.D7)

abbrev PlF : Type := HeightOneSpectrum (𝓞 D.host.F)

variable {D : Formalism.BasicNotions.D7}

def gpart (p : PlF D) : ℕ :=
  if Loc.resChar p = D.host.g 0 then D.host.g 0
  else if Loc.resChar p = D.host.g 1 then D.host.g 1 else 1

def uP (p : PlF D) : ℚ := (gpart p : ℚ) / (Lat.gS D : ℚ)

def qE (p : PlF D) : (D.s.atP p).Ep :=
  match (D.s.atP p).split with
  | some sg => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp)
  | none => 1

def twist (p : PlF D) (s : ℕ) (x : (D.s.atP p).Ep) : (D.s.atP p).Ep :=
  match (D.s.atP p).split with
  | some sg => sg.e.symm ((sg.e x).1, (-1) ^ s * (sg.e x).2)
  | none => x

def nu (r i j : ℕ) : ℕ := 2 * (r + 1) - i - j

def tMod (δ : ∀ p, (D.s.atP p).Fp) (p : PlF D) (ν s : ℕ) (t : D.host.E) : (D.s.atP p).Ep :=
  Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ ν) *
    twist p s ((D.s.atP p).ιE t) * Ring.inverse (qE p)

def tau0 (p : PlF D) (T T' : ℕ) : (D.s.atP p).Ep :=
  match (D.s.atP p).split with
  | some sg => sg.e.symm (-(T : (D.s.atP p).Fp), (T' : (D.s.atP p).Fp)) * Ring.inverse (qE p)
  | none => 0

def blkMod (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (a s : ℕ) (t : D.host.E) : (D.s.atP p).Ep :=
  tMod δ p (nu D.R.rS a (a + s - 1)) s t -
    (if a + s - 1 = D.R.rS + 1 ∧ s = 1 then tau0 p T T' else 0)

def nSh {A : Type} [Ring A] (c : A) : ℕ :=
  if hc : ∃ n : Fin 3, IsUnit (c + (((n : Fin 3) : ℕ) : A)) then ((hc.choose : Fin 3) : ℕ) else 0

def blkTop (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (a s : ℕ) (t : D.host.E) : (D.s.atP p).Ep :=
  if a + s - 1 = D.R.rS + 1 ∧ s = 1 then
    blkMod δ T T' p a s t + ((nSh (blkMod δ T T' p a s t) : ℕ) : (D.s.atP p).Ep)
  else blkMod δ T T' p a s t

def mapBlocks {A B : Type} (f : ℕ → ℕ → A → B) : ℕ → List (A × ℕ) → List (B × ℕ)
  | _, [] => []
  | a, (t, s) :: rest => (f a s t, s) :: mapBlocks f (a + s) rest

def modBlocks {A B : Type} [Monoid B] (f : ℕ → ℕ → A → B) : ℕ → List (A × ℕ) → Option (List (Bˣ × ℕ+))
  | _, [] => some []
  | a, (t, s) :: rest =>
    if h : IsUnit (f a s t) ∧ 0 < s then
      (modBlocks f (a + s) rest).map (fun l => (h.1.unit, ⟨s, h.2⟩) :: l)
    else none

def modPt (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) {n : ℕ} (w : Point D.host.E n) :
    Option (Loc.Pt (D.s.atP p).Ep n) :=
  match modBlocks (blkTop δ T T' p) 1 w.1 with
  | none => none
  | some l => if h : (l.map (fun b => (b.2 : ℕ))).sum = n then some ⟨l, h⟩ else none

def modMat (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) {n : ℕ} (w : Point D.host.E n) :
    Matrix (Fin n) (Fin n) (D.s.atP p).Ep :=
  fun a b => ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) a.val b.val

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

def locK (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (n : ℕ) (w w' : Point D.host.E n) : ℂ :=
  match modPt δ T T' p w, modPt δ T T' p w' with
  | some a, some b => (M p).Kk n a b
  | _, _ => 0

def Dmin {n : ℕ} (w : Point D.host.E n) (l : ℕ) : D.host.E :=
  if hl : l ≤ n then ((ptMat w).submatrix (Fin.castLE hl) (Fin.castLE hl)).det else 0

def zetaOf (w : Point D.host.E (D.R.rS + 1)) : D.host.E := Dmin w (D.R.rS + 1) / Dmin w D.R.rS

def kind (w : Point D.host.E (D.R.rS + 1)) : Option D.host.E :=
  if Dmin w D.R.rS = 0 then none else some (zetaOf w)

def dfac (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : ℂ :=
  match (D.s.atP p).split, w.1.getLast? with
  | some _, some (t, 2) => (M p).psiR (tau0 p T T' * Ring.inverse (blkMod δ T T' p D.R.rS 2 t))
  | _, _ => 1

def KtopP (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w w' : Point D.host.E (D.R.rS + 1)) : ℂ :=
  dfac M δ T T' p w * locK M δ T T' p (D.R.rS + 1) w w' * starRingEnd ℂ (dfac M δ T T' p w')

def KtopG (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)) : ℂ :=
  if kind w = kind w' then ∏ᶠ p, KtopP M δ T T' p w w' else 0

def Gpt (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : D.host.E :=
  Dmin w (D.R.rS + 1) * D.conjF (Dmin w (D.R.rS + 1)) -
    (T : D.host.E) * T' * (Dmin w D.R.rS * D.conjF (Dmin w D.R.rS))

def TotPos (x : D.host.E) : Prop := ∀ τ : D.what₂.Tau, 0 < (D.host.emb (D.eTau τ) x).re

def n0 (c : ℝ) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : ℝ :=
  c * (Real.sqrt |((Algebra.norm ℚ (Gpt T T' w / ((Lat.gS D : D.host.E) ^ D.R.m)) : ℚ) : ℝ)|) ^ (D.R.k - 1)

def gdd (a b : ℤ) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  FractionalIdeal.spanSingleton _ ((Lat.gS D : D.host.E) ^ a) *
    ((D.host.ddE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ^ b)

def La (δ : ∀ p, (D.s.atP p).Fp) (ν s : ℕ) : Set D.host.E :=
  {t | ∀ p, tMod δ p ν s t ∈ (M p).R}

def LaP (ν s : ℕ) : Set D.host.E :=
  {x | x ∈ gdd (D := D) (-1) (-(ν : ℤ)) ∧ x - (-1) ^ s * D.conjF x ∈ gdd (D := D) 0 (-(ν : ℤ))}

def frFac (δ : ∀ p, (D.s.atP p).Fp) (p : PlF D) (a : Fin (D.R.rS + 1)) : (D.s.atP p).Ep :=
  Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
    (D.R.rS - a.val))

attribute [instance] TermLoc.acg TermLoc.mod

def clsOf {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) E) : Option (M.Cls m) :=
  if h : (∀ a b, Z a b ∈ M.R) ∧ IsUnit Z.det then
    some (Quotient.mk (M.isoSetoid m) ⟨Matrix.of fun a b => ⟨Z a b, h.1 a b⟩, by
      have : (Matrix.of fun a b => (⟨Z a b, h.1 a b⟩ : M.R)).map M.R.subtype = Z := rfl
      rw [this]; exact h.2⟩)
  else none

def cornerSh (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) :
    (D.s.atP p).Ep :=
  if Dmin w D.R.rS = 0 then 0
  else ((nSh (blkMod δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep)

section Datum

variable {Y : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word}

end Datum

def BBtop (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (c : Option ((M p).Cls D.R.rS)) : ℂ :=
  match modPt δ T T' p w, c with
  | some a, some c => dfac M δ T T' p w * (M p).BB a c
  | _, _ => 0

def BBG (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1))
    (κ : Option D.host.E) (th : ∀ p, Option ((M p).Cls D.R.rS)) : ℂ :=
  if kind w = κ then ∏ᶠ p, BBtop M δ T T' p w (th p) else 0

def autG (th : ∀ p, Option ((M p).Cls D.R.rS)) : ℂ :=
  ∏ᶠ p, (match th p with
    | some c => (((M p).nAut c : ℕ) : ℂ)
    | none => 1)

def Agree (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) : Prop :=
  (M p).OK ∧ δ p ≠ 0 ∧ (M p).L.cj = (D.s.atP p).cj ∧ (M p).L.O = (D.s.atP p).O ∧
  (∀ y, (M p).L.psi0 y = (D.s.atP p).psiE (-(y * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹))) ∧
  (match (M p).split, (D.s.atP p).split with
    | none, none => True
    | some g, some sg => g.e = sg.e ∧ g.q = sg.q
    | _, _ => False)

def Kglob (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ)
    (n : ℕ) (w w' : Point D.host.E n) : ℂ :=
  if h : n = D.R.rS + 1 then KtopG M δ T T' (h ▸ w) (h ▸ w')
  else ∏ᶠ p, locK M δ T T' p n w w'

end Formalism.MainNotions.S.LocalSplitGroups
