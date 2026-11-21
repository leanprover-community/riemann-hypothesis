import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.MatrixKernelDiamondCommutation
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.ChainTwFrA

section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

open Classical in

def cutDat {X : Fields} {a b : ℕ} (σ : X.K →+* ℂ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K) (x : HomE X.E a b) : ℂ :=
  if x ∈ divLat cA (homAt S N N') then σ (Ξ x) else 0

def ThDatCut : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K), A.LaHyp a b S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB →
    (∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) →
      A.thDat S cA cB N N' Ξ =
        thC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' (cA * cB) (cutDat A.σ₀ S cA N N' Ξ) (A.e a b N N')

def ThDatThC : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K), A.LaHyp a b S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB →
    (∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) →
    (∀ x, x ∉ divLat cA (homAt S N N') → Ξ x = 0) →
      A.thDat S cA cB N N' Ξ =
        thC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' (cA * cB) (fun x => A.σ₀ (Ξ x)) (A.e a b N N')

def ThDatRead : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X)
    (i : ℕ) (c : C.cls i) (c' : C.cls (i + 1)) (cA cB : ℕ) (Ξ : HomE X.E (D.R.N i) (D.R.N (i + 1)) → X.K),
    A.LaHyp (D.R.N i) (D.R.N (i + 1)) r.SS → IsSdLat (r.N i c) → IsSdLat (r.N (i + 1) c') → 0 < cA → 0 < cB → r.lev = cA * cB →
    (∀ x, r.Xi i c c' x = A.σ₀ (Ξ x)) →
    (∀ x ∈ divLat cA (homAt r.SS (r.N i c) (r.N (i + 1) c')), ∀ y ∈ mulLat cB (homAt r.SS (r.N i c) (r.N (i + 1) c')), Ξ (x + y) = Ξ x) →
    (∀ x, x ∉ divLat cA (homAt r.SS (r.N i c) (r.N (i + 1) c')) → Ξ x = 0) →
      s.push (A.thDat r.SS cA cB (r.N i c) (r.N (i + 1) c') Ξ) = r.Th s A i c c'

def ThDatReadNat : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (i : ℕ) (c : C.cls i) (c' : C.cls (i + 1)) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E (D.R.N i))) (N' : Submodule (𝓞 X.E) (Sp X.E (D.R.N (i + 1))))
    (Ξ : HomE X.E (D.R.N i) (D.R.N (i + 1)) → X.K),
    (ambOf s B χ cD : Amb X).LaHyp (D.R.N i) (D.R.N (i + 1)) S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB →
    r.SS = S → r.lev = cA * cB → r.N i c = N → r.N (i + 1) c' = N' → (∀ x, r.Xi i c c' x = s.σ₀ (Ξ x)) →
    (∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) →
    (∀ x, x ∉ divLat cA (homAt S N N') → Ξ x = 0) →
      s.push ((ambOf s B χ cD : Amb X).thDat S cA cB N N' Ξ) = r.Th s (ambOf s B χ cD) i c c'

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def ThDatEntry : Prop :=
  ∀ (A : Amb X) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (al : L.β i) (be : L.β (i + 1))
    (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)),
    Pr.Ok → 0 < Pr.T u → L.Ok Ch sel mu cst G m2 → i < m2 → A.LaHyp (R.N i) (R.N (i + 1)) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N p'.deco.1.N (XiEntry Ch sel mu cst L i al be p p') =
        thEntry Ch sel mu cst L (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA i al be p p' (A.e _ _ p.deco.1.N p'.deco.1.N)

def ThDatCpl1 : Prop :=
  ∀ (A : Amb X) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (al : L.β m2)
    (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))),
    Pr.Ok → 0 < Pr.T u → L.Ok Ch sel mu cst G m2 → A.LaHyp (R.N m2) (R.N (m2 + 1)) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p₀.deco.1.N p.deco.1.N (XiCpl1 Ch sel mu cst L m2 al p₀ p Y) =
        thCpl1 Ch sel mu cst L (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA m2 al p₀ p Y (A.e _ _ p₀.deco.1.N p.deco.1.N)

def XiCpl2Adm {u : Pr.Word} (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu) : Prop :=
  (∀ x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N (tilQ sel mu u dd).1.N),
    ∀ y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N (tilQ sel mu u dd).1.N),
      XiCpl2 Ch sel mu cst m2 p Y dd (x + y) = XiCpl2 Ch sel mu cst m2 p Y dd x) ∧
  ∀ x, x ∉ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N (tilQ sel mu u dd).1.N) → XiCpl2 Ch sel mu cst m2 p Y dd x = 0

def ThDatCpl2 : Prop :=
  ∀ (A : Amb X) (m2 : ℕ) (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu),
    0 < Pr.T u → XiCpl2Adm Ch sel mu cst m2 p Y dd → A.LaHyp (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (tilQ sel mu u dd).1.N (XiCpl2 Ch sel mu cst m2 p Y dd) =
        thCpl2 Ch sel mu cst (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA m2 p Y dd (A.e _ _ p.deco.1.N (tilQ sel mu u dd).1.N)

def XiCpl2AdmOf : Prop :=
  ∀ (m2 : ℕ) (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu),
    Pr.Ok → cst.Ok → R.m = m2 + 2 → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → PosT sel mu u → Y ∈ ybSet sel mu cst p.deco.1.N →
      XiCpl2Adm Ch sel mu cst m2 p Y dd

def ThDatCpl2Of : Prop :=
  ∀ (A : Amb X) (m2 : ℕ) (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu),
    Pr.Ok → 0 < Pr.T u → cst.Ok → R.m = m2 + 2 → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → PosT sel mu u → Y ∈ ybSet sel mu cst p.deco.1.N →
    A.LaHyp (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (tilQ sel mu u dd).1.N (XiCpl2 Ch sel mu cst m2 p Y dd) =
        thCpl2 Ch sel mu cst (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA m2 p Y dd (A.e _ _ p.deco.1.N (tilQ sel mu u dd).1.N)

end Chain

def ReadThDat : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X)
    (Pr : Primes X) (Ch : Chars X Pr D.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))
    (G : ChGlob X D.R.m) (v : Pr.Word) (m2 : ℕ), r.IsChain Ch sel mu cst L A.σ₀ v m2 → Pr.Ok → 0 < Pr.T v → L.Ok Ch sel mu cst G m2 →
    (∀ i, i ≤ m2 → A.LaHyp (D.R.N i) (D.R.N (i + 1)) (Sall sel mu v)) →
    ∃ (pt : ∀ i, i ≤ m2 + 1 → C.cls i → ChPt (R := D.R) sel mu v i) (ix : ∀ i, i ≤ m2 → C.cls i → L.β i)
      (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (row : C.cls (m2 + 1 + 1) → Option (RowPt Pr D.R sel mu)),
      (∀ i (hi : i ≤ m2 + 1) c, r.N i c = (pt i hi c).deco.1.N) ∧
      (∀ c', yb c' ∈ ybSet sel mu cst (pt (m2 + 1) le_rfl c').deco.1.N) ∧
      (∀ i (hi : i < m2) c c', r.Th s A i c c' = s.push (A.thDat (Sall sel mu v) (cAof sel mu cst) (cBof sel mu cst v)
        (pt i (by omega) c).deco.1.N (pt (i + 1) (by omega) c').deco.1.N
        (XiEntry Ch sel mu cst L i (ix i hi.le c) (ix (i + 1) hi c') (pt i (by omega) c) (pt (i + 1) (by omega) c')))) ∧
      (∀ c c', r.Th s A m2 c c' = s.push (A.thDat (Sall sel mu v) (cAof sel mu cst) (cBof sel mu cst v)
        (pt m2 (Nat.le_succ _) c).deco.1.N (pt (m2 + 1) le_rfl c').deco.1.N
        (XiCpl1 Ch sel mu cst L m2 (ix m2 le_rfl c) (pt m2 (Nat.le_succ _) c) (pt (m2 + 1) le_rfl c') (yb c')))) ∧
      (∀ c' d, row c' = some d → HEq (r.N (m2 + 1 + 1) c') (tilQ sel mu v d).1.N) ∧
      (∀ c c' d, row c' = some d → HEq (r.Xi (m2 + 1) c c') fun x => A.σ₀ (XiCpl2 Ch sel mu cst m2 (pt (m2 + 1) le_rfl c) (yb c) d x)) ∧
      (∀ i, i ≤ m2 + 1 → ∀ c, r.pin i c) ∧ ∀ c', r.pin (m2 + 1 + 1) c' ↔ ∃ d, row c' = some d

end Formalism.L2.Ker
end
end

section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Row

variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (v : Pr.Word)

open Classical in

def AtRow (d : RowPt Pr R sel mu) (p' : DecoF X.E (R.N R.m) (Pr.vT v) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) : Prop :=
  p'.deco = tilC sel mu v d ∧ ∀ (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)),
    p'.fr ⟨P, hP⟩ = (Sc.Fr.topFrA (R := R) sel mu v (Finset.subset_union_left : Pr.vGs ⊆ rowSG Pr sel mu)
      (fun _ hP => Finset.mem_union_right _ hP)).fr ⟨P, hP⟩ d

def OverRow {j : ℕ} (d : RowPt Pr R sel mu) (p : ChPt (R := R) sel mu v j) : Prop :=
  ∃ p' : DecoF X.E (R.N R.m) (Pr.vT v) Pr.vGs (QE sel (mu : Chr X.F X.E X.K)), HEq p p' ∧ AtRow sel mu v d p'

end Row

section Pin

variable {D : D7} {X : Fields} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}
variable {Pr : Primes X} (Ch : Chars X Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))

def KerRead.TopPinAt (r : KerRead C X) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) (p1 : C.cls (m2 + 1) → ChPt (R := D.R) sel mu v (m2 + 1))
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)) : Prop :=
  (∀ c', r.N (m2 + 1 + 1) c' = (pT c').deco.1.N) ∧
    ∀ c c' x, r.Xi (m2 + 1) c c' x = σ (XiTop Ch sel mu cst (m2 + 1) (p1 c) (yb c) (pT c') x)

def KerRead.TopPin (r : KerRead C X) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) : Prop :=
  ∃ (p1 : C.cls (m2 + 1) → ChPt (R := D.R) sel mu v (m2 + 1)) (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1))))
    (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)),
    (∀ c, r.N (m2 + 1) c = (p1 c).deco.1.N) ∧ (∀ c, yb c ∈ ybSet sel mu cst (p1 c).deco.1.N) ∧ r.TopPinAt Ch sel mu cst σ v m2 p1 yb pT

def KerRead.IsChainTop (r : KerRead C X) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) : Prop :=
  r.SS = Sall sel mu v ∧ r.lev = levC sel mu cst v ∧
  ∃ (pt : ∀ i, i ≤ m2 + 1 → C.cls i → ChPt (R := D.R) sel mu v i) (ix : ∀ i, i ≤ m2 → C.cls i → L.β i)
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)),
    (∀ i (hi : i ≤ m2 + 1) c, r.N i c = (pt i hi c).deco.1.N) ∧
    (∀ c', yb c' ∈ ybSet sel mu cst (pt (m2 + 1) le_rfl c').deco.1.N) ∧
    (∀ i (hi : i < m2) c c' x, r.Xi i c c' x =
      σ (XiEntry Ch sel mu cst L i (ix i hi.le c) (ix (i + 1) hi c') (pt i (by omega) c) (pt (i + 1) (by omega) c') x)) ∧
    (∀ c c' x, r.Xi m2 c c' x =
      σ (XiCpl1 Ch sel mu cst L m2 (ix m2 le_rfl c) (pt m2 (Nat.le_succ _) c) (pt (m2 + 1) le_rfl c') (yb c') x)) ∧
    r.TopPinAt Ch sel mu cst σ v m2 (pt (m2 + 1) le_rfl) yb pT ∧
    (∀ i, i ≤ m2 + 1 → ∀ c, r.pin i c) ∧ ∀ c', r.pin (m2 + 1 + 1) c' ↔ ∃ d, OverRow sel mu v d (pT c')

end Pin

section Stmt

def TopChain : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ), X.Ok → Pr.Ok → cst.Ok → D.R.m = m2 + 2 →
    (∀ w : rowSG Pr sel mu, Pr.piT v ∉ w.1.asIdeal) → r.IsChainTop Ch sel mu cst L σ v m2 → r.IsChain Ch sel mu cst L σ v m2

def TopOfChainTop : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ),
    r.IsChainTop Ch sel mu cst L σ v m2 → r.TopPin Ch sel mu cst σ v m2

def TopRead : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X) (Pr : Primes X)
    (Ch : Chars X Pr D.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) (p1 : C.cls (m2 + 1) → ChPt (R := D.R) sel mu v (m2 + 1))
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)),
    r.SS = Sall sel mu v → r.lev = levC sel mu cst v → (∀ c, r.N (m2 + 1) c = (p1 c).deco.1.N) → r.TopPinAt Ch sel mu cst σ v m2 p1 yb pT →
    ∀ c c', r.Th s A (m2 + 1) c c' =
      s.push (thC (X.embC A.σ₀) A.δ A.d A.sc A.AA (Sall sel mu v) (p1 c).deco.1.N (pT c').deco.1.N (levC sel mu cst v)
        (fun x => σ (XiTop Ch sel mu cst (m2 + 1) (p1 c) (yb c) (pT c') x)) (A.e _ _ (p1 c).deco.1.N (pT c').deco.1.N))

def TopFree : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r r' : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ),
    r.IsChain Ch sel mu cst L σ v m2 → (∀ c', ¬ r.pin (m2 + 1 + 1) c') → r'.SS = r.SS → r'.lev = r.lev → r'.pin = r.pin →
    (∀ i, i ≤ m2 + 1 → r'.N i = r.N i) → (∀ i, i ≤ m2 → r'.Xi i = r.Xi i) → r'.IsChain Ch sel mu cst L σ v m2

def TopRigid : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r r' : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) (p1 : C.cls (m2 + 1) → ChPt (R := D.R) sel mu v (m2 + 1))
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)),
    r.TopPinAt Ch sel mu cst σ v m2 p1 yb pT → r'.TopPinAt Ch sel mu cst σ v m2 p1 yb pT →
    r'.N (m2 + 1 + 1) = r.N (m2 + 1 + 1) ∧ r'.Xi (m2 + 1) = r.Xi (m2 + 1)

def TopSd : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ),
    r.IsChainTop Ch sel mu cst L σ v m2 → ∀ i, i ≤ m2 + 1 + 1 → ∀ c, IsSdLat (r.N i c)

def TopStrict : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ),
    r.IsChain Ch sel mu cst L σ v m2 → (∀ c', ¬ r.pin (m2 + 1 + 1) c') → Nonempty (C.cls (m2 + 1 + 1)) →
    ∃ r' : KerRead C X, r'.IsChain Ch sel mu cst L σ v m2 ∧ ¬ r'.IsChainTop Ch sel mu cst L σ v m2

def XiTopAdm {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) : Prop :=
  (∀ x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N),
    ∀ y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N),
      XiTop Ch sel mu cst i p Y p' (x + y) = XiTop Ch sel mu cst i p Y p' x) ∧
  ∀ x, x ∉ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst i p Y p' x = 0

def XiTopAdmRef : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)), X.Ok → Pr.Ok → cst.Ok → R.m = m2 + 2 →
    QE sel (mu : Chr X.F X.E X.K) = ∅ → Y ∈ ybSet sel mu cst p.deco.1.N → XiTopAdm Ch sel mu cst (m2 + 1) p Y p'

def ReadThDatTop : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X) (Pr : Primes X)
    (Ch : Chars X Pr D.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (v : Pr.Word) (m2 : ℕ) (p1 : C.cls (m2 + 1) → ChPt (R := D.R) sel mu v (m2 + 1))
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)),
    r.SS = Sall sel mu v → r.lev = levC sel mu cst v → (∀ c, r.N (m2 + 1) c = (p1 c).deco.1.N) → r.TopPinAt Ch sel mu cst A.σ₀ v m2 p1 yb pT →
    0 < Pr.T v → A.LaHyp (D.R.N (m2 + 1)) (D.R.N (m2 + 1 + 1)) (Sall sel mu v) →
    ∀ c c', XiTopAdm Ch sel mu cst (m2 + 1) (p1 c) (yb c) (pT c') →
      r.Th s A (m2 + 1) c c' = s.push (A.thDat (Sall sel mu v) (cAof sel mu cst) (cBof sel mu cst v) (p1 c).deco.1.N (pT c').deco.1.N
        (XiTop Ch sel mu cst (m2 + 1) (p1 c) (yb c) (pT c')))

def XiTopNe : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word), X.Ok → Pr.Ok → cst.Ok → R.m = 2 →
    QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w : Pr.vGs, Pr.piT u ∉ w.1.asIdeal) → cst.sharp = false → (∀ P a, cst.psi P a ≠ 0) →
    ∃ (p : ChPt (R := R) sel mu u (0 + 1)) (Y : Set (Sp X.E (R.N (0 + 1)))) (p' : ChPt (R := R) sel mu u (0 + 1 + 1))
      (x : HomE X.E (R.N (0 + 1)) (R.N (0 + 1 + 1))), Y ∈ ybSet sel mu cst p.deco.1.N ∧ XiTop Ch sel mu cst (0 + 1) p Y p' x ≠ 0

end Stmt

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.TopPinned {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ, (t.rd u μ).IsChainTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.seam.σ₀ (t.word u) t.m2

def KerEntTied.TopInt {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ (c : (D.chTw u μ).cls (t.m2 + 1)) (c' : (D.chTw u μ).cls (t.m2 + 1 + 1)), ¬ (t.rd u μ).pin (t.m2 + 1 + 1) c' →
    ∀ x, IntOff (t.O u μ).S ((t.rd u μ).Xi (t.m2 + 1) c c' x)

end Comparison₂

def HypFreeOfTop : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt → t.HypFree

end Formalism.L2.Ker
end
end
