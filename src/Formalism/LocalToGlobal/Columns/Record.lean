module

public import Mathlib
public import Formalism.LocalRingCardinality.DataForms
public import Formalism.LocalToGlobal.Columns.ToHLat
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.Columns.AtTOwedC
public import Formalism.LocalToGlobal.Columns.AtTOwedS
public import Formalism.LocalToGlobal.Columns.AdjointFrobeniusPreservesRamified
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.RecLevel
public import Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions
public import Formalism.LocalToGlobal.Columns.DGamAut
public import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber
import Formalism.LocalToGlobal.Columns.HeckeSpCount

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace Ev

variable {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

end Ev

end GSD

namespace GSD.Ev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

end GSD.Ev

section Fr

variable {X : Fields} {n : ℕ}

variable {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

end Fr

section ModP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

abbrev modP (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) : Type :=
  ↥M ⧸ (P.asIdeal • (⊤ : Submodule (𝓞 E) ↥M))

def modP.mk (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) : ↥M →ₗ[𝓞 E] modP P M :=
  Submodule.mkQ _

open Classical in
def modP.ext (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (g : modP P M → 𝓞 E ⧸ P.asIdeal) (y : Sp E n) :
    𝓞 E ⧸ P.asIdeal :=
  if h : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M then
    Ring.inverse (Ideal.Quotient.mk P.asIdeal h.choose) * g (modP.mk P M ⟨h.choose • y, h.choose_spec.2⟩)
  else 0

end ModP

section LevT

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

namespace DecoSet

end DecoSet

end LevT

section MoveLemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem modP.mk_osmul (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (g : Module.Dual (𝓞 E ⧸ P.asIdeal) (modP P M))
    (a : 𝓞 E) (x : ↥M) : g (modP.mk P M (a • x)) = Ideal.Quotient.mk P.asIdeal a * g (modP.mk P M x) := by
  have e : a • modP.mk P M x = (Ideal.Quotient.mk P.asIdeal a) • modP.mk P M x :=
    (algebraMap_smul (𝓞 E ⧸ P.asIdeal) a (modP.mk P M x)).symm
  rw [map_smul, e, map_smul, smul_eq_mul]

theorem modP.ext_spec (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (g : Module.Dual (𝓞 E ⧸ P.asIdeal) (modP P M))
    (y : Sp E n) {s : 𝓞 E} (hs : s ∉ P.asIdeal) (hy : s • y ∈ M) :
    Ideal.Quotient.mk P.asIdeal s * modP.ext P M g y = g (modP.mk P M ⟨s • y, hy⟩) := by
  have hex : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M := ⟨s, hs, hy⟩
  unfold modP.ext
  rw [dite_eq_left hex]
  have htP : hex.choose ∉ P.asIdeal := hex.choose_spec.1
  have htM : hex.choose • y ∈ M := hex.choose_spec.2
  have key : Ideal.Quotient.mk P.asIdeal hex.choose * g (modP.mk P M ⟨s • y, hy⟩) =
      Ideal.Quotient.mk P.asIdeal s * g (modP.mk P M ⟨hex.choose • y, htM⟩) := by
    rw [← modP.mk_osmul, ← modP.mk_osmul]
    congr 2
    exact Subtype.ext (smul_comm hex.choose s y)
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hu : IsUnit (Ideal.Quotient.mk P.asIdeal hex.choose) :=
    isUnit_iff_ne_zero.mpr fun h0 => htP (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  calc Ideal.Quotient.mk P.asIdeal s * (Ring.inverse (Ideal.Quotient.mk P.asIdeal hex.choose) *
        g (modP.mk P M ⟨hex.choose • y, htM⟩))
      = Ring.inverse (Ideal.Quotient.mk P.asIdeal hex.choose) *
        (Ideal.Quotient.mk P.asIdeal s * g (modP.mk P M ⟨hex.choose • y, htM⟩)) := by ring
    _ = Ring.inverse (Ideal.Quotient.mk P.asIdeal hex.choose) *
        (Ideal.Quotient.mk P.asIdeal hex.choose * g (modP.mk P M ⟨s • y, hy⟩)) := by rw [key]
    _ = g (modP.mk P M ⟨s • y, hy⟩) := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

theorem modP.ext_of_mem (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (g : Module.Dual (𝓞 E ⧸ P.asIdeal) (modP P M))
    (x : ↥M) : modP.ext P M g x.1 = g (modP.mk P M x) := by
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have h := modP.ext_spec P M g x.1 h1 (by rw [one_smul]; exact x.2)
  rw [map_one, one_mul] at h
  rw [h]
  congr 2
  exact Subtype.ext (one_smul _ _)

theorem modP.ext_funAt (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (g : Module.Dual (𝓞 E ⧸ P.asIdeal) (modP P M)) :
    FunAt P M (modP.ext P M g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨s, hs, hsx⟩ := (mem_locP P M x).1 hx
    obtain ⟨t, ht, hty⟩ := (mem_locP P M y).1 hy
    have hst : s * t ∉ P.asIdeal := fun h => (P.isPrime.mem_or_mem h).elim hs ht
    have h1 : (s * t) • x ∈ M := by rw [mul_comm, mul_smul]; exact M.smul_mem t hsx
    have h2 : (s * t) • y ∈ M := by rw [mul_smul]; exact M.smul_mem s hty
    have h3 : (s * t) • (x + y) ∈ M := by rw [smul_add]; exact M.add_mem h1 h2
    apply mul_left_cancel₀ (mk_ne_zero hst)
    rw [mul_add, modP.ext_spec P M g _ hst h3, modP.ext_spec P M g _ hst h1, modP.ext_spec P M g _ hst h2, ← map_add (f := _), ← map_add (f := _)]
    congr 2
    exact Subtype.ext (smul_add _ _ _)
  · intro a x hx
    obtain ⟨s, hs, hsx⟩ := (mem_locP P M x).1 hx
    have h1 : s • a • x ∈ M := by rw [smul_comm]; exact M.smul_mem a hsx
    apply mul_left_cancel₀ (mk_ne_zero hs)
    rw [modP.ext_spec P M g _ hs h1, mul_left_comm, modP.ext_spec P M g _ hs hsx, ← modP.mk_osmul]
    congr 2
    exact Subtype.ext (smul_comm _ _ _)
  · intro x hx
    unfold modP.ext
    rw [dite_eq_right fun h => hx ((mem_locP P M x).2 h)]

namespace DecoSet

end DecoSet

end MoveLemmas

section FormT

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

variable (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end FormT

section Mem

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

@[reducible] def stepGSD (u : Pr.Word) (j : ℕ) : GSD X.K := formGSD (colVal W u j (Pr.vT u) Pr.vGs) (Λ j)

end Mem

section Glob

variable {X : Fields} {Pr : Primes X} {R : Ranks}

namespace DetChr

variable {m : ℕ} (Dc : DetChr X m)

end DetChr

attribute [instance] ChainGlob.ιFin

variable {W : Wts X Pr.Word R} {σ₀ : X.K →+* ℂ}

end Glob

section Mem2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

set_option linter.unusedVariables false in
@[irreducible] def recDGamAll (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) {σ₀ : X.K →+* ℂ} (hX : X.Ok) (G : ChainGlob W σ₀) : ℕ := dGamAut X R

variable {W Λ}

section Levs

variable {X : Fields} {Pr : Primes X} {R : Ranks}

end Levs

@[reducible] def stepH (hX : X.Ok) (u : Pr.Word) (j : ℕ) : HLat X.K :=
  (stepGSD W Λ u j).toH (stepOk W Λ hX u j) (stepGSD W Λ u j).intDel

end Mem2

section Xp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

@[reducible] def rowGSD : GSD X.K := formGSD (rowVal W SG') ΛM

@[reducible] def ptGSD : GSD X.K :=
  formGSD (roundPk X W.sgTrue fun d : DecoSet (E := X.E) (n := R.N R.m - 1) (ST := ∅) (SG := SG') => d.1.N) ΛM.inv

@[reducible] def ptH (hX : X.Ok) : HLat X.K := (ptGSD W ΛM).toH (ptOk W ΛM hX) (ptGSD W ΛM).intDel

variable {W ΛM}

def tilR (u : Pr.Word) (d : DecoSet (E := X.E) (n := R.N R.m - 1) (ST := ∅) (SG := SG')) : DecoSet (E := X.E) (n := R.N R.m) (ST := Pr.vT u) (SG := Pr.vGs) :=
  (DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).res hSG

variable {Λ}

end Xp

section Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}

end Ker

section Fam

variable {K : Type} [Field K] [NumberField K] [StarRing K]

@[reducible] def cplGSD {S : GSD K} (Y : Cpl S) : GSD K where
  G := S.G
  D := Y.Pts
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  ρ := S.ρ
  Nab p := S.Nab p.1.1
  Del p := S.Del p.1.1

variable {X : Fields} {R : Ranks}

end Fam

section NonDeg

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}

end NonDeg

section Ram

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}

end Ram

section All

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') {ΛM : LevFam X.E X.K (R.N R.m - 1) SG'}

end All

section Mink

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}

variable {σ₀ : X.K →+* ℂ}

end Mink

section FrmMink

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoF X.E n ST SG Q)) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)

end FrmMink

section TwMinkS

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {σ₀ : X.K →+* ℂ}

end TwMinkS

end Formalism.L2.Col
