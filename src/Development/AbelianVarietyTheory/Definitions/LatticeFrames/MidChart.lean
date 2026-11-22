module

public import Mathlib
public import Formalism.LocalToGlobal.HermitianForms.BothSym
public import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

abbrev EF (D : D7) : Type := D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F

section Gen
variable (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

def finM (g : GA D V) : Matrix (Fin n) (Fin n) (EF D) :=
  ((mt V g).map (toEAf D)).reindex (finCongr hn) (finCongr hn)

def infM (g : GA D V) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  (compAt θ τ (mt V g)).reindex (finCongr hn) (finCongr hn)

variable {J : Matrix (Fin n) (Fin n) D.host.E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) {cl : Type}
  (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def IsDec (x : Matrix (Fin n) (Fin n) (EF D)) (p : cl × GL (Fin n) D.host.E × S.U) : Prop :=
  p.2.1 ∈ UJ (sigD D : D.host.E →+* D.host.E) J ∧
    x = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) p.2.1 * (yc p.1).1 * p.2.2.1).1

def atFr {G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (φ : Frames G → ℂ) (y : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  if h : ∀ τ, IsUnit (y τ).det then φ ⟨y, h⟩ else 0

def rdS (ψ : cl → Frames (gramC J (embT D)) → ℂ) (y : Frames (gramC J (embT D))) (g : GA D V) : ℂ :=
  if h : ∃ p, IsDec S yc (finM V hn g) p then
    ((S.chi h.choose.2.2 : ℂˣ) : ℂ) * atFr (ψ h.choose.1) fun τ =>
      atInf (embT D) ((h.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * y.1 τ
  else 0

end Gen

structure Chart (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) where

  cl : Type

  inc : cl → (D.mem u).C.cls i

  K : LevelChart D (D.mem u).A.T (badG D) i hi (fun c : cl => (D.mem u).C.stab i (inc c)) (fun c => clsCrd D u i hi (inc c))

  eY : (D.mem u).C.Y i ≃ Fr D i hi

variable {u : D.what₂.Word}

def Chart.rd {i : ℕ} {hi : i ≤ D.R.m} (Q : Chart D u i hi) (θ : InfFam D)
    (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) (y : (D.mem u).C.Y i) : GA D (D.sp.X i) → ℂ :=
  rdS θ (D.sp.X i) (rankN D i hi) Q.K.lev Q.K.y (fun c z => ψ (Q.inc c) (Q.eY.symm z)) (Q.eY y)

section Sym
variable {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)

end Sym

end GlobalTheory.AdForm
