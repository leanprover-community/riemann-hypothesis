module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

def comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  ∑ u ∈ c.support, c u • heisO ψ S T u f

def IsFinComb {S T : HSp D} (c : WO S T →₀ ℂ) : Prop := ∀ u ∈ c.support, u.map (infPart D) = 0

def biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S c (fun u' => comb ψ S A' c' (C u') v) u

structure IsBiVac (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (LA : Set (Fin A.rank → D.host.E))
    (LS : Set (Fin S.rank → D.host.E)) (LA' : Set (Fin A'.rank → D.host.E)) (C : WO A S → WO S A' → ℂ) : Prop where
  cont : Continuous fun p : WO A S × WO S A' => C p.1 p.2
  left : ∀ v, IsThetaFunO ψ A S (fun u => C u v) ∧ IsLatVac (heisO ψ A S) (latO A S LA LS fun _ => True) fun u => C u v
  right : ∀ u, IsThetaFunO ψ S A' (C u) ∧ IsLatVac (heisO ψ S A') (latO S A' LS LA' fun _ => True) (C u)

def biLift {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ)
    (C : WO A S → WO S A' → ℂ) (h₂ : GA D A') : ℂ :=
  ∫ h₁ in vS.𝓕, (∫ h₀ in vA.𝓕, φ h₀ * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 ∂vA.μ) ∂vS.μ

def HasCen (A : HSp D) (χ : GA D A → ℂ) (φ : GA D A → ℂ) : Prop :=
  ∀ z ∈ GinfC A, z ∈ Subgroup.center (GA D A) → ∀ h, φ (h * z) = χ z * φ h

def InCell {V : HSp D} (R : Subgroup (GA D V)) (t : GA D V) (J : Set (GA D V)) (h : GA D V) : Prop :=
  ∃ r ∈ R, ∃ a ∈ GinfC V, ∃ k ∈ J, h = r * a * t * k

structure DefSp (V : HSp D) where
  s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  vol : Vol V

structure DefSp.Is {V : HSp D} (x : DefSp V) : Prop where
  sig : V.SigOK
  cpt : CoCpt V
  cart : ∀ τ, IsCartanInv (gramAt D V τ) (x.s τ)
  pm : ∀ τ, x.s τ = 1 ∨ x.s τ = -1
  onb : ∀ τ, ∃ p, IsONBasis (gramAt D V τ) (x.s τ) (x.B τ) p
  sd : IsSelfDualC V x.L

structure KerDat (S T : HSp D) where
  om : Om S T
  vac : WO S T → ℂ
  c : WO S T →₀ ℂ

structure KerDat.Is (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T) :
    Prop where
  weil : ∃ χS χT, IsWeilDatumO ψ S T χS χT k.om
  vac : IsVacO ψ θ S T x.s y.s x.L y.L k.vac
  fin : IsFinComb k.c

def KerDat.pt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T)
    (P : PolF D T.rank S.rank) : WO S T → ℂ :=
  pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T k.c k.vac) P

def KerDat.lift (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T)
    (P : PolF D T.rank S.rank) (φ : GA D S → ℂ) : GA D T → ℂ :=
  liftT k.om x.vol.μ x.vol.𝓕 φ (k.pt ψ θ x y P)

structure BesAt (V A : HSp D) (ρ : ℕ) where
  V₀ : HSp D
  L : HSp D
  d : HypDec V V₀ ρ
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  cpt : CoCpt A
  vN : VolN d

@[reducible] def BesAt.lev {V A : HSp D} {ρ : ℕ} (b : BesAt V A ρ) (vA : Vol A) : BesLev D ρ :=
  ⟨V, b.V₀, A, b.L, b.d, b.o, b.ζ, b.line, b.cpt, vA, b.vN⟩

structure JacAt (W W₀ : HSp D) (ρ : ℕ) where
  d : HypDec W W₀ ρ
  cpt : CoCpt W₀
  vN : VolN d

@[reducible] def JacAt.lev {W W₀ : HSp D} {ρ : ℕ} (b : JacAt W W₀ ρ) (v0 : Vol W₀) : JacLev D ρ :=
  ⟨W, W₀, b.d, b.cpt, v0, b.vN⟩

open GlobalTheory.ChainOnto (Com PiLocalization₂)

structure StAt (V : HSp D) where
  par : D.what₂.Tau → SPar
  M : DSModel V par
  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  β : GL (Fin V.rank) (Lev.EAf D)
  L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank
  ν : Measure (GA D V)
  fd : Set (GA D V)

@[reducible] def StAt.st {V : HSp D} (a : StAt V) : PiLocalization₂ D := ⟨V, a.par, a.M, a.Λ, a.β, a.L, a.ν, a.fd⟩

theorem idx_step {j σ m : ℕ} (h : j + 2 * (σ + 1) + 2 = m) : j + 1 + 1 + 2 * σ + 2 = m := by omega

namespace Dat

variable {u : D.what₂.Word} (d : Dat D u)

end Dat

end GlobalTheory.SeeSaw

end
