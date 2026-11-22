module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Core

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

variable (L n) in
def CongConj : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (N : ℕ), 0 < N → ∃ N' : ℕ, 0 < N' ∧
    ∀ κ, Formalism.L2.NG.Cong L n N' κ → Formalism.L2.NG.Cong L n N (h⁻¹ * κ * h)

def IsTypeVec (J' : Set (Formalism.AUTREP.GAf L n)) (χ' : Formalism.AUTREP.GAf L n → ℂ) (f : Formalism.AUTREP.GAf L n → ℂ) : Prop :=
  ∀ κ ∈ J', Formalism.L2.NG.rt L n κ f = χ' κ • f

def heckeG {ι : Type} (s : Finset ι) (γ : ι → Formalism.AUTREP.GAf L n) :
    (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] (Formalism.AUTREP.GAf L n → ℂ) :=
  ∑ i ∈ s, Formalism.L2.NG.rt L n (γ i)

end Core

section CoreProofs

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem rt_apply (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) (x : Formalism.AUTREP.GAf L n) :
    Formalism.L2.NG.rt L n h f x = f (x * h) := rfl

theorem rt_rt (g h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) :
    Formalism.L2.NG.rt L n g (Formalism.L2.NG.rt L n h f) = Formalism.L2.NG.rt L n (g * h) f := by
  funext x
  rw [rt_apply, rt_apply, rt_apply, mul_assoc]

theorem rt_one (f : Formalism.AUTREP.GAf L n → ℂ) : Formalism.L2.NG.rt L n 1 f = f := by
  funext x
  rw [rt_apply, mul_one]

theorem heckeG_apply {ι : Type} (s : Finset ι) (γ : ι → Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) :
    heckeG s γ f = ∑ i ∈ s, Formalism.L2.NG.rt L n (γ i) f := by
  simp [heckeG]

end CoreProofs

section Conc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHost (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ)

structure RowPsi where
  ψ : Formalism.AUTREP.GAf D.host.E n →* GA D V
  inj : Function.Injective ψ
  into : ∀ h, ψ h ∈ GfC V
  onto : ∀ g ∈ GfC V, ∃ h, ψ h = g

variable {V n}

open Classical in
def pre (P : RowPsi V n) (γ : GA D V) : Formalism.AUTREP.GAf D.host.E n :=
  if h : ∃ x, P.ψ x = γ then h.choose else 1

def LevOK (P : RowPsi V n) (J : Set (GA D V)) (χ : GA D V → ℂ) : Prop :=
  ∃ N0 : ℕ, 0 < N0 ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N0 κ → P.ψ κ ∈ J ∧ χ (P.ψ κ) = 1

def Hecke₃ (P : RowPsi V n) (R : Finset (GA D V)) :
    (Formalism.AUTREP.GAf D.host.E n → ℂ) →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E n → ℂ) :=
  heckeG R (pre P)

variable {Sp : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

end Conc

section ConcProofs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHost' (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ}
variable {Sp : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
variable {M : Mult.DSModel V Sp} {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
variable {e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)}

theorem mult_lev {T : Mult.MMap M} (hT : T ∈ Mult.Mult θ M J χ) : ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  intro v k hk g
  induction hT using Submodule.span_induction with
  | mem x hx => exact hx.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy]
    ring
  | smul a x _ hx =>
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx]
    ring

theorem pre_spec (P : RowPsi V n) {γ : GA D V} (hγ : γ ∈ GfC V) : P.ψ (pre P γ) = γ := by
  unfold pre
  rw [dite_eq_left (P.onto γ hγ)]
  exact (P.onto γ hγ).choose_spec

end ConcProofs

end Formalism.IndefR.principalLevelFrame
