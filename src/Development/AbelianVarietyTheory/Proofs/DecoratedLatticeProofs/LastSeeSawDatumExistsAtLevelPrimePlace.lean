module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceAlongLineDatumOverVacuumSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeesawDatumEqLatticePairOverVacuumStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.LastSeeSawDatum

section Helpers

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem comb_apply' {S T : HSp D} (c : WO S T →₀ ℂ) (g : WO S T → ℂ) (u : WO S T) :
    comb ψ S T c g u = ∑ x ∈ c.support, c x * (ψ (symplOH S T u x) * g (u + x)) := by
  simp only [comb, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul]

theorem isThetaFunO_add' {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := {
  quasi γ w := by simp only [Pi.add_apply]; rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hUo', hU'⟩ := hg.level
    refine ⟨U ⊓ U', hUo.inter hUo', fun u hu hi => ?_⟩
    funext w
    have h1 := congrFun (hU u hu.1 hi) w
    have h2 := congrFun (hU' u hu.2 hi) w
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w) }

theorem heisO_smul' {S T : HSp D} (u : WO S T) (r : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (r • f) = r • heisO ψ S T u f := by
  funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem heisO_add' {S T : HSp D} (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := by
  funext w; simp only [heisO, Pi.add_apply]; ring

theorem heisO_zero' {S T : HSp D} (u : WO S T) : heisO ψ S T u (0 : WO S T → ℂ) = 0 := by
  funext w; simp only [heisO, Pi.zero_apply, mul_zero]

theorem isThetaFunO_zero' (S T : HSp D) : IsThetaFunO ψ S T (0 : WO S T → ℂ) := {
  quasi γ w := by simp only [Pi.zero_apply, mul_zero]
  level := ⟨⊤, isOpen_univ, fun u _ _ => heisO_zero' u⟩
  cont := continuous_const
  smooth k L hL hfin w := by simp only [Pi.zero_apply]; exact contDiff_const }

theorem isThetaFunO_smul' {S T : HSp D} (r : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (r • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    exact ⟨U, hUo, fun u hu hi => by rw [heisO_smul', hU u hu hi]⟩
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := by
    simp only [Pi.smul_apply, smul_eq_mul]; exact contDiff_const.mul (hf.smooth k L hL hfin w) }

variable {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}

theorem vac_zero : Vac ψ S T LS LT P 0 :=
  ⟨isThetaFunO_zero' S T, fun u _ => heisO_zero' _, fun e _ u _ _ => heisO_zero' _⟩

theorem vac_add {f g : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) (hg : Vac ψ S T LS LT P g) :
    Vac ψ S T LS LT P (f + g) :=
  ⟨isThetaFunO_add' hf.1 hg.1, fun u hu => by rw [heisO_add', hf.2.1 u hu, hg.2.1 u hu],
    fun e he u hu hu' => by rw [heisO_add', hf.2.2 e he u hu hu', hg.2.2 e he u hu hu']⟩

theorem vac_smul (r : ℂ) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT P (r • f) :=
  ⟨isThetaFunO_smul' r hf.1, fun u hu => by rw [heisO_smul', hf.2.1 u hu],
    fun e he u hu hu' => by rw [heisO_smul', hf.2.2 e he u hu hu']⟩

theorem vac_sum {ι : Type} (s : Finset ι) (r : ι → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ i ∈ s, Vac ψ S T LS LT P (f i)) : Vac ψ S T LS LT P (∑ i ∈ s, r i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (vac_zero : Vac ψ S T LS LT P 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact vac_add (vac_smul _ (h a (Finset.mem_insert_self a s))) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem comb_smul_fun (c : WO S T →₀ ℂ) (r : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (r • f) = r • comb ψ S T c f := by
  funext u
  simp only [comb_apply', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem comb_sum_fun {ι : Type} (c : WO S T →₀ ℂ) (s : Finset ι) (r : ι → ℂ) (f : ι → WO S T → ℂ) :
    comb ψ S T c (∑ i ∈ s, r i • f i) = ∑ i ∈ s, r i • comb ψ S T c (f i) := by
  funext u
  simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

theorem comb_swap {A S X : HSp D} (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ) (G : WO A S → WO S X → ℂ)
    (u : WO A S) (x : WO S X) :
    comb ψ S X c' (fun x' => comb ψ A S c (fun u' => G u' x') u) x =
      comb ψ A S c (fun u' => comb ψ S X c' (G u') x) u := by
  simp only [comb_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Helpers

end GlobalTheory.LastSeeSawDatum
