module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyFreeSumIrreducibles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentTrace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimple

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace GlobalTheory.VWeil

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

variable (h) in
abbrev IrrW : Type := {x : WD h // IsIrrWD x}

theorem isIrrWD_mk (a : WDRep h V) : IsIrrWD (WD.mk a) ↔ a.ρ.IsIrreducible := by
  constructor
  · rintro ⟨n, b, hb, hirr⟩
    obtain ⟨e, he, -⟩ := WD.mk_eq_mk.1 hb
    exact IrrDecomp.isIrreducible_of_equiv e he hirr
  · intro hirr
    obtain ⟨e, he, -⟩ := WD.iso_std a
    exact ⟨_, (WD.std a).2, (WD.sound (WD.iso_std _)).symm, IrrDecomp.isIrreducible_of_equiv e he hirr⟩

theorem nontrivial_of_irr {ρ : Representation ℂ (Weil h) V} (hρ : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem N_eq_zero_of_irr (a : WDRep h V) (hirr : a.ρ.IsIrreducible) : a.N = 0 := by
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans (one_lt_normV w)).ne'
  let S : Subrepresentation a.ρ := ⟨LinearMap.ker a.N, fun σ v hv => by
    have h1 := a.comm_apply σ v
    rw [LinearMap.mem_ker.1 hv, map_zero] at h1
    exact LinearMap.mem_ker.2 ((smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ hq))⟩
  rcases hirr.eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hinj : Function.Injective a.N := by
      rw [← LinearMap.ker_eq_bot]
      exact congrArg Subrepresentation.toSubmodule hS
    obtain ⟨m, hm⟩ := a.nilpotent
    have hinj' : Function.Injective (a.N ^ m) := by
      rw [End.coe_pow]; exact hinj.iterate m
    rw [hm] at hinj'
    have := nontrivial_of_irr hirr
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hinj' (a₁ := v) (a₂ := 0) (by simp))
  · exact LinearMap.ker_eq_top.1 (congrArg Subrepresentation.toSubmodule hS)

theorem IrrW.mono0 (z : IrrW h) : z.1.mono0 := by
  obtain ⟨_, n, a, rfl, ha⟩ := z
  exact (WD.monodromyZero_ofWeilDeligneRepClass_iff a).2 (N_eq_zero_of_irr a ha)

theorem IrrW.lpDim_pos (z : IrrW h) : 0 < z.1.lpDim := by
  obtain ⟨_, n, a, rfl, ha⟩ := z
  have := nontrivial_of_irr ha
  show 0 < (WD.mk a).lpDim
  rw [WD.lpDim_mk]
  exact finrank_pos

variable (h) in
def frobCoset (r : ℕ) : Set (Weil h) := {τ | deg τ = -(r : ℤ)}

@[simp] theorem mem_frobCoset {r : ℕ} {τ : Weil h} : τ ∈ frobCoset h r ↔ deg τ = -(r : ℤ) := Iff.rfl

section Artin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Artin

namespace VR

end VR

end GlobalTheory.VWeil
