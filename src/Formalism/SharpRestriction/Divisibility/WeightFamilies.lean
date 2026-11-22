module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataParamsT
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.WeightFamilies

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped ComplexOrder

def rho (D : D7) (j : ℕ) : ℕ := (D.R.sigW j).2

def dP (D : D7) (j : ℕ) : ℕ := 2 * D.R.f * rho D j

def RRv (D : D7) (CR : ℝ) : ℝ := D.host.rdE ^ CR

def PPv (D : D7) (L : SizeData₂ D) (C A : ℝ) : ℝ := C * zBase L ^ A

theorem PPv_rec {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : PPv D L T.CP T.eP = T.PP := by
  unfold PPv
  exact T.PP_eq.symm

def PP0v (D : D7) (L : SizeData₂ D) (C A : ℝ) : ℝ :=
  C * ((D.R.f : ℝ) * (D.R.r : ℝ) + L.sc.L + logdE D + |L.logOm|) ^ A

structure Wt (D : D7) (j : ℕ) where
  aP : D.what₂.Tau → Fin (D.R.sigW j).1 → ℕ
  aM : D.what₂.Tau → Fin (D.R.sigW j).2 → ℕ
  aPlus_antitone : ∀ τ, Antitone (aP τ)
  aM_anti : ∀ τ, Antitone (aM τ)
  n : ℕ
  n_even : Even n

def Wt.size {D : D7} {j : ℕ} (ka : Wt D j) : ℝ :=
  (∑ τ, ((∑ i, (ka.aP τ i : ℝ)) + ∑ i, (ka.aM τ i : ℝ))) +
    (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (ka.n : ℝ) + 1

theorem Wt.one_le_size {D : D7} {j : ℕ} (ka : Wt D j) : 1 ≤ ka.size := by
  unfold Wt.size
  have h1 : 0 ≤ ∑ τ, ((∑ i, (ka.aP τ i : ℝ)) + ∑ i, (ka.aM τ i : ℝ)) :=
    Finset.sum_nonneg fun τ _ => add_nonneg (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _)
      (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _)
  have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (ka.n : ℝ) := by
    positivity
  linarith

def dimY (D : D7) (j : ℕ) : ℕ :=
  D.R.f * ((D.R.sigW j).1 * (D.R.sigW j).2 + (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 +
    (D.R.sigW j).2 * ((D.R.sigW j).2 - 1) / 2)

def Wt.LastPos {D : D7} {j : ℕ} (ka : Wt D j) : Prop :=
  ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → 1 ≤ ka.aP τ i

section Cusp

variable (D : D7) {n : ℕ}

def ev (l x : Fin n → D.host.E) : D.host.E := ∑ i, l i * x i

def dualO (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E) :=
  {l | ∀ x ∈ X, ev D l x ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)}

def dualZ (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E) :=
  {l | ∀ x ∈ X, Algebra.trace ℚ D.host.E (ev D l x) ∈ Set.range (Int.cast : ℤ → ℚ)}

def hform (A : Matrix (Fin n) (Fin n) D.host.E) (l m : Fin n → D.host.E) : D.host.E :=
  ∑ i, ∑ k, l i * A i k * D.host.conj (m k)

def IsHerm (A : Matrix (Fin n) (Fin n) D.host.E) : Prop :=
  ∀ i k, A k i = D.host.conj (A i k)

def PosDefE (A : Matrix (Fin n) (Fin n) D.host.E) : Prop :=
  ∀ l : Fin n → D.host.E, l ≠ 0 → ∀ σ : D.host.E →+* ℂ, 0 < (σ (hform D A l l)).re

def IntOn (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (A : Matrix (Fin n) (Fin n) D.host.E)
    (c : D.host.E) : Prop :=
  ∀ l ∈ dualO D X, ∀ m ∈ dualO D X,
    c * hform D A l m ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)

def ExpoSet (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Matrix (Fin n) (Fin n) D.host.E) :=
  {A | IsHerm D A ∧ PosDefE D A ∧ IntOn D X A (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))}

theorem emb_conj (σ : D.host.E →+* ℂ) (z : D.host.E) : σ (D.host.conj z) = star (σ z) := by
  have hg : D.host.gal D.host.conj = D.R.cc := by
    first
    | exact MulEquiv.apply_symm_apply _ _
    | simp [Formalism.HC.HostRaw.conj]
  exact (D.host.der.conj_iff σ D.host.conj).mpr hg z

def trF (z : D.host.E) : ℝ := ∑ τ, (DV.tauEmb D τ z).re

def c1 (CR T c : ℝ) (j : ℕ) : ℝ :=
  RRv D CR * T * c * (dP D j : ℝ) ^ 2 * (rho D j : ℝ) / 2

end Cusp

section Half

variable {E : Type} [Field E] [NumberField E] {cj : E → E} {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

end Half

structure Prov (D : D7) where

  KO : Type
  [fKO : Field KO]
  [nfKO : NumberField KO]

  eO : 𝓞 KO ≃+* D.what₂.O

  Cusp : (j : ℕ) → Wt D j → Type
  [acgC : ∀ j ka, AddCommGroup (Cusp j ka)]
  [modC : ∀ j ka, Module KO (Cusp j ka)]
  [fdC : ∀ j ka, FiniteDimensional KO (Cusp j ka)]
  [modOC : ∀ j ka, Module (𝓞 KO) (Cusp j ka)]
  [towC : ∀ j ka, IsScalarTower (𝓞 KO) KO (Cusp j ka)]

  Mlat : ∀ j ka, Submodule (𝓞 KO) (Cusp j ka)

  supN : ∀ j ka, (KO →+* ℂ) → Cusp j ka → ℝ
  supN_nonneg : ∀ j ka σ F, 0 ≤ supN j ka σ F
  supN_eq_zero : ∀ j ka σ F, supN j ka σ F = 0 ↔ F = 0
  supN_smul : ∀ j ka σ (a : KO) F, supN j ka σ (a • F) = ‖σ a‖ * supN j ka σ F
  supN_add : ∀ j ka σ F G, supN j ka σ (F + G) ≤ supN j ka σ F + supN j ka σ G

  l2NormAlt : ∀ j ka, (KO →+* ℂ) → Cusp j ka → ℝ
  l2Norm_nonneg_bis : ∀ j ka σ F, 0 ≤ l2NormAlt j ka σ F
  l2Norm_eq_zero_iff : ∀ j ka σ F, l2NormAlt j ka σ F = 0 ↔ F = 0
  l2Norm_smul_alt : ∀ j ka σ (a : KO) F, l2NormAlt j ka σ (a • F) = ‖σ a‖ * l2NormAlt j ka σ F
  l2Norm_add_le' : ∀ j ka σ F G, l2NormAlt j ka σ (F + G) ≤ l2NormAlt j ka σ F + l2NormAlt j ka σ G
  l2Norm_le_supNorm_alt : ∀ j ka σ F, l2NormAlt j ka σ F ≤ supN j ka σ F

  Cu : ℕ → Type

  Xc : ∀ j, Cu j → Submodule (𝓞 D.host.E) (Fin (rho D j) → D.host.E)
  Xc_lat : ∀ j c, Submodule.IsLattice D.host.E (Xc j c)

  FJt : ∀ j (c : Cu j), ExpoSet D (Xc j c) → Wt D j → Type
  [acgF : ∀ j c χ ka, AddCommGroup (FJt j c χ ka)]
  [modF : ∀ j c χ ka, Module KO (FJt j c χ ka)]

  sg : ∀ j (c : Cu j) (χ : ExpoSet D (Xc j c)) (ka : Wt D j), Cusp j ka →ₗ[KO] FJt j c χ ka

attribute [instance] Prov.fKO Prov.nfKO Prov.acgC Prov.modC Prov.fdC Prov.modOC Prov.towC
  Prov.acgF Prov.modF

section Derived

variable {D : D7} (X : Prov D)

def Killed (CR T c : ℝ) {j : ℕ} (cu : X.Cu j) (χ : ExpoSet D (X.Xc j cu)) : Prop :=
  ∃ xi ∈ dualZ D (X.Xc j cu), xi ≠ 0 ∧ trF D (hform D χ.1 xi xi) ≤ c1 D CR T c j

def MggK (CR T c : ℝ) (j : ℕ) (ka : Wt D j) : Submodule X.KO (X.Cusp j ka) :=
  ⨅ (cu : X.Cu j) (χ : ExpoSet D (X.Xc j cu)) (_ : Killed X CR T c cu χ), LinearMap.ker (X.sg j cu χ ka)

def MggIn (CR T c : ℝ) (j : ℕ) (ka : Wt D j) : Submodule (𝓞 X.KO) (X.Mlat j ka) :=
  ((MggK X CR T c j ka).restrictScalars (𝓞 X.KO)).comap (X.Mlat j ka).subtype

abbrev Qm (CR T c : ℝ) (j : ℕ) (ka : Wt D j) : Type :=
  X.Mlat j ka ⧸ MggIn X CR T c j ka

def rhoP (CR T c : ℝ) (j : ℕ) (ka : Wt D j) : ℕ :=
  Module.finrank (𝓞 X.KO) (Qm X CR T c j ka)

def meanLogSup {j : ℕ} {ka : Wt D j} (F : X.Cusp j ka) : ℝ :=
  (∑ σ : X.KO →+* ℂ, Real.log (X.supN j ka σ F)) / (Fintype.card (X.KO →+* ℂ) : ℝ)

theorem meanLogSup_le {j : ℕ} {ka : Wt D j} (F : X.Cusp j ka) {b : ℝ}
    (h : ∀ σ : X.KO →+* ℂ, Real.log (X.supN j ka σ F) ≤ b) : meanLogSup X F ≤ b := by
  unfold meanLogSup
  have hc : (0 : ℝ) < (Fintype.card (X.KO →+* ℂ) : ℝ) := by
    have h0 : 0 < Fintype.card (X.KO →+* ℂ) := by
      first
      | (rw [NumberField.Embeddings.card]; exact Module.finrank_pos)
      | exact Fintype.card_pos
    exact_mod_cast h0
  rw [div_le_iff₀ hc]
  calc (∑ σ : X.KO →+* ℂ, Real.log (X.supN j ka σ F)) ≤ ∑ _σ : X.KO →+* ℂ, b :=
        Finset.sum_le_sum fun σ _ => h σ
    _ = b * (Fintype.card (X.KO →+* ℂ) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

def degO : ℝ := (Module.finrank ℚ X.KO : ℝ)

def rdO : ℝ := |((discr X.KO : ℤ) : ℝ)| ^ (1 / degO X)

def lnN (la : HeightOneSpectrum (𝓞 X.KO)) : ℝ := Real.log (Ideal.absNorm la.asIdeal : ℝ)

def lenAt (la : HeightOneSpectrum (𝓞 X.KO)) (N : Type) [AddCommGroup N] [Module (𝓞 X.KO) N] : ℕ∞ :=
  Module.length (Localization.AtPrime la.asIdeal) (LocalizedModule la.asIdeal.primeCompl N)

def Obound (L : SizeData₂ D) (C A : ℝ) : Prop :=
  Real.log (degO X) ≤ PPv D L C A ∧ Real.log (rdO X) ≤ PPv D L C A

end Derived

section Statements

variable {D : D7}

end Statements

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ProvF Fm)

end Family

section FamilyK

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ProvF Fm)

end FamilyK

theorem one_le_zBase {D : D7} (L : SizeData₂ D) : 1 ≤ zBase L := by
  unfold zBase
  have hL : 1 ≤ L.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact le_of_lt (Real.one_lt_rpow L.sc.one_lt_alt L.sc.eps_pos)
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have h : 1 ≤ D.R.f := by
      unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
      have := D.R.m_le_f
      have := D.R.two_le_m
      omega
    exact_mod_cast h
  have hr : (1 : ℝ) ≤ (D.R.r : ℝ) := by
    have h : 1 ≤ D.R.r := by
      unfold Formalism.BasicNotions.Ranks.r
      have := D.R.two_le_m
      omega
    exact_mod_cast h
  calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
    _ ≤ (D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L := by gcongr

end Formalism.MainNotions.WeightFamilies

end
