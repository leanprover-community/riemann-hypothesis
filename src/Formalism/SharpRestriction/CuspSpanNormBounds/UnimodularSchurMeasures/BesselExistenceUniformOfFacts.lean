import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.FlagUnipotentLattices.ThirdHeightFromSecond

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

section Grp

variable {k r : ℕ}

theorem unitary_group_mul_mem {a b : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']

theorem cayley_conj_mem_diagonal_model {ε : Fin (2 * r + k + 1) → Bool} {P a : Mat k r} (hP : IsCayleyU k r ε P)
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    P * a * P⁻¹ ∈ UJset ε ∧ P⁻¹ * (P * a * P⁻¹) * P = a := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  constructor
  · show (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε
    calc (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹)
        = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hH, ha']
      _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2]; simp
  · calc P⁻¹ * (P * a * P⁻¹) * P = (P⁻¹ * P) * a * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = a := by rw [h1]; simp

theorem discrete_series_map_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) {a b : Mat k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ (a * b) = (σ a).comp (σ b) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have hrep := hDS.2.2.1.1.2 _ (cayley_conj_mem_diagonal_model hP ha).1 _ (cayley_conj_mem_diagonal_model hP hb).1
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have e1 : P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = a * b := by
    calc P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
      _ = a * b := by rw [h1]; simp
  simp only [e1, (cayley_conj_mem_diagonal_model hP ha).2, (cayley_conj_mem_diagonal_model hP hb).2] at hrep
  exact hrep

end Grp


structure BData : Type 1 where
  k : ℕ
  r : ℕ
  z : Fin (2 * r + k + 1) → ℂ
  c : Fin r → ℂ
  u : Fin k → ℝ
  v : Fin (k - 1) → ℝ
  b : Fin (2 * r + 2) → ℝ
  H : Type
  [hN : NormedAddCommGroup H]
  [hI : InnerProductSpace ℂ H]
  [hC : CompleteSpace H]
  σ : Mat k r → (H →L[ℂ] H)
  Vp : Type
  [vN : NormedAddCommGroup Vp]
  [vI : InnerProductSpace ℂ Vp]
  [vF : FiniteDimensional ℂ Vp]
  π : Mat k r → (Vp →L[ℂ] Vp)
  w : H
  μG : Measure (Formalism.QuantumDeterminants.Mt k r)
  μS : Measure (Formalism.QuantumDeterminants.Mt k r)
  ν : Measure (Formalism.QuantumDeterminants.Mt k r)

attribute [instance] BData.hN BData.hI BData.hC BData.vN BData.vI BData.vF

namespace BData

variable (X : BData)

abbrev G : Set (Mat X.k X.r) := Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk X.k X.r)

abbrev ψ : Mat X.k X.r → ℂ := psiGen X.k X.r X.z X.c

abbrev e : Mat X.k X.r → ℂ := eFun X.μG X.σ X.w

def Hyp : Prop :=
  RealPlaceNumericalSetting X.k X.r X.z X.c X.u X.v X.b ∧ IsDSHpk X.k X.r (eps48 X.k X.r) (lam48 X.k X.r X.v X.b) X.σ ∧
    IsHCTypeW X.k X.r X.z X.u X.π ∧ IsLowUnitH X.k X.r (eps48 X.k X.r) (lam48 X.k X.r X.v X.b) X.σ X.w ∧
    IsHaarOn X.G X.μG ∧ IsHaarOn (Formalism.QuantumDeterminants.Sset X.k X.r X.z) X.μS ∧ IsQuotMeas X.μG X.μS X.ν

def IsSol (W : Mat X.k X.r → X.Vp) : Prop :=
  AEStronglyMeasurable (fun x => W (Matrix.of x)) X.μG ∧ AEStronglyMeasurable (fun x => W (Matrix.of x)) X.ν ∧
    IsSPsiEquiv X.z X.ψ X.π W ∧ l2SG X.ν W < ⊤ ∧ l2SG X.ν W ≠ 0 ∧
    ∀ x ∈ X.G, rconv X.μG X.e W x = W x

def IsFun (B : X.H → X.Vp) : Prop :=
  IsBesselMapSm X.z X.ψ X.σ X.π B ∧ HasOrdLe X.k X.r (rk48 X.k X.r ^ 2 / 2 + 1) X.σ B ∧
    ∃ x ∈ smoothVecs (k := X.k) (r := X.r) X.σ, B x ≠ 0

def W' (B : X.H → X.Vp) : Mat X.k X.r → X.Vp := fun g => B (X.σ g X.w)

def Φ (B : X.H → X.Vp) (χ : Mat X.k X.r → ℝ) : Mat X.k X.r → X.Vp := fun g => (χ g : ℂ) • X.W' B g

def Wf (B : X.H → X.Vp) (χ : Mat X.k X.r → ℝ) : Mat X.k X.r → X.Vp := rconv X.μG X.e (X.Φ B χ)

def OrbitSmooth : Prop := ∀ g ∈ X.G, X.σ g X.w ∈ smoothVecs (k := X.k) (r := X.r) X.σ

def OrbitNZ (B : X.H → X.Vp) : Prop := ∃ g ∈ X.G, B (X.σ g X.w) ≠ 0

def IsCut (B : X.H → X.Vp) (χ : Mat X.k X.r → ℝ) : Prop :=
  (∀ g, 0 ≤ χ g) ∧ (∀ s ∈ Formalism.QuantumDeterminants.Sset X.k X.r X.z, ∀ g ∈ X.G, χ (s * g) = χ g) ∧
    AEStronglyMeasurable (fun x => X.Φ B χ (Matrix.of x)) X.μG ∧ (∃ M : ℝ, ∀ g ∈ X.G, ‖X.Φ B χ g‖ ≤ M) ∧
    ((∫⁻ x, (‖X.Φ B χ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂X.ν) < ⊤ ∧
      ∃ Ω : Set (Mat X.k X.r), IsCompact Ω ∧
        ∀ g ∈ X.G, χ g ≠ 0 → ∃ s ∈ Formalism.QuantumDeterminants.Sset X.k X.r X.z, s * g ∈ Ω) ∧
    0 < ∫ x, χ (Matrix.of x) * ‖X.W' B (Matrix.of x)‖ ^ 2 ∂X.ν

def CutStep (B : X.H → X.Vp) : Prop := X.OrbitNZ B → ∃ χ, X.IsCut B χ

def ConvolutionKernelIntegrable : Prop := Integrable (fun x => X.e (Matrix.of x)) X.μG

def IdemStep (B : X.H → X.Vp) : Prop :=
  ∀ χ, X.IsCut B χ → ∀ x ∈ X.G, rconv X.μG X.e (X.Wf B χ) x = X.Wf B χ x

def ProjectionSquareIntegrable (B : X.H → X.Vp) : Prop :=
  ∀ χ, X.IsCut B χ → AEStronglyMeasurable (fun x => X.Wf B χ (Matrix.of x)) X.μG ∧
    AEStronglyMeasurable (fun x => X.Wf B χ (Matrix.of x)) X.ν ∧ l2SG X.ν (X.Wf B χ) < ⊤

def Pairing (B : X.H → X.Vp) : Prop :=
  ∀ χ, X.IsCut B χ →
    ∫ x, ⟪X.W' B (Matrix.of x), X.Wf B χ (Matrix.of x)⟫_ℂ ∂X.ν =
      ∫ x, ⟪X.W' B (Matrix.of x), (χ (Matrix.of x) : ℂ) • X.W' B (Matrix.of x)⟫_ℂ ∂X.ν

variable {X}

theorem W'_equiv (hX : X.Hyp) {B : X.H → X.Vp} (hB : X.IsFun B) (hs : X.OrbitSmooth) :
    IsSPsiEquiv X.z X.ψ X.π (X.W' B) := by
  intro h hh m hm g hg
  have hhm : h * m ∈ X.G := unitary_group_mul_mem hh.1 hm.1
  unfold W'
  rw [discrete_series_map_mul hX.2.1 hhm hg]
  exact hB.1.2.2.1 h hh m hm _ (hs g hg)

theorem Φ_equiv (hX : X.Hyp) {B : X.H → X.Vp} (hB : X.IsFun B) (hs : X.OrbitSmooth) {χ : Mat X.k X.r → ℝ}
    (hχ : X.IsCut B χ) : IsSPsiEquiv X.z X.ψ X.π (X.Φ B χ) := by
  intro h hh m hm g hg
  unfold Φ
  rw [hχ.2.1 (h * m) ⟨h, hh, m, hm, rfl⟩ g hg, W'_equiv hX hB hs h hh m hm g hg, map_smul, smul_comm]

theorem mp_left (hX : X.Hyp) {g : Mat X.k X.r} (hg : g ∈ X.G) :
    MeasurePreserving (Formalism.QuantumDeterminants.lmulM g) X.μG X.μG := by
  refine ⟨?_, hX.2.2.2.2.1.2.2.2 g hg⟩
  unfold Formalism.QuantumDeterminants.lmulM
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  have h0 : Measurable fun x : Formalism.QuantumDeterminants.Mt X.k X.r => x l j := by fun_prop
  exact h0.const_mul _

theorem ae_mem (hX : X.Hyp) : ∀ᵐ y ∂X.μG, Matrix.of y ∈ X.G := by
  have := hX.2.2.2.2.1.2.2.1
  rw [ae_iff]
  exact this

theorem integrable_conv (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ) (he : X.ConvolutionKernelIntegrable)
    {g : Mat X.k X.r} (hg : g ∈ X.G) :
    Integrable (fun y => X.e (Matrix.of y) • X.Φ B χ (g * Matrix.of y)) X.μG := by
  obtain ⟨M, hM⟩ := hχ.2.2.2.1
  have hm : AEStronglyMeasurable (fun y => X.Φ B χ (g * Matrix.of y)) X.μG :=
    hχ.2.2.1.comp_measurePreserving (mp_left hX hg)
  refine he.smul_bdd M hm ?_
  filter_upwards [ae_mem hX] with y hy
  exact hM _ (unitary_group_mul_mem hg hy)




end BData


def BesselExistenceFacts : Prop :=
  ∀ X : BData, X.Hyp → ∀ B : X.H → X.Vp, X.IsFun B →
    X.OrbitSmooth ∧ X.OrbitNZ B ∧ X.CutStep B ∧ X.ConvolutionKernelIntegrable ∧ X.IdemStep B ∧ X.ProjectionSquareIntegrable B ∧ X.Pairing B





end Formalism.MainNotions.LeviCoordinates

end
