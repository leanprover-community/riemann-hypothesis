import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

structure JDat (k r : ℕ) (Wp Wq : Type) where
  H : Type
  [h1 : NormedAddCommGroup H]
  [h2 : InnerProductSpace ℂ H]
  [h3 : CompleteSpace H]
  σ : Mx k r → (H →L[ℂ] H)
  w0 : H
  l : H → Wp
  l' : H → Wq

attribute [instance] JDat.h1 JDat.h2 JDat.h3

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

namespace JDat

def deg (μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : JDat k r Wp Wq) : ℝ := PI.BesselPeriodGGP.fdegH μG A.σ A.w0

def scal (μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : JDat k r Wp Wq) : ℝ :=
  A.deg μG / (‖A.l A.w0‖ ^ 2 * ‖A.l' A.w0‖ ^ 2)

def coef (μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : JDat k r Wp Wq) (g : B.Mat k r) : Wq →L[ℂ] Wp :=
  ((A.scal μG : ℝ) : ℂ) • (innerSL ℂ (A.l' A.w0)).smulRight (⟪A.w0, A.σ g A.w0⟫_ℂ • A.l A.w0)

variable [CompleteSpace Wp] [CompleteSpace Wq]

def Good (Bs : B.RealPlaceData k r Wp Wq) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (u u' : Fin k → ℝ) (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : JDat k r Wp Wq) : Prop :=
  Side k r ε lam h A.σ A.w0 Bs.z Formalism.QuantumDeterminants.cStd u Bs.π Bs.μW Bs.μN Bs.μG νq ∧
  Side k r ε lam h A.σ A.w0 Bs.z' Formalism.QuantumDeterminants.cStd u' Bs.π' Bs.μW' Bs.μN Bs.μG νq' ∧
  PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) Bs.z (Formalism.QuantumDeterminants.psi k r Bs.z Formalism.QuantumDeterminants.cStd) A.σ Bs.π A.l ∧
  PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) Bs.z' (Formalism.QuantumDeterminants.psi k r Bs.z' Formalism.QuantumDeterminants.cStd) A.σ Bs.π' A.l' ∧
  (∀ x ∈ DDsp A.σ A.w0, ∀ y ∈ DDsp A.σ A.w0,
    be Bs.z Formalism.QuantumDeterminants.cStd Bs.π A.σ Bs.μW Bs.μN x y = (innerSL ℂ (A.l y)).smulRight (A.l x)) ∧
  (∀ x ∈ DDsp A.σ A.w0, ∀ y ∈ DDsp A.σ A.w0,
    be Bs.z' Formalism.QuantumDeterminants.cStd Bs.π' A.σ Bs.μW' Bs.μN x y = (innerSL ℂ (A.l' y)).smulRight (A.l' x))

end JDat


theorem coef_apply (μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : JDat k r Wp Wq) (g : B.Mat k r) (x : Wq) :
    A.coef μG g x = (((A.scal μG : ℝ) : ℂ) * (⟪A.l' A.w0, x⟫_ℂ * ⟪A.w0, A.σ g A.w0⟫_ℂ)) • A.l A.w0 := by
  show ((A.scal μG : ℝ) : ℂ) • (⟪A.l' A.w0, x⟫_ℂ • (⟪A.w0, A.σ g A.w0⟫_ℂ • A.l A.w0)) = _
  rw [smul_smul, smul_smul, mul_assoc]


def lamOf {n : ℕ} (sh : ℝ) (μ : Fin n → ℤ) : Fin n → ℝ := fun i => (μ i : ℝ) + sh

structure JFam (k r : ℕ) (Wp Wq : Type) where
  ε : Fin (2 * r + k + 1) → Bool
  sh : ℝ
  h : ℝ
  u : Fin k → ℝ
  u' : Fin k → ℝ
  νq : Measure (Formalism.QuantumDeterminants.Mt k r)
  νq' : Measure (Formalism.QuantumDeterminants.Mt k r)
  A : (Fin (2 * r + k + 1) → ℤ) → JDat k r Wp Wq

namespace JFam

open Classical in

def J (Bs : B.RealPlaceData k r Wp Wq) (F : JFam k r Wp Wq) (μ : Fin (2 * r + k + 1) → ℤ) : B.Mat k r → (Wq →L[ℂ] Wp) :=
  if Formalism.QuantumDeterminants.IsHCParam (lamOf F.sh μ) then (F.A μ).coef Bs.μG else 0



variable [CompleteSpace Wp] [CompleteSpace Wq]

def Good (Bs : B.RealPlaceData k r Wp Wq) (F : JFam k r Wp Wq) (lam0 : Fin (2 * r + k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Formalism.QuantumDeterminants.IsHCParam (lamOf F.sh μ) →
    (F.A μ).Good Bs F.ε (lamOf F.sh μ) F.h F.u F.u' F.νq F.νq'

end JFam

def pieriDataOfFamily {P : M.Par} [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ)
    (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) (c0 q0 : ℕ) (H : ℝ) :
    PieriExpansionData P Wp Wq where
  n := 2 * P.r + P.k + 1
  J := F.J p.T.base
  lam := lam0
  tau := tau
  c0 := c0
  q0 := q0
  H := H

def JmuPin : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (u u' : Fin k → ℝ) (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r))
    (A : JDat k r Wp Wq),
    A.Good Bs ε lam h u u' νq νq' → A.l A.w0 ≠ 0 → A.l' A.w0 ≠ 0 →
    ∀ γ ∈ JF.Om k r Bs.z Bs.z',
      B.JF Bs (A.coef Bs.μG) γ = ((A.deg Bs.μG : ℝ) : ℂ) • Mop Bs.μG A.σ A.w0 A.l A.l' γ

theorem exists_good (hDD : DDFormOne) (hI : Inputs) [CompleteSpace Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wq]
    [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (u u' : Fin k → ℝ) (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r))
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (hs : Side k r ε lam h σ w0 Bs.z Formalism.QuantumDeterminants.cStd u Bs.π Bs.μW Bs.μN Bs.μG νq)
    (hs' : Side k r ε lam h σ w0 Bs.z' Formalism.QuantumDeterminants.cStd u' Bs.π' Bs.μW' Bs.μN Bs.μG νq') :
    ∃ (l : H → Wp) (l' : H → Wq), (JDat.mk H σ w0 l l' : JDat k r Wp Wq).Good Bs ε lam h u u' νq νq' := by
  obtain ⟨l, hl, hbe, -⟩ := hDD hI k r ε lam h H σ w0 Wp Bs.z _ u Bs.π Bs.μW Bs.μN Bs.μG νq hs
  obtain ⟨l', hl', hbe', -⟩ := hDD hI k r ε lam h H σ w0 Wq Bs.z' _ u' Bs.π' Bs.μW' Bs.μN Bs.μG νq' hs'
  exact ⟨l, l', hs, hs', hl, hl', fun x hx y hy => (hbe x hx y hy).2, fun x hx y hy => (hbe' x hx y hy).2⟩

end

end Formalism.FourierDecayAlt.P.CutBP.Jmu
