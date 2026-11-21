import Mathlib

section
noncomputable section

open Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Jp

abbrev Ix (n : ℕ) : Type := Fin n ⊕ Fin n

variable {n : ℕ}

section Ring

variable {R : Type} [CommRing R]

def nU (y : Matrix (Fin n) (Fin n) R) : GL (Ix n) R where
  val := fromBlocks 1 y 0 1
  inv := fromBlocks 1 (-y) 0 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

def pM (a d : GL (Fin n) R) (b : Matrix (Fin n) (Fin n) R) : GL (Ix n) R where
  val := fromBlocks a.1 b 0 d.1
  inv := fromBlocks (a⁻¹).1 (-((a⁻¹).1 * b * (d⁻¹).1)) 0 (d⁻¹).1
  val_inv := by
    simp [fromBlocks_multiply, ← fromBlocks_one, ← Matrix.mul_assoc]
  inv_val := by
    simp [fromBlocks_multiply, ← fromBlocks_one, Matrix.mul_assoc]

def lowerLeftBlock (g : GL (Ix n) R) : Matrix (Fin n) (Fin n) R := g.1.toBlocks₂₁

def dBlk (g : GL (Ix n) R) : Matrix (Fin n) (Fin n) R := g.1.toBlocks₂₂

end Ring

def iD {k : Type} [Field k] (g : GL (Ix n) k) : ℕ := n - (dBlk g).rank

section Local

variable {O : Type} [CommRing O] [IsLocalRing O] {L : Type} [Field L] [Algebra O L]

abbrev inL : GL (Ix n) O →* GL (Ix n) L := Matrix.GeneralLinearGroup.map (algebraMap O L)

abbrev resK : GL (Ix n) O →* GL (Ix n) (IsLocalRing.ResidueField O) :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue O)

def scM (w : Lˣ) : GL (Fin n) L := Units.map (Matrix.scalar (Fin n) : L →+* Matrix (Fin n) (Fin n) L).toMonoidHom w

def tauM (w : Lˣ) : GL (Ix n) L := pM 1 (scM w) 0

def IsHgt (nv : Lˣ →* ℝ≥0) (h : GL (Ix n) L → ℝ≥0) : Prop :=
  ∀ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ : GL (Ix n) O),
    h (pM a d b * inL κ) = nv (Matrix.GeneralLinearGroup.det a) / nv (Matrix.GeneralLinearGroup.det d)

def NvOK [Fintype (IsLocalRing.ResidueField O)] (nv : Lˣ →* ℝ≥0) (w : Lˣ) : Prop :=
  (∀ u : Oˣ, nv (Units.map (algebraMap O L).toMonoidHom u) = 1) ∧
    nv w = ((Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0))⁻¹

def IsRed (w : Lˣ) (κ : GL (Ix n) O) (hb : GL (Ix n) (IsLocalRing.ResidueField O)) : Prop :=
  ∃ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ' : GL (Ix n) O),
    inL κ * tauM w = pM a d b * inL κ' ∧ resK κ' = hb

def Gam2 (ϖ : O) : Subgroup (GL (Ix n) O) :=
  (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}))).ker

instance (ϖ : O) : (Gam2 (n := n) ϖ).Normal := by unfold Gam2; infer_instance

def avgK (ϖ : O) (φ : GL (Ix n) O → ℂ) : ℂ :=
  (Nat.card (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) : ℂ)⁻¹ * ∑ᶠ u : GL (Ix n) O ⧸ Gam2 (n := n) ϖ, φ (Quotient.out u)

def liftM (ℓ : IsLocalRing.ResidueField O → O) (Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)) :
    Matrix (Fin n) (Fin n) L := (Y.map ℓ).map (algebraMap O L)

end Local

def coY {k : Type} [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (β Y : Matrix (Fin n) (Fin n) k) : ℂ :=
  ((Fintype.card k : ℂ) ^ (n * n))⁻¹ * (starRingEnd ℂ) (ψ₀ (Matrix.trace (Y * β)))

end GlobalTheory.CompanionTheory.Jp

end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Jp

def sumG {k : Type} [Field k] {n : ℕ} (f : GL (Ix n) k → ℂ) : ℂ := ∑ᶠ g, f g

def JpIw : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (g : GL (Ix n) L), ∃ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ : GL (Ix n) O),
      g = pM a d b * inL κ

def JpHgt : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ nv : Lˣ →* ℝ≥0, NvOK (O := O) nv w → ∀ h : GL (Ix n) L → ℝ≥0, IsHgt (O := O) nv h → ∀ κ : GL (Ix n) O,
      h (inL κ * (tauM w)⁻¹) = (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ (2 * iD (resK κ)) /
        (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ n

def JpUnif : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O),
    Irreducible ϖ → ∀ (X : Type) [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] (ρ : X →* GL (Ix n) O), Function.Surjective ρ →
    MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) O))) → ∀ φ : GL (Ix n) O → ℂ,
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∫ x, φ (ρ x) ∂ν = avgK ϖ φ

def JpCmp : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ Ψ : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ, (∀ a d b g, Ψ (pM a d b * g) = Ψ g) →
    ∀ T : GL (Ix n) O → GL (Ix n) (IsLocalRing.ResidueField O), (∀ κ, IsRed (O := O) w κ (T κ)) →
      avgK ϖ (fun κ => Ψ (T κ)) =
        sumG (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ g) /
          sumG (fun g : GL (Ix n) (IsLocalRing.ResidueField O) =>
            (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g))

def JpPos : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (n r m : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 → ∀ β : Matrix (Fin n) (Fin n) k, β.rank = r →
    r ≤ m → ∃ x : ℝ, 0 < x ∧
      sumG (fun g : GL (Ix n) k => ∑ Y : Matrix (Fin n) (Fin n) k,
        (Fintype.card k : ℂ) ^ (r * iD g) * coY ψ₀ β Y * (Fintype.card k : ℂ) ^ (m * iD (g * nU Y))) = x

def JpCondition : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n r t : ℕ), r + t = n → 1 ≤ r →
    ∀ ψ₀ : AddChar (IsLocalRing.ResidueField O) ℂ, ψ₀ ≠ 1 →
    ∀ β : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), β.rank = r →
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ c ((t : ℂ) / 2) ≠ 0 ∧
      ∀ (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
      ∀ ℓ : IsLocalRing.ResidueField O → O, (∀ a, IsLocalRing.residue O (ℓ a) = a) →
      ∀ nv : Lˣ →* ℝ≥0, NvOK (O := O) nv w → ∀ h : GL (Ix n) L → ℝ≥0, IsHgt (O := O) nv h →
      ∀ (X : Type) [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X) [IsProbabilityMeasure ν]
        [ν.IsMulLeftInvariant] (ρ : X →* GL (Ix n) O), Function.Surjective ρ →
        MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) O))) → ∀ z : ℂ,
        ∫ x, ∑ Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), coY ψ₀ β Y *
          (((h (inL (ρ x) * nU ((w⁻¹ : Lˣ).1 • liftM (L := L) ℓ Y)) : ℝ≥0) : ℝ) : ℂ) ^ (z + (n : ℂ) / 2) ∂ν = c z

end GlobalTheory.CompanionTheory.Jp

end
end
