import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def admitted (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ) : Prop :=
  Measurable θ ∧ (∀ p, 0 ≤ θ p) ∧ ∀ p, D.inSS p → ∫ x, θ (actR γ (Matrix.of x) p) ∂μR = 1

def orbI (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (θ : B.SS k r → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    Wq →L[ℂ] Wp :=
  ∫ p, θ p • (B.xiTau D (1, 1) p • B.rho D p F γ) ∂D.μSS

def zc (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : ℕ :=
  (Finset.univ.filter fun l : Fin (r + 2) => Dmin k r D.z D.z' γ l = 0).card

end

def StepAdm (CV : ℕ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r)),
    B.IsHaarOn (Rset γ) μR →
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ →
    ∃ θ : B.SS k r → ℝ, admitted D γ μR θ ∧
      Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS

def ZeroUpTo (CV m : ℕ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
    B.IsHaarOn (Rset γ) μR →
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    (∀ g ∈ bigPos D, B.JF D F' g = 0) →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    orbI D γ θ F' = 0

def StepBig (CV : ℕ) : Prop := ZeroUpTo CV 0

def StepDown (CV : ℕ) : Prop := ∀ m : ℕ, ZeroUpTo CV m → ZeroUpTo CV (m + 1)

end PI.UnitaryGroupMassFormula.DLm
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def HasRun (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (i j : ℕ) : Prop :=
  1 ≤ i ∧ i < j ∧ j ≤ r + 1 ∧
    (∀ l : Fin (r + 2), l.val + 1 = i → Dmin k r D.z D.z' γ l ≠ 0) ∧
    (∀ l : Fin (r + 2), i ≤ l.val → l.val < j → Dmin k r D.z D.z' γ l = 0) ∧
    (∀ l : Fin (r + 2), l.val = j → Dmin k r D.z D.z' γ l ≠ 0)

def Hyps (CV : ℕ) (D : B.RealPlaceData k r Wp Wq) (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  1 ≤ r ∧ 0 < ε ∧ (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A ∧ mmV CV r ≤ mm ∧ B.InCC A mm F' ∧
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) ∧ (∀ g ∈ bigPos D, B.JF D F' g = 0)

end

def RunExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r),
    0 < Gf k r D.z D.z' γ → 1 ≤ zc D γ → ∃ i j : ℕ, HasRun D γ i j

def DownJ (CV : ℕ) : Prop :=
  StepAdm CV → ∀ m : ℕ, ZeroUpTo CV m →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ) (i j : ℕ),
    B.IsHaarOn (Rset γ) μR → Hyps CV D A ε mm F' →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → HasRun D γ i j → j ≤ r → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    orbI D γ θ F' = 0

def DownTop (CV : ℕ) : Prop :=
  StepAdm CV → ∀ m : ℕ, ZeroUpTo CV m →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ) (i : ℕ),
    B.IsHaarOn (Rset γ) μR → Hyps CV D A ε mm F' →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → HasRun D γ i (r + 1) → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    orbI D γ θ F' = 0

def AdmExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (μR : Measure (Mt k r)),
    B.IsHaarOn (Rset γ) μR → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → ∃ θ : B.SS k r → ℝ, admitted D γ μR θ

def AdmConv (CV : ℕ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ),
    B.IsHaarOn (Rset γ) μR →
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS

def BigTheta : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
    B.IsHaarOn (Rset γ) μR → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ = 0 → admitted D γ μR θ →
    ∃ c : ℝ, 0 < c ∧ ∀ p, D.inSS p → θ p = c

def BigOf (CV : ℕ) : Prop := BigTheta → B.JtauOne → StepBig CV

theorem stepDown_of (CV : ℕ) (hR : RunExists) (hJ : DownJ CV) (hT : DownTop CV) (hA : StepAdm CV) :
    StepDown CV := by
  intro m ih k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ μR θ hH hr hε hA' hmm hF hs hJ0 hrel hG hz hθ hi
  by_cases h0 : zc D γ = 0
  · exact ih k r Wp Wq D A ε mm F' γ μR θ hH hr hε hA' hmm hF hs hJ0 hrel hG (by omega) hθ hi
  · obtain ⟨i, j, hij⟩ := hR k r Wp Wq D γ hG (by omega)
    have hy : Hyps CV D A ε mm F' := ⟨hr, hε, hA', hmm, hF, hs, hJ0⟩
    rcases Nat.lt_or_ge j (r + 1) with hj | hj
    · exact hJ hA m ih k r Wp Wq D A ε mm F' γ μR θ i j hH hy hrel hG hz hij (by omega) hθ hi
    · have hjr : j = r + 1 := le_antisymm hij.2.2.1 hj
      subst hjr
      exact hT hA m ih k r Wp Wq D A ε mm F' γ μR θ i hH hy hrel hG hz hij hθ hi

end PI.UnitaryGroupMassFormula.DLm
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

structure TopModel where
  V : Type
  [ng : NormedAddCommGroup V]
  [ns : NormedSpace ℂ V]
  [cs : CompleteSpace V]

attribute [instance] TopModel.ng TopModel.ns TopModel.cs

def TopDensity (C₂ C CV : ℕ) : Prop :=
  StepAdm CV → ∀ m : ℕ, ZeroUpTo CV m →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ) (i : ℕ),
    B.IsHaarOn (Rset γ) μR → Hyps CV D A ε mm F' →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → HasRun D γ i (r + 1) → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    ∃ (β : ℂ) (p m' : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (M : TopModel)
      (Φ0 : G.Mat (p + (m' + 1 + 1)) → M.V) (e : ℕ → ℝ) (K Cp : ℝ) (P : Seminorm ℂ M.V) (D' z₀ : ℂ),
      β ≠ 0 ∧ (∀ a, d a ≠ 0) ∧ p + (m' + 1 + 1) = r + 1 ∧ D' ≠ 0 ∧
      z₀ ∈ G.rootSet (m' + 2) ((-1) ^ (m' + 3) * D') ∧ 0 ≤ Cp ∧ (∀ v, P v ≤ Cp * ‖v‖) ∧
      U.DecayAll (C₂ * (m' + 2) ^ 2) e K Φ0 ∧
      (∀ j ≤ C₂ * (m' + 2) ^ 2,
        (A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j)) / (5 * ((r : ℝ) + 1))
          - (C : ℝ) * (r : ℝ) ^ 2 ≤ e j / (5 * ((r : ℝ) + 1))) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ t c : ℂ, t ≠ 0 → ‖t‖ < δ → c * t ^ (m' + 1) = D' →
        P (G.OmBlock β (m' + 1) (U.PhiTop β σ d Φ0) t c) = 0) ∧
      (P (G.OmLong β (m' + 1) (U.PhiTop β σ d Φ0) z₀) = 0 → orbI D γ θ F' = 0)




end PI.UnitaryGroupMassFormula.DLm
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def IsUT {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) : Prop := (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1

def castM {n n' : ℕ} (h : n = n') (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n') (Fin n') ℂ :=
  Matrix.reindex (finCongr h) (finCongr h) M

def topPt {p s r : ℕ} (h : p + s = r + 1) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (Z : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  castM h (U.blk2 (U.hMat σ d) 0 0 Z)

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def ZOrb (D : B.RealPlaceData k r Wp Wq) (g : B.Mat k r) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Prop :=
  ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsUT u ∧ IsUT u' ∧ Zhat k r D.z D.z' g = u.conjTranspose * M * u'

end

def TopNF : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (γ : B.Mat k r) (i : ℕ),
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → HasRun D γ i (r + 1) →
    ∃ (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (z₀ : ℂ),
      p + 1 = i ∧ (∀ a, d a ≠ 0) ∧ z₀ ≠ 0 ∧ ZOrb D γ (topPt hps σ d (z₀ • G.wMat (m' + 1 + 1)))

def TopLower : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (γ : B.Mat k r) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (z₀ : ℂ) (m : ℕ),
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → (∀ a, d a ≠ 0) → z₀ ≠ 0 →
    ZOrb D γ (topPt hps σ d (z₀ • G.wMat (m' + 1 + 1))) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ t c : ℂ, t ≠ 0 → ‖t‖ < δ → c * t ^ (m' + 1) = (-1) ^ (m' + 3) * z₀ ^ (m' + 2) →
      ∃ (g : B.Mat k r) (μR : Measure (Mt k r)), B.IsHaarOn (Rset g) μR ∧ IsRelevant D g ∧
        0 < Gf k r D.z D.z' g ∧ zc D g ≤ m ∧ ZOrb D g (topPt hps σ d (G.ptBlock (m' + 1) t c))

def TopSlice : Prop :=
  ∀ C₂ : ℕ, ∃ C CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1)
    (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) → (∀ a, d a ≠ 0) →
    ∃ (β : ℂ) (Φ0 : G.Mat (p + (m' + 1 + 1)) → (Wq →L[ℂ] Wp)) (e : ℕ → ℝ) (K : ℝ),
      β ≠ 0 ∧ U.DecayAll (C₂ * (m' + 2) ^ 2) e K Φ0 ∧
      (∀ j ≤ C₂ * (m' + 2) ^ 2,
        (A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j)) / (5 * ((r : ℝ) + 1))
          - (C : ℝ) * (r : ℝ) ^ 2 ≤ e j / (5 * ((r : ℝ) + 1))) ∧
      (∀ t c : ℂ, t ≠ 0 → c ≠ 0 → ∀ (g : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
        B.IsHaarOn (Rset g) μR → IsRelevant D g → 0 < Gf k r D.z D.z' g →
        ZOrb D g (topPt hps σ d (G.ptBlock (m' + 1) t c)) → admitted D g μR θ →
        Integrable (fun x => θ x • (B.xiTau D (1, 1) x • B.rho D x F' g)) D.μSS →
        (G.OmBlock β (m' + 1) (U.PhiTop β σ d Φ0) t c = 0 ↔ orbI D g θ F' = 0)) ∧
      (∀ z : ℂ, z ≠ 0 → ∀ (g : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
        B.IsHaarOn (Rset g) μR → IsRelevant D g → 0 < Gf k r D.z D.z' g →
        ZOrb D g (topPt hps σ d (z • G.wMat (m' + 1 + 1))) → admitted D g μR θ →
        Integrable (fun x => θ x • (B.xiTau D (1, 1) x • B.rho D x F' g)) D.μSS →
        (G.OmLong β (m' + 1) (U.PhiTop β σ d Φ0) z = 0 ↔ orbI D g θ F' = 0))

end PI.UnitaryGroupMassFormula.DLm
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def fibInt (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : Wq →L[ℂ] Wp :=
  ∫ x : B.SS k r, B.rho D x F g ∂((D.μW.prod μ0).prod (D.μW'.prod μ0'))

def FibreRel (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)) {p m' : ℕ}
    (hps : p + (m' + 1 + 1) = r + 1) (Φ0 : G.Mat (p + (m' + 1 + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ g ∈ B.GV k r, 0 < Gf k r D.z D.z' g → ∃ (L₁ : Wp ≃L[ℂ] Wp) (L₂ : Wq ≃L[ℂ] Wq),
    ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      Φ0 (castM hps.symm (Zhat k r D.z D.z' (n⁻¹ * g * n'))) =
        (L₁ : Wp →L[ℂ] Wp).comp ((fibInt D μ0 μ0' F (n⁻¹ * g * n')).comp (L₂ : Wq →L[ℂ] Wq))

end

def TopDensEx : Prop :=
  ∀ C₂ : ℕ, ∃ C CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    ∃ (μ0 μ0' : Measure (Mt k r)) (Φ0 : G.Mat (p + (m' + 1 + 1)) → (Wq →L[ℂ] Wp)) (e : ℕ → ℝ) (K : ℝ),
      B.IsHaarOn (C2.N0set k r D.z) μ0 ∧ B.IsHaarOn (C2.N0set k r D.z') μ0' ∧
      U.DecayAll (C₂ * (m' + 2) ^ 2) e K Φ0 ∧
      (∀ j ≤ C₂ * (m' + 2) ^ 2,
        A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j) ≤ e j) ∧
      FibreRel D μ0 μ0' F' hps Φ0

def TopUnfold : Prop :=
  ∃ CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1)
    (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (μ0 μ0' : Measure (Mt k r))
    (Φ0 : G.Mat (p + (m' + 1 + 1)) → (Wq →L[ℂ] Wp)) (q : ℕ) (e : ℕ → ℝ) (K : ℝ),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) → (∀ a, d a ≠ 0) →
    B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    U.DecayAll q e K Φ0 → (∀ i ≤ q, 2 * ((r : ℝ) + 1) ^ 2 < e i / (5 * ((r : ℝ) + 1))) →
    FibreRel D μ0 μ0' F' hps Φ0 →
    ∃ β : ℂ, β ≠ 0 ∧
      (∀ t c : ℂ, t ≠ 0 → c ≠ 0 → ∀ (g : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
        B.IsHaarOn (Rset g) μR → IsRelevant D g → 0 < Gf k r D.z D.z' g →
        ZOrb D g (topPt hps σ d (G.ptBlock (m' + 1) t c)) → admitted D g μR θ →
        Integrable (fun x => θ x • (B.xiTau D (1, 1) x • B.rho D x F' g)) D.μSS →
        (G.OmBlock β (m' + 1) (U.PhiTop β σ d Φ0) t c = 0 ↔ orbI D g θ F' = 0)) ∧
      (∀ z : ℂ, z ≠ 0 → ∀ (g : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
        B.IsHaarOn (Rset g) μR → IsRelevant D g → 0 < Gf k r D.z D.z' g →
        ZOrb D g (topPt hps σ d (z • G.wMat (m' + 1 + 1))) → admitted D g μR θ →
        Integrable (fun x => θ x • (B.xiTau D (1, 1) x • B.rho D x F' g)) D.μSS →
        (G.OmLong β (m' + 1) (U.PhiTop β σ d Φ0) z = 0 ↔ orbI D g θ F' = 0))

end PI.UnitaryGroupMassFormula.DLm
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def zN {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) : ℝ := Real.sqrt (∑ a, ∑ b, Complex.normSq (Z a b))

def FibreBound : Prop :=
  ∃ C : ℕ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)),
    1 ≤ r → B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ (ε A : ℝ), 0 < ε → (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3) ≤ A → ∃ K : ℝ, 0 ≤ K ∧
      ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g →
        ∫⁻ x : B.SS k r, ENNReal.ofReal (B.gN (B.sgs x g) ^ (-A)) ∂((D.μW.prod μ0).prod (D.μW'.prod μ0')) ≤
          ENNReal.ofReal (K * (1 + zN (Zhat k r D.z D.z' g)) ^
            (-(A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3))))

def DensFramesOf : Prop := FibreBound → TopDensEx

end PI.UnitaryGroupMassFormula.DLm
end
end
