import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIndexAddOfIsWittLower
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanMajorantStabilisersConjugate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory.MulVecTensorResolution

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mulVec_map_tmul {v : HeightOneSpectrum (𝓞 F)} {k l : ℕ} (M : Matrix (Fin k) (Fin l) E)
    (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (x : Fin l → E) :
    Matrix.mulVec (Matrix.map M fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) (fun i => a ⊗ₜ[F] x i) =
      fun j => a ⊗ₜ[F] (Matrix.mulVec M x) j := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    TensorProduct.tmul_sum]

theorem map_mem_latLoc {v : HeightOneSpectrum (𝓞 F)} {k l : ℕ} (M : Matrix (Fin k) (Fin l) E)
    {L₁ : Submodule (𝓞 E) (Fin l → E)} {L₂ : Submodule (𝓞 E) (Fin k → E)}
    (hM : ∀ x ∈ L₁, Matrix.mulVec M x ∈ L₂) {w : Fin l → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}
    (hw : w ∈ GlobalTheory.AdelicU.latLoc F L₁ v) :
    Matrix.mulVec (Matrix.map M fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) w ∈ GlobalTheory.AdelicU.latLoc F L₂ v := by
  refine GlobalTheory.AdelicU.latLoc_induction
    (p := fun w => Matrix.mulVec (Matrix.map M fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) w ∈
      GlobalTheory.AdelicU.latLoc F L₂ v) ?_ ?_ ?_ ?_ hw
  · intro a ha x hx
    rw [mulVec_map_tmul]
    exact GlobalTheory.AdelicU.tmul_mem_latLoc ha (hM x hx)
  · rw [Matrix.mulVec_zero]; exact zero_mem _
  · intro y z hy hz
    rw [Matrix.mulVec_add]; exact add_mem hy hz
  · intro y hy
    rw [Matrix.mulVec_neg]; exact neg_mem hy

theorem mulVec_map_resolution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n m t : ℕ}
    {e e' : Matrix (Fin n) (Fin t) R} {i₀ : Matrix (Fin n) (Fin m) R} {qX qY : Matrix (Fin t) (Fin n) R}
    {q0 : Matrix (Fin m) (Fin n) R} (h : e * qX + i₀ * q0 + e' * qY = 1) (y : Fin n → S) :
    y = e.map φ *ᵥ (qX.map φ *ᵥ y) + i₀.map φ *ᵥ (q0.map φ *ᵥ y) + e'.map φ *ᵥ (qY.map φ *ᵥ y) := by
  have h' := congrArg φ.mapMatrix h
  simp only [map_add, map_one, RingHom.mapMatrix_apply, Matrix.map_mul] at h'
  simp only [Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
  rw [h', Matrix.one_mulVec]

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] {n m t : ℕ} {e e' : Matrix (Fin n) (Fin t) E} {i₀ : Matrix (Fin n) (Fin m) E} {qX qY : Matrix (Fin t) (Fin n) E} {q0 : Matrix (Fin m) (Fin n) E}, e * qX + i₀ * q0 + e' * qY = (1 : Matrix (Fin n) (Fin n) E) → qX * e = (1 : Matrix (Fin t) (Fin t) E) → qX * i₀ = (0 : Matrix (Fin t) (Fin m) E) → qX * e' = (0 : Matrix (Fin t) (Fin t) E) → q0 * e = (0 : Matrix (Fin m) (Fin t) E) → q0 * i₀ = (1 : Matrix (Fin m) (Fin m) E) → q0 * e' = (0 : Matrix (Fin m) (Fin t) E) → qY * e = (0 : Matrix (Fin t) (Fin t) E) → qY * i₀ = (0 : Matrix (Fin t) (Fin m) E) → qY * e' = (1 : Matrix (Fin t) (Fin t) E) → ∀ {L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)} {L' : Submodule (NumberField.RingOfIntegers E) (Fin m → E)} {L₁ : Submodule (NumberField.RingOfIntegers E) (Fin t → E)}, (∀ (z : Fin n → E), z ∈ L ↔ Matrix.mulVec qX z ∈ L₁ ∧ Matrix.mulVec q0 z ∈ L' ∧ Matrix.mulVec qY z ∈ L₁) → ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (y : Fin n → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E), y ∈ GlobalTheory.AdelicU.latLoc F L v ↔ Matrix.mulVec (Matrix.map qX fun (x : E) ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y ∈ GlobalTheory.AdelicU.latLoc F L₁ v ∧ Matrix.mulVec (Matrix.map q0 fun (x : E) ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y ∈ GlobalTheory.AdelicU.latLoc F L' v ∧ Matrix.mulVec (Matrix.map qY fun (x : E) ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y ∈ GlobalTheory.AdelicU.latLoc F L₁ v := by
  intro F E _ _ _ _ n m t e e' i₀ qX qY q0 hsum hXe hXi hXe' h0e h0i h0e' hYe hYi hYe' L L' L₁ hL v y
  have mX : ∀ x ∈ L, Matrix.mulVec qX x ∈ L₁ := fun x hx => ((hL x).1 hx).1
  have m0 : ∀ x ∈ L, Matrix.mulVec q0 x ∈ L' := fun x hx => ((hL x).1 hx).2.1
  have mY : ∀ x ∈ L, Matrix.mulVec qY x ∈ L₁ := fun x hx => ((hL x).1 hx).2.2
  have me : ∀ x ∈ L₁, Matrix.mulVec e x ∈ L := fun x hx => (hL _).2
    ⟨by rw [Matrix.mulVec_mulVec, hXe, Matrix.one_mulVec]; exact hx,
     by rw [Matrix.mulVec_mulVec, h0e, Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, hYe, Matrix.zero_mulVec]; exact zero_mem _⟩
  have mi : ∀ x ∈ L', Matrix.mulVec i₀ x ∈ L := fun x hx => (hL _).2
    ⟨by rw [Matrix.mulVec_mulVec, hXi, Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, h0i, Matrix.one_mulVec]; exact hx,
     by rw [Matrix.mulVec_mulVec, hYi, Matrix.zero_mulVec]; exact zero_mem _⟩
  have me' : ∀ x ∈ L₁, Matrix.mulVec e' x ∈ L := fun x hx => (hL _).2
    ⟨by rw [Matrix.mulVec_mulVec, hXe', Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, h0e', Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, hYe', Matrix.one_mulVec]; exact hx⟩
  constructor
  · intro hy
    exact ⟨map_mem_latLoc qX mX hy, map_mem_latLoc q0 m0 hy, map_mem_latLoc qY mY hy⟩
  · rintro ⟨h1, h2, h3⟩
    have key : y = Matrix.mulVec (Matrix.map e fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x)
          (Matrix.mulVec (Matrix.map qX fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y) +
        Matrix.mulVec (Matrix.map i₀ fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x)
          (Matrix.mulVec (Matrix.map q0 fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y) +
        Matrix.mulVec (Matrix.map e' fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x)
          (Matrix.mulVec (Matrix.map qY fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y) :=
      mulVec_map_resolution
        (Algebra.TensorProduct.includeRight : E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E).toRingHom hsum y
    rw [key]
    exact add_mem (add_mem (map_mem_latLoc e me h1) (map_mem_latLoc i₀ mi h2)) (map_mem_latLoc e' me' h3)

end GlobalTheory.MulVecTensorResolution
end

section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.EmbLevel

open Formalism.UG

section Ring

variable {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {φ : A →+* B}

theorem cT_map (hφ : ∀ x, φ (σ x) = τ (φ x)) {m p : Type} (M : Matrix m p A) :
    (cT σ M).map φ = cT τ (M.map φ) := by
  funext i j
  exact hφ (M j i)

theorem conj_mem_iff {n : ℕ} (b g : GL (Fin n) B) :
    b⁻¹ * g * b ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = cT τ (b⁻¹).1 * (b⁻¹).1 := by
  have h1 : b.1 * (b⁻¹).1 = 1 := b.mul_inv
  have h2 : (b⁻¹).1 * b.1 = 1 := b.inv_mul
  have h3 : cT τ (b⁻¹).1 * cT τ b.1 = 1 := by rw [← cT_mul, h1, cT_one]
  have h4 : cT τ b.1 * cT τ (b⁻¹).1 = 1 := by rw [← cT_mul, h2, cT_one]
  change cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) = 1 ↔ _
  have e : cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) =
      cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1 := by
    simp only [cT_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e]
  generalize cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = X
  constructor
  · intro h
    calc X = (cT τ (b⁻¹).1 * cT τ b.1) * X * (b.1 * (b⁻¹).1) := by rw [h1, h3, Matrix.one_mul, Matrix.mul_one]
      _ = cT τ (b⁻¹).1 * (cT τ b.1 * X * b.1) * (b⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]
  · rintro rfl
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul, h2]

theorem conj_bc_mem_iff (hφ : ∀ x, φ (σ x) = τ (φ x)) {n : ℕ} (c g : GL (Fin n) A) :
    (bc φ c)⁻¹ * bc φ g * bc φ c ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      (cT σ g.1 * (cT σ (c⁻¹).1 * (c⁻¹).1) * g.1).map φ = (cT σ (c⁻¹).1 * (c⁻¹).1).map φ := by
  rw [conj_mem_iff, ← map_inv]
  simp only [Matrix.map_mul, cT_map hφ]
  rfl

end Ring

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem compInf_sigR (σ : E →ₐ[F] E) (w : InfinitePlace F) (x : AF F ⊗[F] E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

omit [NumberField E] in
theorem mem_levelAll_iff (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (c : GL (Fin n) (AF F ⊗[F] E)) (g : GAd σ J) : g ∈ levelAll σ J L c ↔
    (∀ v y, y ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J g).1.map (compFin F E v) *ᵥ y ∈ latLoc F L v) ∧
      ∀ w, (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (GlobalTheory.AdelicU.matHom _ σ J g).1 *
          (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1) * (GlobalTheory.AdelicU.matHom _ σ J g).1).map (compInf F E w) =
        (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1).map (compInf F E w) := by
  refine mem_levelAll.trans (and_congr Iff.rfl (forall_congr' fun w => ?_))
  rw [mem_stabArch, matHom_projArch]
  exact conj_bc_mem_iff (compInf_sigR σ w) c _

end Lattice

variable {D : D7}

end GlobalTheory.RegSch.EmbLevel

end
end
