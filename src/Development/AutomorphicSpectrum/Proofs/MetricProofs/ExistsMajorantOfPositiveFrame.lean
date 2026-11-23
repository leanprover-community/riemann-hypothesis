module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitarySurjective
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ComplexOrder

section Conj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev cj (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := A.map (starRingEnd ℂ)

theorem cj_cj (A : Matrix ι ι ℂ) : cj (cj A) = A := by
  ext i k; simp [cj]

theorem cj_injective : Function.Injective (cj : Matrix ι ι ℂ → Matrix ι ι ℂ) :=
  Function.LeftInverse.injective cj_cj

theorem cj_mul (A B : Matrix ι ι ℂ) : cj (A * B) = cj A * cj B := Matrix.map_mul

theorem cj_eq (A : Matrix ι ι ℂ) : cj A = Aᴴᵀ := by
  ext i k; simp [cj]

theorem cj_inv (A : Matrix ι ι ℂ) : cj A⁻¹ = (cj A)⁻¹ := by
  rw [cj_eq, cj_eq, conjTranspose_nonsing_inv, transpose_nonsing_inv]

theorem cj_conjTranspose (A : Matrix ι ι ℂ) : cj Aᴴ = (cj A)ᴴ := by
  ext i k; simp [cj]

theorem posDef_cj {P : Matrix ι ι ℂ} (h : P.PosDef) : (cj P).PosDef := by
  have : cj P = Pᵀ := by rw [cj_eq, h.1.eq]
  rw [this]
  exact h.transpose

theorem cj_mulVec (A : Matrix ι ι ℂ) (v : ι → ℂ) : cj A *ᵥ star v = star (A *ᵥ v) := by
  ext i; simp [cj, mulVec, dotProduct, map_sum]

theorem re_term_cj (P G : Matrix ι ι ℂ) (v : ι → ℂ) :
    (star (G *ᵥ star v) ⬝ᵥ (cj P *ᵥ (G *ᵥ star v))).re = (star (cj G *ᵥ v) ⬝ᵥ (P *ᵥ (cj G *ᵥ v))).re := by
  have hu : G *ᵥ star v = star (cj G *ᵥ v) := by
    rw [← cj_mulVec, cj_cj]
  rw [hu, cj_mulVec, star_dotProduct_star, dotProduct_comm]
  simp

theorem stab_iff_cj (P G : Matrix ι ι ℂ) :
    (G.map (starRingEnd ℂ))ᵀ * cj P * G = cj P ↔ (cj G)ᴴ * P * cj G = P := by
  have h : (G.map (starRingEnd ℂ))ᵀ * cj P * G = cj ((cj G)ᴴ * P * cj G) := by
    rw [cj_mul, cj_mul, cj_conjTranspose, cj_cj]
    rfl
  rw [h]
  exact cj_injective.eq_iff

end Conj

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

omit [IsCMField E] in
theorem embOf_coe (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : embOf s (a : E) = s a :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) a

omit [IsCMField E] in
theorem embOf_comp (φ : E →+* ℂ) : embOf (φ.comp (algebraMap (𝓞 E) E)) = φ :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (by
    ext a; simpa using embOf_coe (φ.comp (algebraMap (𝓞 E) E)) a)

omit [IsCMField E] in
theorem embOf_injective : Function.Injective (embOf : (𝓞 E →+* ℂ) → (E →+* ℂ)) := by
  intro s s' h
  ext a
  have := congrArg (fun φ : E →+* ℂ => φ (a : E)) h
  simpa [embOf_coe] using this

theorem plc_bijective (F : UnivFam E Ψ j j' n g Λ) : Function.Bijective (plc F) := by
  apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.plc_bijective <;> assumption

theorem emb_ne (F : UnivFam E Ψ j j' n g Λ) (τ : Ψ) (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) :=
  (InfinitePlace.embedding_mk_eq (embOf (F.σ τ))).resolve_left h

def atPlc (F : UnivFam E Ψ j j' n g Λ) (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (τ : Ψ) :
    Matrix (Fin (j + j')) (Fin (j + j')) ℂ := by
  classical
  exact if (plc F τ).embedding = embOf (F.σ τ) then Pt τ else cj (Pt τ)

variable {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem gramAt_of_eq {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) = C.gr τ := by
  rw [gramAt, h]; rfl

theorem gramAt_of_ne {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) = cj (C.gr τ) := by
  rw [gramAt, emb_ne F τ h]
  ext i k
  simp [LatEmb.gr, ComplexEmbedding.conjugate_coe_eq]

theorem vecAt_of_eq (x : Λ) {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x) (plc F τ) = C.vec x τ := by
  ext i
  simp [vecAt, LatEmb.vec, h]

theorem vecAt_of_ne (x : Λ) {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x) (plc F τ) = star (C.vec x τ) := by
  ext i
  simp [vecAt, LatEmb.vec, emb_ne F τ h, ComplexEmbedding.conjugate_coe_eq]

theorem tm_of_eq (a : C.Arch) {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    C.tm a τ = ((a : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) := by
  rw [LatEmb.tm, tauMat, if_pos h]

theorem tm_of_ne (a : C.Arch) {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    C.tm a τ = cj ((a : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) := by
  rw [LatEmb.tm, tauMat, if_neg h]

theorem atPlc_of_eq (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) {τ : Ψ}
    (h : (plc F τ).embedding = embOf (F.σ τ)) : atPlc F Pt τ = Pt τ := by
  rw [atPlc]; exact if_pos h

theorem atPlc_of_ne (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) {τ : Ψ}
    (h : (plc F τ).embedding ≠ embOf (F.σ τ)) : atPlc F Pt τ = cj (Pt τ) := by
  rw [atPlc]; exact if_neg h

def majOf (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) : Majorant C.h (Pi.basisFun E (Fin (j + j'))) where
  P w := atPlc F Pt ((Equiv.ofBijective _ (plc_bijective F)).symm w)
  posDef w := by
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    have hτ : (Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ) = τ :=
      Equiv.ofBijective_symm_apply_apply _ _ _
    rw [hτ]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h]; exact hP τ
    · rw [atPlc_of_ne Pt h]; exact posDef_cj (hP τ)
  siegel w := by
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    have hτ : (Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ) = τ :=
      Equiv.ofBijective_symm_apply_apply _ _ _
    rw [hτ]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h, gramAt_of_eq C h]; exact hS τ
    · rw [atPlc_of_ne Pt h, gramAt_of_ne C h, ← cj_inv, ← cj_mul, ← cj_mul, hS τ]

theorem majOf_P (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (τ : Ψ) : (majOf C Pt hP hS).P (plc F τ) = atPlc F Pt τ := by
  show atPlc F Pt ((Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ)) = _
  rw [Equiv.ofBijective_symm_apply_apply]

theorem majOf_term (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (a : C.Arch) (x : Λ) (τ : Ψ) :
    (star (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x)) (plc F τ)) ⬝ᵥ
      ((majOf C Pt hP hS).P (plc F τ) *ᵥ invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x)) (plc F τ))).re =
    (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re := by
  rw [majOf_P]
  by_cases h : (plc F τ).embedding = embOf (F.σ τ)
  · rw [atPlc_of_eq Pt h, tm_of_eq C _ h, ← vecAt_of_eq C x h]
    rfl
  · rw [atPlc_of_ne Pt h, tm_of_ne C _ h, ← re_term_cj, ← vecAt_of_ne C x h]
    rfl

theorem majOf_len (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (a : C.Arch) (x : Λ) :
    (majOf C Pt hP hS).len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x))) ^ 2 =
      ∑ τ, (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re := by
  rw [Majorant.len, Real.sq_sqrt]
  · rw [← (Equiv.ofBijective _ (plc_bijective F)).sum_comp]
    exact Finset.sum_congr rfl fun τ _ => majOf_term C Pt hP hS a x τ
  · exact Finset.sum_nonneg fun w _ => ((majOf C Pt hP hS).posDef w).posSemidef.re_dotProduct_nonneg _

theorem majOf_stab (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (c : C.Arch) :
    c ∈ (majOf C Pt hP hS).stab ↔ ∀ τ, (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ := by
  have hloc : ∀ τ, ((((c : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)).map
        (starRingEnd ℂ))ᵀ * (majOf C Pt hP hS).P (plc F τ) *
        ((c : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) =
        (majOf C Pt hP hS).P (plc F τ) ↔ (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ := by
    intro τ
    rw [majOf_P]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h, tm_of_eq C _ h]
      rfl
    · rw [atPlc_of_ne Pt h, tm_of_ne C _ h]
      exact stab_iff_cj _ _
  rw [Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi]
  constructor
  · intro hc τ
    exact (hloc τ).1 (mem_unitaryGroupMatrix.1 (hc (plc F τ) (Set.mem_univ _)))
  · intro hc w _
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    exact mem_unitaryGroupMatrix.2 ((hloc τ).2 (hc τ))

end Arch

theorem exists_majorant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F)
    (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (Pt τ).PosDef) →
    (∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) →
    ∃ M : Majorant C.h (Pi.basisFun E (Fin (j + j'))),
      (∀ (a : C.Arch) (x : Λ), M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x))) ^ 2 =
        ∑ τ, (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re) ∧
      ∀ c : C.Arch, c ∈ M.stab ↔ ∀ τ, (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ :=
  by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C Pt hP hS
  exact ⟨majOf C Pt hP hS, majOf_len C Pt hP hS, majOf_stab C Pt hP hS⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj
