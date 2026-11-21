import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited

section
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HermLocal

namespace GlobalTheory.HermLocal.Model

section Quad
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]

noncomputable def conjSqrt : QuadraticAlgebra K d 0 ≃ₐ[K] QuadraticAlgebra K d 0 :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by
    change star _ = _
    ext <;> simp

theorem conjSqrt_apply (z : QuadraticAlgebra K d 0) : conjSqrt d z = star z := rfl


theorem isQuadratic : Algebra.IsQuadraticExtension K (QuadraticAlgebra K d 0) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two d 0

end Quad

instance two_not_sq : Fact (∀ r : ℚ_[2], r ^ 2 ≠ 2 + 0 * r) := ⟨fun r h => by
  rw [zero_mul, add_zero] at h
  have h1 := congrArg Padic.valuation h
  have h2 : (2 : ℚ_[2]).valuation = 1 := by exact_mod_cast Padic.valuation_p (p := 2)
  rw [Padic.valuation_pow, h2] at h1
  omega⟩


instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem norm_one_add_sq (t : ℚ_[3]) (ht : ‖t‖ ≤ 1) : ‖1 + t ^ 2‖ = 1 := by
  let s : ℤ_[3] := ⟨t, ht⟩
  have hu : IsUnit (1 + s ^ 2) := by
    by_contra h
    have h1 : 1 + s ^ 2 ∈ RingHom.ker (PadicInt.toZMod (p := 3)) := by
      rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, map_add, map_pow, map_one] at h1
    revert h1
    generalize PadicInt.toZMod s = z
    revert z; decide
  exact PadicInt.isUnit_iff.1 hu



instance neg_one_not_sq : Fact (∀ r : ℚ_[3], r ^ 2 ≠ -1 + 0 * r) := ⟨fun r h => by
  rw [zero_mul, add_zero] at h
  have h1 : ‖r‖ ^ 2 = 1 := by rw [← norm_pow, h]; simp
  have h2 : ‖r‖ ≤ 1 := by nlinarith [norm_nonneg r]
  have := norm_one_add_sq r h2
  rw [h] at this
  simp at this⟩


section Global
variable {E : Type} [Field E] [NumberField E] [IsCMField E]



end Global


end GlobalTheory.HermLocal.Model
end

section
noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.SplitUnitary.Model

open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
open GlobalTheory.HermLocal.Model (conjSqrt conjSqrt_apply)




section Form

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)


end Form

section Edge

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def Concl (hc : ∀ z, c (c z) = z) (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) {ψ : AddChar F ℂ}
    (hψ : Continuous ψ) (χ : Eˣ →* Circle) : Prop :=
  ∃ ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E)),
      IsSmoothRep ω ∧
      (∀ μ : @Measure (Matrix α ν E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)),
          ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ) ∧
      (∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E),
        Heisenberg₂ c hψ Q w * ω g =
          ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) ∧
      ∀ (a : GL ν E) (φ : SB (Matrix α ν E)) (x : Matrix α ν E),
        (ω (levi c hc a) φ : Matrix α ν E → ℂ) x =
          (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
            ((nabs F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det a)) ^
              ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) *
            (φ : Matrix α ν E → ℂ) (x * (a : Matrix ν ν E))




end Edge

end GlobalTheory.SplitUnitary.Model

end
end
