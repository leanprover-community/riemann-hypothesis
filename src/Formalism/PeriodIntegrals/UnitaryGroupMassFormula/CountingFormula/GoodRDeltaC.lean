import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GzNeOfTotPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.BasisEApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.DenEqOneOfForallPadicNormLeOne

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.DeltaB

open Polynomial

variable {R K A : Type} [CommRing R] [Field K] [CommRing A] [Algebra R K] [Algebra K A] [Algebra R A]
  [IsScalarTower R K A]

theorem trace_isIntegral_rank2 (b : Module.Basis (Fin 2) K A) {y : A} (hy : IsIntegral R y) :
    IsIntegral R (Algebra.trace K A y) := by
  classical
  obtain ⟨p, hpm, hp⟩ := hy
  let L := AlgebraicClosure K
  let M : Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix b y
  let M' : Matrix (Fin 2) (Fin 2) L := M.map (algebraMap K L)
  have hpy : Polynomial.aeval y p = 0 := hp
  have hpM : Polynomial.aeval M p = 0 := by
    have h1 := Polynomial.aeval_algHom_apply ((Algebra.leftMulMatrix b).restrictScalars R) y p
    rw [hpy, map_zero] at h1
    exact h1
  have hpM' : Polynomial.aeval M' p = 0 := by
    have h1 := Polynomial.aeval_algHom_apply
      (((Algebra.ofId K L).mapMatrix : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) L).restrictScalars R) M p
    rw [hpM, map_zero] at h1
    exact h1
  have hroot : ∀ μ ∈ M'.charpoly.roots, IsIntegral R μ := by
    intro μ hμ
    have h1 : μ ∈ spectrum L M' := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots'.mp hμ).2
    have h2 := spectrum.subset_polynomial_aeval M' (p.map (algebraMap R L)) ⟨μ, h1, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hpM', spectrum.zero_eq] at h2
    refine ⟨p, hpm, ?_⟩
    have h3 : Polynomial.eval μ (p.map (algebraMap R L)) = 0 := h2
    rwa [Polynomial.eval_map] at h3
  have htr : algebraMap K L (Algebra.trace K A y) = M'.charpoly.roots.sum := by
    rw [Algebra.trace_eq_matrix_trace b y, ← Matrix.trace_eq_sum_roots_charpoly]
    simp [M', M, Matrix.trace, Matrix.map_apply]
  have hint : IsIntegral R (algebraMap K L (Algebra.trace K A y)) := by
    rw [htr]
    exact IsIntegral.multiset_sum hroot
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).mp hint

end PI.UnitaryGroupMassFormula.CntFormula.DeltaB
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.DeltaC

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S.Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem norm_le_one_of_isIntegral_zl {ℓ : ℕ} [Fact ℓ.Prime] {t : ℚ_[ℓ]} (ht : IsIntegral ℤ_[ℓ] t) :
    ‖t‖ ≤ 1 := by
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp ht
  exact PadicInt.norm_le_one y

theorem mem_of_isIntegral_fp (L : LocAt F E sig p) {s : L.Fp} (hs : IsIntegral 𝒪[L.Fp] s) : s ∈ 𝒪[L.Fp] := by
  exact (Valuation.integer.integers (ValuativeRel.valuation L.Fp)).mem_of_integral hs

theorem trace_mem (L : LocAt F E sig p) {y : L.Ep} (hy : y ∈ L.O) : Algebra.trace L.Fp L.Ep y ∈ 𝒪[L.Fp] := by
  haveI := L.free
  haveI := PI.ProdFormulaE.Base.finite L
  let b : Module.Basis (Fin 2) L.Fp L.Ep := Module.finBasisOfFinrankEq L.Fp L.Ep L.rank
  exact mem_of_isIntegral_fp L (DeltaB.trace_isIntegral_rank2 b ((L.O_def y).mp hy))

end PI.UnitaryGroupMassFormula.CntFormula.DeltaC
end
end
