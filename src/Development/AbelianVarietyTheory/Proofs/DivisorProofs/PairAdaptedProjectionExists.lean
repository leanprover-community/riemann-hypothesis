module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblSiegelChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem trace_one_tmul (e : E) : Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem eq_zero_of_psi_trace {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AE F E)
    (h : ∀ t : AE F E, ψ (Algebra.trace (AF F) (AE F E) (a * t)) = 1) : a = 0 := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let bb : Module.Basis _ (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  have hco : ∀ i, ∀ x : AE F E, Algebra.trace (AF F) (AE F E) (x * ((1 : AF F) ⊗ₜ[F] b.traceDual i)) = bb.repr x i := by
    intro i x
    conv_lhs => rw [← bb.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul, bb, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, trace_one_tmul, mul_comm (b _) (b.traceDual i), Module.Basis.trace_traceDual_mul]
    simp
  refine bb.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  apply GlobalTheory.DiagNonvan.eq_zero_of_psi_mul hψ
  intro y
  have := h (y • ((1 : AF F) ⊗ₜ[F] b.traceDual i))
  rwa [mul_smul_comm, map_smul, hco, smul_eq_mul, mul_comm] at this

end GlobalTheory.DblSiegelChar

namespace GlobalTheory.DblSiegelChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.DblSiegelChar

namespace GlobalTheory.DblSiegelChar

end GlobalTheory.DblSiegelChar
