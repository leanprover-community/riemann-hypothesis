module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

noncomputable section

namespace GlobalTheory.GeoFix

theorem exists_lau_approx (p : ℕ) [Fact p.Prime] (K : ℕ) (x : O0 p) :
    ∃ (a : Lau p) (c : O0 p), x = algebraMap (Lau p) (O0 p) a + (p : O0 p) ^ K * c := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (pI p) K x)
  have hker : RingHom.ker (AdicCompletion.evalₐ (pI p) K) = (pI p ^ K).map (algebraMap (Lau p) (O0 p)) := by
    ext y
    rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem (Lau p), ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]
    have hle : (pI p ^ K • ⊤ : Ideal (Lau p)) ≤ pI p ^ K := by intro z hz; simpa using hz
    rw [← AdicCompletion.factor_eval_eq_evalₐ (pI p) y hle]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (pI p) (Lau p) K y)
      rw [← hb] at h ⊢
      have : b ∈ pI p ^ K := Ideal.Quotient.eq_zero_iff_mem.mp h
      exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
    · intro h; rw [h, map_zero]
  have hmem : x - algebraMap (Lau p) (O0 p) a ∈ RingHom.ker (AdicCompletion.evalₐ (pI p) K) := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ha, sub_self]
  rw [hker, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow, map_natCast,
    Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨a, c, by rw [mul_comm, hc]; ring⟩

end GlobalTheory.GeoFix
