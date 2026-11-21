import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpMat
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.LieDecomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.SLApply

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.expSub :
    ∀ (d d' : ℕ) (S : Subalgebra ℂ (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ))
      (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d') (Fin d') ℂ), (A, B) ∈ S → (NormedSpace.exp A, NormedSpace.exp B) ∈ S := by
  intro d d' S A B h
  have hc : IsClosed (S : Set (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule S)
  have hA : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • A ^ n) (NormedSpace.exp A) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hB : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • B ^ n) (NormedSpace.exp B) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B
  refine hc.mem_of_tendsto (hA.prodMk hB) (Filter.Eventually.of_forall fun s => ?_)
  refine S.sum_mem fun n _ => ?_
  exact S.smul_mem (S.pow_mem h n) ((n.factorial : ℂ)⁻¹)
end

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.pairAlg :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ Ξ' : AlgRep E a)
      (S : Subalgebra ℂ (Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ × Matrix (Fin Ξ'.d) (Fin Ξ'.d) ℂ)),
      (∀ τ i j, (eL Ξ.dmat τ i j, eL Ξ'.dmat τ i j) ∈ S) →
        (∀ X, (Ξ.dmat X, Ξ'.dmat X) ∈ S) ∧ ∀ y, (Ξ.mat y, Ξ'.mat y) ∈ S := by
  intro E _ _ _ a Ξ Ξ' S h
  have h1 : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), (Ξ.dmat (toL X), Ξ'.dmat (toL X)) ∈ S := by
    intro X
    have e : (Ξ.dmat (toL X), Ξ'.dmat (toL X)) = ∑ τ : E →+* ℂ, ∑ i, ∑ j,
        (X.map (coord τ)) i j • (eL Ξ.dmat τ i j, eL Ξ'.dmat τ i j) := by
      rw [lieDecomp E a _ Ξ.dmat X, lieDecomp E a _ Ξ'.dmat X]
      refine Prod.ext ?_ ?_
      · simp only [hol_apply, Prod.fst_sum, Prod.smul_fst]
      · simp only [hol_apply, Prod.snd_sum, Prod.smul_snd]
    rw [e]
    exact S.sum_mem fun τ _ => S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (h τ i j) _
  refine ⟨fun X => h1 (Matrix.of X), fun y => ?_⟩
  let H : Submonoid (GL (Fin a) (Cinf E)) :=
    { carrier := {y | (Ξ.mat y, Ξ'.mat y) ∈ S}
      one_mem' := by
        change (Ξ.mat 1, Ξ'.mat 1) ∈ S
        rw [map_one, map_one]
        exact S.one_mem
      mul_mem' := by
        intro x y hx hy
        change (Ξ.mat (x * y), Ξ'.mat (x * y)) ∈ S
        rw [map_mul, map_mul]
        exact S.mul_mem hx hy }
  refine expGen E a H (fun X y hy => ?_) y
  change (Ξ.mat y, Ξ'.mat y) ∈ S
  rw [expMat E a Ξ X y hy, expMat E a Ξ' X y hy]
  exact expSub _ _ S _ _ (h1 X)
end

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.algIrr :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a), IsMultiGl (eEnd Ξ) ∧ ∀ W, Stab (eEnd Ξ) W → W = ⊥ ∨ W = ⊤ := by
  intro E _ _ _ a Ξ
  refine ⟨?_, fun W hW => ?_⟩
  · obtain ⟨h1, h2⟩ := eLRel E a _ Ξ.dmat (GlobalTheory.AlgInfChar.dmat_bracket Ξ)
    let f := (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom
    have hf : ∀ τ i j, eEnd Ξ τ i j = f (eL Ξ.dmat τ i j) := fun _ _ _ => rfl
    refine ⟨fun τ i j k l => ?_, fun s t hst i j k l => ?_⟩
    · have h := congrArg f (h1 τ i j k l)
      simpa only [hf, map_sub, map_mul, apply_ite f, map_zero] using h
    · rw [hf, hf, ← map_mul, ← map_mul, h2 s t hst]
  · let S : Subalgebra ℂ (Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ × Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) :=
      { carrier := {p | ∀ w ∈ W, p.1 *ᵥ w ∈ W}
        mul_mem' := fun {p q} hp hq w hw => by
          rw [Prod.fst_mul, ← Matrix.mulVec_mulVec]
          exact hp _ (hq w hw)
        add_mem' := fun {p q} hp hq w hw => by
          rw [Prod.fst_add, Matrix.add_mulVec]
          exact W.add_mem (hp w hw) (hq w hw)
        algebraMap_mem' := fun c w hw => by
          rw [Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.fst_one, Matrix.smul_mulVec, Matrix.one_mulVec]
          exact W.smul_mem c hw }
    exact Ξ.irred W fun y v hv => (pairAlg E a Ξ Ξ S fun τ i j w hw => hW τ i j w hw).2 y v hv
end
