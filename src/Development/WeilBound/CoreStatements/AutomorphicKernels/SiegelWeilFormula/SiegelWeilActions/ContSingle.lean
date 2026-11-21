import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DMEqDiag
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PtEx
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainLe

section
noncomputable section

open scoped Matrix

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n k : ℕ} (i₀ : Fin n) (em : Fin k → Fin n)

def cB (u v : Fin k → R) (z : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks (1 + ∑ j, Matrix.single i₀ (em j) (u j)) (Matrix.single i₀ i₀ z) 0 (1 - ∑ j, Matrix.single (em j) i₀ (v j))

variable {i₀ em}

theorem cB_mul (hem : ∀ j, em j ≠ i₀) (u v : Fin k → R) (z : R) : cB i₀ em u v z * cB i₀ em (-u) (-v) (-z) = 1 := by
  have hPP : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hQQ : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _
  have hPZ : ∀ (w : Fin k → R) (c : R),
      (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0 := by
    intro w c
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hZQ : ∀ (w : Fin k → R) (c : R),
      Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0 := by
    intro w c
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _
  simp only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, Matrix.fromBlocks_multiply, Pi.neg_apply, ← Matrix.single_neg,
    Finset.sum_neg_distrib]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, one_mul, mul_one, mul_zero, zero_mul,
      hPP, hQQ, hPZ, hZQ, neg_zero, add_zero, zero_add, sub_zero, neg_neg] <;>
    abel

theorem cB_unitary (hem : ∀ j, em j ≠ i₀) (f : R →+* R) (hf : ∀ a, f (f a) = a) (e : R) (he : e * e = 1)
    (u : Fin k → R) (z : R) (hz : f z = -(e * z)) :
    (cB i₀ em u (fun j => f (u j)) z)ᵀ * kunf.jw n e * (cB i₀ em u (fun j => f (u j)) z).map f = kunf.jw n e := by
  have hPP : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hQQ : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _
  have hPZ : ∀ (w : Fin k → R) (c : R),
      (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0 := by
    intro w c
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hZQ : ∀ (w : Fin k → R) (c : R),
      Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0 := by
    intro w c
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _
  have hmap : ∀ M : Matrix (Fin n) (Fin n) R, M.map f = f.mapMatrix M := fun M =>
    (RingHom.mapMatrix_apply f M).symm
  simp only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, PositivityTheory.SiegelWeilFormula.kunf.jw, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_sum, Matrix.transpose_single, hmap,
    map_add, map_sub, map_one, map_zero, map_sum]
  simp only [RingHom.mapMatrix_apply, Matrix.map_single, hf, hz]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [mul_zero, zero_mul, add_zero]
  · simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_sub, add_mul, one_mul, hQQ, sub_zero]
    abel
  · simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one]
    congr 1
    simp only [mul_add, sub_mul, one_mul, mul_one, hPP, add_zero]
    abel
  · simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one,
      mul_sub, sub_mul, one_mul, hPZ, hZQ, sub_zero, Matrix.smul_single, smul_eq_mul, smul_zero]
    rw [← Matrix.single_add, show e * -(e * z) + z = 0 by linear_combination (-z) * he, Matrix.single_zero]

end Alg

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

section
noncomputable section

open scoped Matrix

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n k : ℕ} {i₀ : Fin n} {em : Fin k → Fin n}

theorem cB_dM (hem : ∀ j, em j ≠ i₀) (u v : Fin k → R) (z x y : R) (hxy : x * y = 1) :
    cB i₀ em u v z * dM i₀ x y = dM i₀ x y * cB i₀ em (fun j => y * u j) (fun j => y * v j) (y * y * z) := by
  have hS : ∀ (w : Fin k → R) a b, (∑ j, Matrix.single i₀ (em j) (w j)) a b =
      if a = i₀ then ∑ j, (if em j = b then w j else 0) else 0 := by
    intro w a b
    rw [Matrix.sum_apply]
    split_ifs with ha
    · subst ha; exact Finset.sum_congr rfl fun j _ => by rw [Matrix.single_apply]; simp
    · exact Finset.sum_eq_zero fun j _ => by
        rw [Matrix.single_apply]; split_ifs with h
        · exact absurd h.1.symm ha
        · rfl
  have hT : ∀ (w : Fin k → R) a b, (∑ j, Matrix.single (em j) i₀ (w j)) a b =
      if b = i₀ then ∑ j, (if em j = a then w j else 0) else 0 := by
    intro w a b
    rw [Matrix.sum_apply]
    split_ifs with hb
    · subst hb; exact Finset.sum_congr rfl fun j _ => by rw [Matrix.single_apply]; simp
    · exact Finset.sum_eq_zero fun j _ => by
        rw [Matrix.single_apply]; split_ifs with h
        · exact absurd h.2.symm hb
        · rfl
  have hs0 : ∀ (w : Fin k → R), ∑ j, (if em j = i₀ then w j else 0) = 0 :=
    fun w => Finset.sum_eq_zero fun j _ => by rw [if_neg (hem j)]
  have hsy : ∀ (w : Fin k → R) b, ∑ j, (if em j = b then y * w j else 0) = y * ∑ j, (if em j = b then w j else 0) := by
    intro w b; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  rw [dM_eq_diag]
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases p with a | a <;> rcases q with b | b
  · simp only [cB, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.one_apply, hS, hsy, dg, Sum.inl.injEq, reduceCtorEq,
      if_false]
    by_cases hab : a = b
    · subst hab; by_cases ha : a = i₀
      · subst ha; simp [hs0]
      · simp [ha]
    · by_cases ha : a = i₀
      · subst ha
        simp only [if_neg hab, if_true, if_neg (Ne.symm hab), zero_add, mul_one]
        rw [← mul_assoc, hxy, one_mul]
      · simp [ha, hab]
  · simp only [cB, Matrix.fromBlocks_apply₁₂, Matrix.single_apply, dg, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false]
    by_cases h : i₀ = a ∧ i₀ = b
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, if_true]
      linear_combination (-(y * z)) * hxy
    · simp only [if_neg h, zero_mul, mul_zero]
  · simp [cB]
  · simp only [cB, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.one_apply, hT, hsy, dg, Sum.inr.injEq, reduceCtorEq,
      if_false]
    by_cases hab : a = b
    · subst hab; by_cases ha : a = i₀
      · subst ha; simp [hs0]
      · simp [ha]
    · by_cases hb : b = i₀
      · subst hb
        simp only [if_neg hab, if_true, if_neg hab, zero_sub]
        ring
      · simp [hb, hab]

end Alg

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

section
noncomputable section

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma_cm (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2 w.embedding, h.2.2.2 w.embedding, star_star]

theorem exists_sigma_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hne
  push_neg at hne
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc : w.IsComplex := h.2.1.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.2 hc
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  change star (w.embedding x) = w.embedding x
  rw [← h.2.2.2 w.embedding, hne]

theorem deltaEx' (h : IsCMExt F E σ) (ε : ℤˣ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -(((ε : ℤ) : E) * δ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · obtain ⟨x, hx⟩ := exists_sigma_ne h
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sigma_sigma_cm h]
    simp
  · exact ⟨1, one_ne_zero, by simp⟩

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

section
noncomputable section

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n : ℕ} (i₀ : Fin n)

theorem wM_map {S : Type} [CommRing S] (f : R →+* S) (a b : R) : (wM i₀ a b).map f = wM i₀ (f a) (f b) := by
  delta wM
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.single_apply, map_add, map_sub]
  split_ifs <;> simp

theorem wM_blocks (a b : R) : wM i₀ a b = Matrix.fromBlocks (1 - Matrix.single i₀ i₀ 1) (a • Matrix.single i₀ i₀ 1)
    (b • Matrix.single i₀ i₀ 1) (1 - Matrix.single i₀ i₀ 1) := by
  delta wM
  ext (i | i) (j | j) <;>
    simp [Matrix.single_apply, Matrix.one_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem wM_unitary (f : R →+* R) (a b e : R) (h1 : b * e * f a = 1) (h2 : a * f b = e) :
    (wM i₀ a b)ᵀ * kunf.jw n e * (wM i₀ a b).map f = kunf.jw n e := by
  have hjw : kunf.jw n e = Matrix.fromBlocks 0 1 (e • 1) 0 := rfl
  have hEE : Matrix.single i₀ i₀ (1 : R) * Matrix.single i₀ i₀ 1 = Matrix.single i₀ i₀ 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hET : (Matrix.single i₀ i₀ (1 : R))ᵀ = Matrix.single i₀ i₀ 1 := Matrix.transpose_single _ _ _
  have h1' : e * b * f a = 1 := by rw [mul_comm e b]; exact h1
  rw [wM_map, wM_blocks, wM_blocks, hjw]
  generalize Matrix.single i₀ i₀ (1 : R) = E at hEE hET ⊢
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hET,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul, hEE, sub_self, smul_zero,
    sub_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · trivial
  · linear_combination (norm := module) h1' • E
  · linear_combination (norm := module) h2 • E
  · trivial
end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

section
set_option linter.style.haveILetI false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adeleHaarB {m : MeasurableSpace (AF F)} (hB : @BorelSpace (AF F) _ m) :
    ∃ μ : @Measure (AF F) m, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ ∀ r : GroundTheory.Global.IdeleGroup F,
      μ.map (fun y => (r : AF F) * y) =
        (((((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹).toNNReal : NNReal) : ENNReal) • μ := by
  have h1 : m = GroundTheory.Global.measurableSpace_adeleRing F :=
    hB.measurable_eq.trans (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq.symm
  subst h1
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GroundTheory.Global.instIsAddHaarMeasureAdeleRingRingOfIntegersAdeleMeasure F
  refine ⟨GroundTheory.Global.adeleMeasure F, inferInstance, inferInstance, fun r => ?_⟩
  exact GroundTheory.Global.map_smul_adeleMeasure r

theorem pi_map_const {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (f : X → X) (hf : Measurable f)
    (c : NNReal) (hμ : μ.map f = (c : ENNReal) • μ) (ι : Type) [Fintype ι] [DecidableEq ι] :
    (Measure.pi fun _ : ι => μ).map (fun y i => f (y i)) = ((c : ENNReal) ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  haveI : SigmaFinite (μ.map f) := by
    rw [hμ]
    exact (inferInstance : SigmaFinite (c • μ))
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  simp only [hμ]
  haveI : SigmaFinite ((c : ENNReal) • μ) := (inferInstance : SigmaFinite (c • μ))
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem measN (n k : ℕ) (bs : Module.Basis (Fin n) F E) : ∃ κ : Measure ((Fin k → AE F E) × AF F), κ.IsAddHaarMeasure ∧
    ∀ r : GroundTheory.Global.IdeleGroup F, ∃ sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F),
      (∀ c : (Fin k → AE F E) × AF F, sc c = ((fun j : Fin k => (r : AF F) • c.1 j), ((r : AF F) * (r : AF F)) • c.2)) ∧
      κ.map sc = ENNReal.ofReal (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ ^ (n * k + 2)) • κ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI hBA : BorelSpace (AF F) := ⟨rfl⟩
  haveI hBE : BorelSpace (AE F E) := ⟨rfl⟩
  obtain ⟨ν, hνH, hνS, hν⟩ := adeleHaarB (F := F) hBA
  let ψ := (Algebra.TensorProduct.basis (AF F) bs).equivFun
  have hψ : Continuous ψ :=
    IsModuleTopology.continuous_of_linearMap (ψ : AE F E →ₗ[AF F] (Fin n → AF F))
  have hψs : Continuous ψ.symm :=
    IsModuleTopology.continuous_of_linearMap (ψ.symm : (Fin n → AF F) →ₗ[AF F] AE F E)
  let e : ((Fin k → Fin n → AF F) × AF F) ≃+ ((Fin k → AE F E) × AF F) :=
    AddEquiv.prodCongr (AddEquiv.piCongrRight fun _ => ψ.symm.toAddEquiv) (AddEquiv.refl _)
  have he : Continuous e := by
    change Continuous fun p : (Fin k → Fin n → AF F) × AF F => ((fun j => ψ.symm (p.1 j)), p.2)
    exact (continuous_pi fun j => hψs.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_snd
  have hes : Continuous e.symm := by
    change Continuous fun p : (Fin k → AE F E) × AF F => ((fun j => ψ (p.1 j)), p.2)
    exact (continuous_pi fun j => hψ.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_snd
  let μW : Measure (Fin k → Fin n → AF F) := Measure.pi fun _ => Measure.pi fun _ => ν
  refine ⟨(μW.prod ν).map e, e.isAddHaarMeasure_map _ he hes, fun r => ?_⟩
  set a : AF F := (r : AF F) with ha
  set b : AF F := ((r⁻¹ : GroundTheory.Global.IdeleGroup F) : AF F) with hb
  have hab : b * a = 1 := r.inv_mul
  have hba : a * b = 1 := r.mul_inv
  let S : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F := fun c => (fun j => a • c.1 j, (a * a) • c.2)
  let S' : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F := fun c => (fun j => b • c.1 j, (b * b) • c.2)
  have hS : Continuous S :=
    (continuous_pi fun j => ((continuous_apply j).comp continuous_fst).const_smul a).prodMk
      (continuous_snd.const_smul (a * a))
  have hS' : Continuous S' :=
    (continuous_pi fun j => ((continuous_apply j).comp continuous_fst).const_smul b).prodMk
      (continuous_snd.const_smul (b * b))
  let sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F) :=
    { toFun := S
      invFun := S'
      left_inv := fun c => by
        refine Prod.ext (funext fun j => ?_) ?_
        · show b • a • c.1 j = c.1 j
          rw [smul_smul, hab, one_smul]
        · show (b * b) • (a * a) • c.2 = c.2
          rw [smul_smul, show b * b * (a * a) = (b * a) * (b * a) by ring, hab, one_mul, one_smul]
      right_inv := fun c => by
        refine Prod.ext (funext fun j => ?_) ?_
        · show a • b • c.1 j = c.1 j
          rw [smul_smul, hba, one_smul]
        · show (a * a) • (b * b) • c.2 = c.2
          rw [smul_smul, show a * a * (b * b) = (a * b) * (a * b) by ring, hba, one_mul, one_smul]
      measurable_toFun := hS.measurable
      measurable_invFun := hS'.measurable }
  refine ⟨sc, fun c => rfl, ?_⟩
  let T1 : (Fin k → Fin n → AF F) → (Fin k → Fin n → AF F) := fun w j i => a * w j i
  let T2 : AF F → AF F := fun t => (a * a) * t
  have hT1 : Continuous T1 := continuous_pi fun j => continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply j))
  have hT2 : Continuous T2 := continuous_const.mul continuous_id
  have hcomm : (sc : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F) ∘ e = e ∘ Prod.map T1 T2 := by
    funext p
    refine Prod.ext (funext fun j => ?_) rfl
    show a • ψ.symm (p.1 j) = ψ.symm (fun i => a * p.1 j i)
    rw [← map_smul]
    rfl
  set c : NNReal := (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹).toNNReal with hc
  have h1 : ν.map (fun y => a * y) = (c : ENNReal) • ν := hν r
  have hm1 : Measurable fun y : AF F => a * y := (continuous_const.mul continuous_id).measurable
  have hin : (Measure.pi fun _ : Fin n => ν).map (fun y i => a * y i) =
      ((c ^ n : NNReal) : ENNReal) • Measure.pi fun _ : Fin n => ν := by
    rw [pi_map_const ν (fun y => a * y) hm1 c h1 (Fin n), Fintype.card_fin, ENNReal.coe_pow]
  have hW : μW.map T1 = ((c : ENNReal) ^ n) ^ k • μW := by
    have hm2 : Measurable fun y : Fin n → AF F => fun i => a * y i :=
      (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
    have := pi_map_const (Measure.pi fun _ : Fin n => ν) (fun y i => a * y i) hm2 (c ^ n) hin (Fin k)
    rw [Fintype.card_fin, ENNReal.coe_pow] at this
    exact this
  have hA : ν.map T2 = (c : ENNReal) ^ 2 • ν := by
    have : T2 = (fun y => a * y) ∘ (fun y => a * y) := by
      funext t
      simp [T2, mul_assoc]
    rw [this, ← Measure.map_map hm1 hm1, h1, Measure.map_smul, h1, smul_smul, sq]
  rw [show ((μW.prod ν).map e).map sc = ((μW.prod ν).map e).map (sc : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F) from rfl,
    Measure.map_map sc.measurable he.measurable, hcomm,
    ← Measure.map_map he.measurable (hT1.measurable.prodMap hT2.measurable),
    ← Measure.map_prod_map μW ν hT1.measurable hT2.measurable, hW, hA,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
  congr 1
  have hx : (0 : ℝ) ≤ ((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ := inv_nonneg.mpr (le_of_lt (GroundTheory.Global.IdeleGroup.ideleModule F r).2)
  rw [ENNReal.ofReal_pow hx, ← pow_mul, ← pow_add]
  rfl

theorem measEx' (k : ℕ) (bs : Module.Basis (Fin 2) F E) : ∃ κ : Measure ((Fin k → AE F E) × AF F), κ.IsAddHaarMeasure ∧
    ∀ r : GroundTheory.Global.IdeleGroup F, ∃ sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F),
      (∀ c : (Fin k → AE F E) × AF F, sc c = ((fun j : Fin k => (r : AF F) • c.1 j), ((r : AF F) * (r : AF F)) • c.2)) ∧
      κ.map sc = ENNReal.ofReal (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ ^ (2 * k + 2)) • κ :=
  measN 2 k bs

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act

def CLawEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d),
  ∃ (w₁ : d.G) (cM : (Fin L.n → AE F E) × AF F → d.G) (κ : Measure ((Fin L.n → AE F E) × AF F)),
    CLaw R L w₁ cM κ ∧ w₁ ∈ rat2 σ d.Y ∧
    (∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)) ∧
    Continuous cM ∧ κ.IsAddHaarMeasure ∧
    ∃ δ : E, δ ≠ 0 ∧ ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (c.1 j))
      (Matrix.single L.i₀ L.i₀ (c.2 • inclR (F := F) (AF F) δ)) 0 A'

theorem cont_single {X α : Type} [TopologicalSpace X] [TopologicalSpace α] [Zero α] {m p : Type} [DecidableEq m]
    [DecidableEq p] (i : m) (j : p) {f : X → α} (hf : Continuous f) : Continuous fun x => Matrix.single i j (f x) :=
  continuous_pi fun a => continuous_pi fun b => by
    simp only [Matrix.single_apply]
    split_ifs
    exacts [hf, continuous_const]

theorem cLawEx : CLawEx := by
  intro F E _ _ _ _ _ σ d R L
  have hε := R.hε
  have hem : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  set e : AE F E := ((R.ε : ℤ) : AE F E) with he_def
  have hee : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  obtain ⟨δ, hδ0, hδ⟩ := CL.deltaEx' d.cm R.ε
  obtain ⟨κ, hκ, hsc⟩ := CL.measEx' (F := F) (E := E) L.n d.bs

  let M₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ (1 : E) ((R.ε : ℤ) : E)
  let M₀' : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ ((R.ε : ℤ) : E) (1 : E)
  have hW : incM F M₀ = CL.wM L.i₀ (1 : AE F E) e := by
    show M₀.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hW' : incM F M₀' = CL.wM L.i₀ e (1 : AE F E) := by
    show M₀'.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hWW : incM F M₀ * incM F M₀' = 1 := by
    rw [hW, hW']; exact CL.wM_mul L.i₀ _ _ _ _ (one_mul 1) hee
  have hWu : (incM F M₀)ᵀ * kunf.jw d.n e * (incM F M₀).map (cA σ) = kunf.jw d.n e := by
    rw [hW]
    refine CL.wM_unitary L.i₀ (cA σ).toRingHom 1 e e ?_ ?_
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_one, mul_one, hee]
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, he_def, map_intCast, one_mul]
  obtain ⟨w₁, hw₁⟩ := kunf.exists_of_frame hε (incM F M₀) (incM F M₀') hWW hWu
  have hw₁' : inFrame d.b w₁ = CL.wM L.i₀ (1 : AE F E) e := hw₁.trans hW

  set δ' : AE F E := inclR (F := F) (AF F) δ with hδ'
  let Mc : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em c.1 (fun j => cA σ (c.1 j)) (c.2 • δ')
  let Mc' : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em (-c.1) (-fun j => cA σ (c.1 j)) (-(c.2 • δ'))
  have hcont : ∀ s : AF F → AF F, Continuous s → ∀ t : (Fin L.n → AE F E) → (Fin L.n → AE F E), Continuous t →
      Continuous fun c : (Fin L.n → AE F E) × AF F =>
        CL.cB L.i₀ L.em (t c.1) (fun j => cA σ (t c.1 j)) (s c.2 • δ') := by
    intro s hs t ht
    refine Continuous.matrix_fromBlocks ?_ ?_ continuous_const ?_
    · exact continuous_const.add (continuous_finsetSum _ fun j _ =>
        cont_single _ _ ((continuous_apply j).comp (ht.comp continuous_fst)))
    · exact cont_single _ _ (Continuous.smul (f := fun c : (Fin L.n → AE F E) × AF F => s c.2) (g := fun _ => δ')
        (hs.comp continuous_snd) continuous_const)
    · exact continuous_const.sub (continuous_finsetSum _ fun j _ => cont_single _ _
        ((GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ).comp ((continuous_apply j).comp (ht.comp continuous_fst))))
  have hMc : Continuous Mc := hcont id continuous_id id continuous_id
  have hMc' : Continuous Mc' := by
    have := hcont (fun a => -a) continuous_neg (fun u => -u) continuous_neg
    convert this using 2 with c
    simp only [Mc', neg_smul, Pi.neg_apply, map_neg]
    rfl
  have hcA_z : ∀ a : AF F, cA σ (a • δ') = -(e * (a • δ')) := by
    intro a
    rw [map_smul, hδ', GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR σ δ, hδ, map_neg, map_mul, map_intCast, smul_neg, mul_smul_comm]
  obtain ⟨cM, hcMc, hcM⟩ := CL.ptEx' d hε Mc Mc' hMc hMc'
    (fun c => CL.cB_mul hem c.1 _ _) (fun c => CL.cB_unitary hem (cA σ).toRingHom
      (fun a => GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ (CL.sigma_sigma_cm d.cm) a) e hee c.1 (c.2 • δ') (hcA_z c.2))
  have hfr := fun x y => GlobalTheory.EisBL.DoubledParabolic.inFrame_mul (σ := σ) (Y := d.Y) d.b x y
  refine ⟨w₁, cM, κ, ⟨?_, ?_, ?_⟩, kunf.rat_of_inFrame hw₁, ⟨1, (R.ε : ℤ), one_ne_zero, ?_, ?_⟩, hcMc, hκ,
    ⟨δ, hδ0, fun c => ⟨_, hcM c⟩⟩⟩
  ·
    intro w τ y g hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := CL.rEx d w
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, CL.frame_dil d R w r hrw hro hrf L.i₀ hy]
    exact CL.comm_dM L.i₀ _ (L.j_out g) _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := CL.rEx d w
    have hy' := CL.isDil_inv hy
    obtain ⟨t, ht, ha, hχ⟩ := CL.par_dil d R w L.i₀ hy'
    refine ⟨R.ι w y⁻¹, t, ht, by rw [ha]; ring_nf, hχ, ?_⟩
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, hw₁', CL.frame_dil d R w r hrw hro hrf L.i₀ hy, CL.frame_dil d R w r hrw hro hrf L.i₀ hy', neg_neg]
    exact CL.wM_dM L.i₀ _ _ _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, hrm, hrw, hro, hrf⟩ := CL.rEx d w
    obtain ⟨sc, hsc1, hsc2⟩ := hsc (r (-τ))
    refine ⟨sc, fun c => ?_, ?_⟩
    · apply kunf.inFrame_injective d.b
      rw [hfr, hfr, hcM, hcM, CL.frame_dil d R w r hrw hro hrf L.i₀ hy]
      have hxy : ((r τ : AF F) • (1 : AE F E)) * ((r (-τ) : AF F) • (1 : AE F E)) = 1 := by
        rw [smul_mul_smul_comm, one_mul, ← Units.val_mul, ← hr0, add_neg_cancel, hr1]; simp
      rw [CL.cB_dM hem _ _ _ _ _ hxy, hsc1]
      congr 1
      simp only [Mc]
      congr 1
      · funext j; exact smul_one_mul _ _
      · funext j; rw [map_smul, smul_one_mul]
      · rw [mul_assoc, smul_one_mul, smul_one_mul, smul_assoc, mul_smul]
    · rw [hsc2, hrm, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul, ← Atop.LD.n_succ L]
      congr 2
      push_cast; ring
  · simp [map_intCast]
  · rw [hw₁']; simp [CL.wM, map_intCast, map_one, he_def]

end PositivityTheory.SiegelWeilFormula.Act

end
end
