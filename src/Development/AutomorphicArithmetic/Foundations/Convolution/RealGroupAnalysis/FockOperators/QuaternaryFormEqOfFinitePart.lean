import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.HermAct
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F]
  [IsTotallyComplex E]

private theorem adeleMap_snd (a : A F) (ha : a.2 = 0) : (AdeleBaseChange.adeleMap F E a).2 = 0 := by
  change AdeleBaseChange.finiteAdeleMap F E a.2 = 0
  rw [ha, map_zero]

private theorem mkE_snd (D : Dat F E) (u t : A F) (hu : u.2 = 0) (ht : t.2 = 0) : (D.mkE u t).2 = 0 := by
  change (AdeleBaseChange.adeleMap F E u).2 + (AdeleBaseChange.adeleMap F E t).2 * (rt D.θ : A E).2 = 0
  rw [adeleMap_snd u hu, adeleMap_snd t ht, zero_mul, add_zero]

private theorem mkE_sub (D : Dat F E) (u t u' t' : A F) :
    D.mkE (u - u') (t - t') = D.mkE u t - D.mkE u' t' := by
  simp only [Dat.mkE, map_sub]
  ring

private theorem snd_sub (a b : A E) : (a - b).2 = a.2 - b.2 := rfl

private theorem bar_snd (D : Dat F E) (z z' : A E) (h : z.2 = z'.2) : (D.bar z).2 = (D.bar z').2 := by
  obtain ⟨-, h2, h3, h4⟩ := hermAct F E D
  have hw : (z - z').2 = 0 := by rw [snd_sub, h, sub_self]
  have h5 := h4 (D.co (z - z') 0) (D.co (z - z') 1) (by rw [h3]; exact hw)
  have h6 : D.bar (z - z') = D.mkE (D.co (z - z') 0) (-D.co (z - z') 1) := by rw [← h2, h3]
  have h7 : (D.bar (z - z')).2 = 0 := by
    rw [h6]
    refine mkE_snd D _ _ h5.1 ?_
    change -(D.co (z - z') 1).2 = 0
    rw [h5.2, neg_zero]
  rw [map_sub, snd_sub] at h7
  exact sub_eq_zero.1 h7

private theorem mkE_inj (D : Dat F E) (a b a' b' : A F) (h : (D.mkE a b).2 = (D.mkE a' b').2) :
    a.2 = a'.2 ∧ b.2 = b'.2 := by
  obtain ⟨-, -, -, h4⟩ := hermAct F E D
  have h5 := h4 (a - a') (b - b') (by rw [mkE_sub, snd_sub, h, sub_self])
  exact ⟨sub_eq_zero.1 h5.1, sub_eq_zero.1 h5.2⟩

end

theorem UpperTheory.ConvolutionTheory.R2.Fo.actFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (y : GL (Fin 2) (Cinf E)) v, finPartPi (D.act (infGL E 2 y) v) = finPartPi v := by
  intro F E _ _ _ _ _ _ _ D y v
  have h1 := (hermAct F E D).1 (infGL E 2 y) v
  have hg : ∀ i j, pFin E ((infGL E 2 y).val i j) = (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j := fun i j =>
    congrArg (fun g : GL (Fin 2) (Af E) => g.val i j) (pFin_infGL y)
  have hone : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := by
    intro i j
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.one_apply_ne e]
  have hb : ∀ i j, pFin E (D.bar ((infGL E 2 y).val i j)) = (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j := by
    intro i j
    have e : pFin E (D.bar ((infGL E 2 y).val i j)) = pFin E (D.bar ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j)) :=
      bar_snd D _ _ ((hg i j).trans (hone i j))
    rw [e, hone]
    congr 1
    by_cases e' : i = j
    · subst e'; simp
    · simp [Matrix.one_apply_ne e']
  have hm1 : (infGL E 2 y).val.map (pFin E) = 1 := by
    exact Matrix.ext fun i j => hg i j
  have hm2 : (((infGL E 2 y).val.map D.bar)ᵀ).map (pFin E) = 1 := by
    refine Matrix.ext fun i j => ?_
    have := hb j i
    simp only [Matrix.map_apply, Matrix.transpose_apply]
    rw [this, Matrix.one_apply, Matrix.one_apply]
    simp [eq_comm]
  have hH : (D.herm (D.act (infGL E 2 y) v)).map (pFin E) = (D.herm v).map (pFin E) := by
    rw [h1, Matrix.map_mul, Matrix.map_mul, hm1, hm2, one_mul, mul_one]
  have e00 := congrFun (congrFun hH 0) 0
  have e01 := congrFun (congrFun hH 0) 1
  have e11 := congrFun (congrFun hH 1) 1
  have a1 := mkE_inj D _ _ _ _ (show (D.mkE _ 0).2 = (D.mkE _ 0).2 from e00)
  have a2 := mkE_inj D _ _ _ _ (show (D.mkE _ _).2 = (D.mkE _ _).2 from e01)
  have a3 := mkE_inj D _ _ _ _ (show (D.mkE _ 0).2 = (D.mkE _ 0).2 from e11)
  funext i
  fin_cases i
  · exact a3.1
  · exact a1.1
  · exact a2.1
  · exact a2.2
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem mul_eq_of_inf_zero {F : Type} [Field F] [NumberField F] (x u u' : A F) (hx : x.1 = 0)
    (h : u.2 = u'.2) : x * u = x * u' := by
  apply Prod.ext
  · change x.1 * u.1 = x.1 * u'.1
    rw [hx, zero_mul, zero_mul]
  · change x.2 * u.2 = x.2 * u'.2
    rw [h]

private theorem quaternaryForm_eq_of_finitePart {F : Type} [Field F] [NumberField F] (δ : F) (a v v' : V4 F)
    (ha : ∀ i, (a i).1 = 0) (h : finPartPi v = finPartPi v') : B4 δ a v = B4 δ a v' := by
  have e : ∀ i j, a i * v j = a i * v' j := fun i j =>
    mul_eq_of_inf_zero _ _ _ (ha i) (congrFun h j)
  simp only [B4, e]

theorem UpperTheory.ConvolutionTheory.R2.Fo.lFix :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (y : GL (Fin 2) (Cinf E)) Λ, ∀ φ ∈ Fix D.δ Λ, W.L (infGL E 2 y) φ ∈ Fix D.δ Λ := by
  intro F E _ _ _ _ _ _ _ D W y Λ φ hφ
  have hφ' : ∀ a : V4 F, (∀ i, (a i).1 = 0 ∧ (a i).2 ∈ Λ) → ∀ v,
      φ.1 (v + a) = φ.1 v ∧ ψ (B4 D.δ a v) * φ.1 v = φ.1 v := hφ
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hinv : (infGL E 2 y)⁻¹ = infGL E 2 y⁻¹ := (map_inv (infGL E 2) y).symm
  have hfin := UpperTheory.ConvolutionTheory.R2.Fo.actFin F E D y⁻¹

  have key : ∀ a : V4 F, (∀ i, (a i).1 = 0) → D.act (infGL E 2 y⁻¹) a = a := by
    intro a ha
    let e : A F := (0, 1)
    have hea : e • a = a := by
      funext i
      apply Prod.ext
      · change (0 : _) * (a i).1 = (a i).1
        rw [ha i, mul_zero]
      · change (1 : _) * (a i).2 = (a i).2
        rw [one_mul]
    have hinf : D.act (infGL E 2 y⁻¹) a = e • D.act (infGL E 2 y⁻¹) a := by
      rw [hρ, ← Matrix.mulVec_smul, hea]
    funext i
    apply Prod.ext
    · rw [hinf, ha i]
      change (0 : _) * _ = 0
      rw [zero_mul]
    · exact congrFun (hfin a) i
  change ∀ a : V4 F, (∀ i, (a i).1 = 0 ∧ (a i).2 ∈ Λ) → ∀ v,
    (W.L (infGL E 2 y) φ).1 (v + a) = (W.L (infGL E 2 y) φ).1 v ∧
      ψ (B4 D.δ a v) * (W.L (infGL E 2 y) φ).1 v = (W.L (infGL E 2 y) φ).1 v
  intro a ha v
  have hfix := key a fun i => (ha i).1
  have hact : D.act (infGL E 2 y⁻¹) (v + a) = D.act (infGL E 2 y⁻¹) v + a := by
    rw [hρ, Matrix.mulVec_add, ← hρ, ← hρ, hfix]
  have hB : B4 D.δ a v = B4 D.δ a (D.act (infGL E 2 y⁻¹) v) :=
    quaternaryForm_eq_of_finitePart _ _ _ _ (fun i => (ha i).1) (hfin v).symm
  refine ⟨?_, ?_⟩
  · rw [W.L_apply, W.L_apply, hinv, hact, (hφ' a ha _).1]
  · rw [W.L_apply, hinv, mul_left_comm, hB, (hφ' a ha _).2]
end
