import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstCoordsMulVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CongSpanSingleIff

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
open scoped TensorProduct

theorem frA_reindex_mul {R m n : Type} [CommRing R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (A B : Matrix m m R) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B :=
  (Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm).symm

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem secondCoords_mulVec (hθ : IsSplitEquiv X p θ) (x : HAp X p) (Z : Matrix (IdxD D) (IdxD D) (FpX X p))
    (hZ : Z * (((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
        (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) = 1) (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q (((HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J x : GL (Fin X.B.I.n) (TpX X p)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ v) = Zᵀ *ᵥ crd2 X p θ Q v := by
  set e := idxEquiv X
  set M1 := Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ x) with hM1
  set M2 := Matrix.reindex e e (cmp2 X.B.I.cm.sig X.B.I.J θ x) with hM2
  set J' := Matrix.reindex e e (jm1 X.B.I.J θ) with hJ'
  set Qm := (Q : Matrix (IdxD D) (IdxD D) (FpX X p))
  set Qi := ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p))
  have hQ : Qm * Qi = 1 := by
    simp only [Qm, Qi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hU : M1ᵀ * (J'ᵀ * M2) = J'ᵀ := by
    have h0 := cmp_unit X.B.I.cm.sig X.B.I.J θ hθ x
    have h1 := congrArg (fun A => Matrix.reindex e e Aᵀ) h0
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h1
    rw [frA_reindex_mul, frA_reindex_mul] at h1
    simpa [hM1, hM2, hJ', Matrix.transpose_reindex] using h1
  have hYZ : (Qi * M1 * Qm) * Z = 1 := mul_eq_one_comm.mp hZ
  have hQY : Qm * (Qi * M1 * Qm) = M1 * Qm := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have key : Qmᵀ * (J'ᵀ * M2) = Zᵀ * (Qmᵀ * J'ᵀ) := by
    calc Qmᵀ * (J'ᵀ * M2) = ((Qi * M1 * Qm) * Z)ᵀ * (Qmᵀ * (J'ᵀ * M2)) := by
          rw [hYZ, Matrix.transpose_one, Matrix.one_mul]
      _ = Zᵀ * ((Qm * (Qi * M1 * Qm))ᵀ * (J'ᵀ * M2)) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul Qm]; simp only [Matrix.mul_assoc]
      _ = Zᵀ * (Qmᵀ * (M1ᵀ * (J'ᵀ * M2))) := by
          rw [hQY, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Zᵀ * (Qmᵀ * J'ᵀ) := by rw [hU]
  unfold crd2
  rw [secondProj_split_mulVec]
  have hr : ((((HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J x : GL (Fin X.B.I.n) (TpX X p)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)).map fun t => (θ t).2) *ᵥ pr2 θ v) ∘ e.symm =
      M2 *ᵥ (pr2 θ v ∘ e.symm) := by
    rw [hM2, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    have : (pr2 θ v ∘ e.symm) ∘ e.symm.symm = pr2 θ v := by funext i; simp
    rw [this]; rfl
  have key' : Qmᵀ * J'ᵀ * M2 = Zᵀ * Qmᵀ * J'ᵀ := by rw [Matrix.mul_assoc, key, Matrix.mul_assoc]
  rw [hr, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun A => A *ᵥ (pr2 θ v ∘ e.symm)) key'

end Loc

end MassDataIdxSteps
end
end

section
noncomputable section

namespace MassDataIdxFrA

open Matrix

variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem clause_iff (hker : RingHom.ker π = Ideal.span {γ}) (Y : Matrix ι ι O) {β : Type} (u : β → ι → F)
    (pos : β → ι) (hu : ∀ b, ∃ z, IntVec O z ∧ u b = Pi.single (pos b) 1 + (γ : F) • z) (s : Set β)
    (w : ι → F) (j : ι) (hw : ∃ z, IntVec O z ∧ w = Pi.single j 1 + (γ : F) • z) :
    CongSpan O γ (u '' s) ((Y.map ((↑) : O → F) - 1) *ᵥ w) ↔
      ∀ i, i ∉ pos '' s → π (Y i j) = if i = j then 1 else 0 := by
  classical
  have hdiv : ∀ a : O, π a = 0 ↔ ∃ c : O, a = γ * c := by
    intro a
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [← hc, mul_comm]⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, mul_comm]⟩
  have hsm : ∀ (a : O) (x : ι → F), a • x = (a : F) • x := fun a x => rfl
  obtain ⟨z, hz, rfl⟩ := hw
  set Y' := Y.map ((↑) : O → F) with hY'
  let cO : ι → O := fun i => Y i j - (if i = j then 1 else 0)
  have hcO : ∀ i, (cO i : F) = (Y i j : F) - (if i = j then 1 else 0) := by
    intro i
    by_cases hij : i = j <;> simp [cO, hij]
  have hcol : (Y' - 1) *ᵥ Pi.single j (1 : F) = ∑ i, (cO i : F) • Pi.single i (1 : F) := by
    ext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hcO]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hY', Matrix.one_apply]
  have hint : ∀ i, ((Y' - 1) *ᵥ z) i ∈ O := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply, hY', Matrix.map_apply]
    refine _root_.sum_mem fun l _ => mul_mem (sub_mem (Y i l).2 ?_) (hz l)
    split_ifs
    · exact one_mem O
    · exact zero_mem O
  have hentry : ∀ i, ((Y' - 1) *ᵥ (Pi.single j 1 + (γ : F) • z)) i =
      (cO i : F) + (γ : F) * ((Y' - 1) *ᵥ z) i := by
    intro i
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcol,
      Finset.sum_apply]
    simp [Pi.single_apply]
  constructor
  · rintro ⟨W, hW, z', hz', hv⟩ i hi
    have key : ∀ v ∈ Submodule.span O (u '' s), ∃ c : O, v i = (γ : F) * c := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, rfl⟩ := hx
        obtain ⟨zb, hzb, hub⟩ := hu b
        refine ⟨⟨zb i, hzb i⟩, ?_⟩
        have hne : i ≠ pos b := fun h => hi ⟨b, hb, h.symm⟩
        simp [hub, Pi.single_apply, hne]
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨c1, h1⟩ := hx
        obtain ⟨c2, h2⟩ := hy
        exact ⟨c1 + c2, by rw [Pi.add_apply, h1, h2]; push_cast; ring⟩
      | smul a x _ hx =>
        obtain ⟨c, h⟩ := hx
        refine ⟨a * c, ?_⟩
        rw [hsm, Pi.smul_apply, smul_eq_mul, h]
        push_cast
        ring
    obtain ⟨c, hc⟩ := key W hW
    have hvi := congrFun hv i
    rw [hentry i, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc] at hvi
    have hO : cO i = γ * ⟨(c : F) + z' i - ((Y' - 1) *ᵥ z) i,
        sub_mem (add_mem c.2 (hz' i)) (hint i)⟩ := by
      apply Subtype.ext
      show (cO i : F) = (γ : F) * ((c : F) + z' i - ((Y' - 1) *ᵥ z) i)
      linear_combination hvi
    have h0 := (hdiv _).2 ⟨_, hO⟩
    simp only [cO, map_sub, sub_eq_zero] at h0
    rw [h0]
    split_ifs <;> simp
  · intro hcond
    have hsel : ∀ i, i ∈ pos '' s → ∃ b, b ∈ s ∧ pos b = i := fun i hi => hi
    choose bsel hbs hpos using hsel
    have hout : ∀ i, i ∉ pos '' s → ∃ e : O, cO i = γ * e := by
      intro i hi
      apply (hdiv _).1
      simp only [cO, map_sub, hcond i hi]
      split_ifs <;> simp
    choose dsel hdsel using hout
    choose zb hzb hub using hu
    refine ⟨∑ i, (if h : i ∈ pos '' s then cO i • u (bsel i h) else 0), ?_,
      ∑ i, ((if h : i ∈ pos '' s then 0 else (dsel i h : F) • Pi.single i (1 : F)) -
        (if h : i ∈ pos '' s then (cO i : F) • zb (bsel i h) else 0)) + (Y' - 1) *ᵥ z, ?_, ?_⟩
    · refine _root_.sum_mem fun i _ => ?_
      split_ifs with h
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨bsel i h, hbs i h, rfl⟩)
      · exact Submodule.zero_mem _
    · intro l
      rw [Pi.add_apply, Finset.sum_apply]
      refine add_mem (_root_.sum_mem fun i _ => ?_) (hint l)
      rw [Pi.sub_apply]
      refine sub_mem ?_ ?_
      · split_ifs with h
        · exact zero_mem O
        · rw [Pi.smul_apply, smul_eq_mul]
          exact mul_mem (dsel i h).2 (by rw [Pi.single_apply]; split_ifs; exacts [one_mem O, zero_mem O])
      · split_ifs with h
        · rw [Pi.smul_apply, smul_eq_mul]
          exact mul_mem (cO i).2 (hzb _ l)
        · exact zero_mem O
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hcol, smul_add, Finset.smul_sum, ← add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : i ∈ pos '' s
      · simp only [h, dif_pos, hsm, hub, hpos i h, sub_zero, zero_sub, smul_add, smul_neg, smul_smul]
        rw [mul_comm]
        abel
      · simp only [h, dif_neg, not_false_eq_true, sub_zero, zero_add, smul_smul]
        rw [hdsel i h]
        push_cast
        rfl

end MassDataIdxFrA
end
end

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

def fposA (a : Fin D.R.rS) : IdxD D := Sum.inr (Sum.inr (Fin.rev a))

def EntA (π : Op X p →+* ZMod (gOf p)) (Y : GL (IdxD D) (Op X p)) : Prop :=
  (∀ a : Fin D.R.rS, ∀ i, i ∉ (Sum.inl '' {b : Fin D.R.rS | b.1 < a.1} : Set (IdxD D)) →
    π ((Y : Matrix (IdxD D) (IdxD D) (Op X p)) i (Sum.inl a)) = if i = Sum.inl a then 1 else 0) ∧
  (∀ i, i ∉ (Sum.inl '' Set.univ : Set (IdxD D)) →
    π ((Y : Matrix (IdxD D) (IdxD D) (Op X p)) i zI) = if i = zI then 1 else 0) ∧
  (∀ j : Fin D.R.k, ∀ i, i ∉ (posW (r := D.R.rS) j : Set (IdxD D)) →
    π ((Y : Matrix (IdxD D) (IdxD D) (Op X p)) i (wI j)) = if i = wI j then 1 else 0) ∧
  (∀ a : Fin D.R.rS, ∀ i, i ∉ (fposA (D := D) '' {b : Fin D.R.rS | b.1 < a.1}) →
    π (((Y⁻¹ : GL (IdxD D) (Op X p)) : Matrix (IdxD D) (IdxD D) (Op X p)) (fposA a) i) =
      if i = fposA a then 1 else 0) ∧
  (∀ i, i ∉ (fposA (D := D) '' Set.univ) →
    π (((Y⁻¹ : GL (IdxD D) (Op X p)) : Matrix (IdxD D) (IdxD D) (Op X p)) zI i) = if i = zI then 1 else 0)

theorem firstCoords_sub (a b : Fin X.B.I.n → TpX X p) : crd1 X p θ Q (a - b) = crd1 X p θ Q a - crd1 X p θ Q b := by
  unfold crd1
  rw [map_sub, show (pr1 θ a - pr1 θ b) ∘ (idxEquiv X).symm =
    pr1 θ a ∘ (idxEquiv X).symm - pr1 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_sub]

theorem secondCoords_sub (a b : Fin X.B.I.n → TpX X p) : crd2 X p θ Q (a - b) = crd2 X p θ Q a - crd2 X p θ Q b := by
  unfold crd2
  rw [map_sub, show (pr2 θ a - pr2 θ b) ∘ (idxEquiv X).symm =
    pr2 θ a ∘ (idxEquiv X).symm - pr2 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_sub, Matrix.mulVec_sub]

end Loc

end MassDataIdxSteps
end
end
