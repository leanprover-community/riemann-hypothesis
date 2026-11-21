import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FrAIntReindex
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsSub

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem locCong_iff_ent (hθ : IsSplitEquiv X p θ) (π : Op X p →+* ZMod (gOf p))
    (hker : RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)}) (hS : SplitA X p θ Q) (hA : AdaptA X p θ Q)
    (x : HAp X p) (Y : GL (IdxD D) (Op X p))
    (hY : ((glRed (algebraMap (Op X p) (FpX X p)) Y : GL (IdxD D) (FpX X p)) :
        Matrix (IdxD D) (IdxD D) (FpX X p)) =
      ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
        (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) :
    LocCong X p x ↔ EntA X p π Y := by
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  obtain ⟨hE1, hZ1, hB1, hE2, hZ2, hB2⟩ := hA
  set O := OvA X p
  set M := ((HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J x : GL (Fin X.B.I.n) (TpX X p)) :
    Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p))
  set Ym := (Y : Matrix (IdxD D) (IdxD D) (Op X p))
  set Yi := ((Y⁻¹ : GL (IdxD D) (Op X p)) : Matrix (IdxD D) (IdxD D) (Op X p))
  have hYm : ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      Matrix.reindex (idxEquiv X) (idxEquiv X) (M.map fun t => (θ t).1) *
      (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) = Ym.map ((↑) : O → FpX X p) := hY.symm
  have hZ : Yi.map ((↑) : O → FpX X p) * (((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
      (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) = 1 := by
    rw [← hY]
    have h1 : Yi * Ym = 1 := by
      simp only [Yi, Ym]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := congrArg (fun A => A.map (algebraMap (Op X p) (FpX X p))) h1
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  have c1 : ∀ u, crd1 X p θ Q ((M - 1) *ᵥ u) = (Ym.map ((↑) : O → FpX X p) - 1) *ᵥ crd1 X p θ Q u := by
    intro u
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, firstCoords_sub, firstCoords_mulVec, hYm, Matrix.sub_mulVec, Matrix.one_mulVec]
  have c2 : ∀ u, crd2 X p θ Q ((M - 1) *ᵥ u) = (Yiᵀ.map ((↑) : O → FpX X p) - 1) *ᵥ crd2 X p θ Q u := by
    intro u
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, secondCoords_sub, secondCoords_mulVec X p θ Q hθ x _ hZ, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.transpose_map]

  have hsplit : ∀ S y, InModP X p X.B.g S y ↔ CongSpan O (gA X p) (crd1 X p θ Q '' S) (crd1 X p θ Q y) ∧
      CongSpan O (gA X p) (crd2 X p θ Q '' S) (crd2 X p θ Q y) := fun S y => (imA_inModP_Bg X p S y).trans (hS S y)

  have ce : ∀ a : Fin D.R.rS, InModP X p X.B.g ((fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) '' {b | b.1 < a.1})
      ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.e0 a)) ↔
      (∀ i, i ∉ (Sum.inl '' {b : Fin D.R.rS | b.1 < a.1} : Set (IdxD D)) →
        π (Ym i (Sum.inl a)) = if i = Sum.inl a then 1 else 0) ∧
      (∀ i, i ∉ (fposA (D := D) '' {b : Fin D.R.rS | b.1 < a.1}) →
        π (Yi (fposA a) i) = if i = fposA a then 1 else 0) := by
    intro a
    rw [hsplit, Set.image_image, Set.image_image, c1, c2]
    refine and_congr ?_ ?_
    · exact clause_iff O π (gA X p) hker Ym _ (fun b => (Sum.inl b : IdxD D)) (fun b => hE1 b) _ _ _ (hE1 a)
    · have := clause_iff O π (gA X p) hker Yiᵀ _ (fposA (D := D)) (fun b => hE2 b) {b : Fin D.R.rS | b.1 < a.1}
        _ (fposA a) (hE2 a)
      simpa only [Matrix.transpose_apply] using this

  have cz : InModP X p X.B.g (Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b))
      ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 X.z0) ↔
      (∀ i, i ∉ (Sum.inl '' Set.univ : Set (IdxD D)) → π (Ym i zI) = if i = zI then 1 else 0) ∧
      (∀ i, i ∉ (fposA (D := D) '' Set.univ) → π (Yi zI i) = if i = zI then 1 else 0) := by
    rw [hsplit, ← Set.image_univ, Set.image_image, Set.image_image, c1, c2]
    refine and_congr ?_ ?_
    · exact clause_iff O π (gA X p) hker Ym _ (fun b => (Sum.inl b : IdxD D)) (fun b => hE1 b) _ _ _ hZ1
    · obtain ⟨z, hz, hz'⟩ := hZ2
      have hw : ∃ z', IntVec O z' ∧ -crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0) =
          Pi.single zI 1 + ((gA X p : O) : FpX X p) • z' :=
        ⟨-z, fun i => by simpa using neg_mem (hz i), by rw [hz', neg_add, neg_neg, smul_neg]⟩
      have hneg : (Yiᵀ.map ((↑) : O → FpX X p) - 1) *ᵥ crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0) =
          -((Yiᵀ.map ((↑) : O → FpX X p) - 1) *ᵥ -crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0)) := by
        rw [Matrix.mulVec_neg, neg_neg]
      rw [hneg, congSpan_neg]
      have := clause_iff O π (gA X p) hker Yiᵀ _ (fposA (D := D)) (fun b => hE2 b) Set.univ _ zI hw
      simpa only [Matrix.transpose_apply] using this

  have cw : ∀ j : Fin D.R.k, InModP X p X.B.g ((Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
      (fun j => PI.FinKW.vecV X.B.I p.1 (X.bw j)) '' {j' | j'.1 < j.1})
      ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw j)) ↔
      (∀ i, i ∉ (posW (r := D.R.rS) j : Set (IdxD D)) → π (Ym i (wI j)) = if i = wI j then 1 else 0) := by
    intro j
    have h0 : crd2 X p θ Q ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw j)) = 0 := by
      rw [c2]
      have : crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.bw j)) = 0 := by
        unfold crd2; rw [hB2 j]
        have : ((0 : Fin X.B.I.n → FpX X p) ∘ (idxEquiv X).symm) = 0 := rfl
        rw [this, Matrix.mulVec_zero, Matrix.mulVec_zero]
      rw [this, Matrix.mulVec_zero]
    rw [hsplit, h0, c1]
    simp only [congSpan_zero, and_true]
    let u : Fin D.R.rS ⊕ Fin D.R.k → IdxD D → FpX X p :=
      Sum.elim (fun b => crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.e0 b)))
        (fun j' => crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.bw j')))
    let pos : Fin D.R.rS ⊕ Fin D.R.k → IdxD D := Sum.elim Sum.inl wI
    let s : Set (Fin D.R.rS ⊕ Fin D.R.k) := Set.range Sum.inl ∪ Sum.inr '' {j' | j'.1 < j.1}
    have hset : crd1 X p θ Q '' ((Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
        (fun j => PI.FinKW.vecV X.B.I p.1 (X.bw j)) '' {j' | j'.1 < j.1}) = u '' s := by
      ext v; simp only [u, s, Set.mem_image, Set.mem_union, Set.mem_range, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨x, (⟨y, rfl⟩ | ⟨b, hb, rfl⟩), rfl⟩
        · exact ⟨Sum.inl y, Or.inl ⟨y, rfl⟩, rfl⟩
        · exact ⟨Sum.inr b, Or.inr ⟨b, hb, rfl⟩, rfl⟩
      · rintro ⟨c, (⟨y, rfl⟩ | ⟨b, hb, rfl⟩), rfl⟩
        · exact ⟨_, Or.inl ⟨y, rfl⟩, rfl⟩
        · exact ⟨_, Or.inr ⟨b, hb, rfl⟩, rfl⟩
    have hpos : pos '' s = posW (r := D.R.rS) j := by
      ext v; simp [pos, s, posW]
    rw [hset]
    have hu : ∀ b, ∃ z, IntVec O z ∧ u b = Pi.single (pos b) 1 + ((gA X p : O) : FpX X p) • z := by
      rintro (b | j')
      · exact hE1 b
      · exact hB1 j'
    have := clause_iff O π (gA X p) hker Ym u pos hu s _ (wI j) (hB1 j)
    rw [hpos] at this
    exact this
  unfold LocCong EntA
  rw [forall_congr' ce, cz, forall_congr' cw, forall_and]
  constructor
  · rintro ⟨⟨hP, hQ⟩, ⟨hR, hS'⟩, hT⟩; exact ⟨hP, hR, hT, hQ, hS'⟩
  · rintro ⟨hP, hR, hT, hQ, hS'⟩; exact ⟨⟨hP, hQ⟩, ⟨hR, hS'⟩, hT⟩

end Loc

end MassDataIdxSteps
end
end

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Pos

variable {r k : ℕ}

theorem frA_condE (a : Fin r) (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.castSucc a → i ≠ pe a') ↔ i ∉ (Sum.inl '' {b : Fin r | b.1 < a.1}) := by
  constructor
  · rintro h ⟨b, hb, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_castSucc_iff.mpr hb) (by rw [pe_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    have ha2 : (a' : ℕ) < a.1 := ha'
    refine ⟨⟨a', by omega⟩, ha2, ?_⟩
    rw [hi, pe_inl_of_lt ha']

theorem frA_condZ (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.last r → i ≠ pe a') ↔ i ∉ (Sum.inl '' Set.univ) := by
  constructor
  · rintro h ⟨b, -, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_last b) (by rw [pe_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    refine ⟨⟨a', ha'⟩, trivial, ?_⟩
    rw [hi, pe_inl_of_lt ha']

theorem frA_condF (a : Fin r) (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.castSucc a → i ≠ pf a') ↔
      i ∉ ((fun b : Fin r => (Sum.inr (Sum.inr (Fin.rev b)) : Formalism.FourierDecayAlt.S3.Idx r k)) '' {b : Fin r | b.1 < a.1}) := by
  constructor
  · rintro h ⟨b, hb, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_castSucc_iff.mpr hb) (by rw [pf_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    have ha2 : (a' : ℕ) < a.1 := ha'
    refine ⟨⟨a', by omega⟩, ha2, ?_⟩
    rw [hi, pf_of_lt ha']

theorem frA_condFZ (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.last r → i ≠ pf a') ↔
      i ∉ ((fun b : Fin r => (Sum.inr (Sum.inr (Fin.rev b)) : Formalism.FourierDecayAlt.S3.Idx r k)) '' Set.univ) := by
  constructor
  · rintro h ⟨b, -, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_last b) (by rw [pf_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    refine ⟨⟨a', ha'⟩, trivial, ?_⟩
    rw [hi, pf_of_lt ha']

end Pos

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

theorem ent_iff_nuG (π : Op X p →+* ZMod (gOf p)) (Y : GL (IdxD D) (Op X p)) :
    EntA X p π Y ↔ glRed π Y ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k := by
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  rw [mem_nuG_iff_flags, colFlag_iff', colW_iff, rowFlag_iff', ← map_inv, Fin.forall_fin_succ',
    Fin.forall_fin_succ']
  simp only [pe_castSucc, pe_last, pf_castSucc, pf_last]
  simp only [frA_condE, frA_condZ, frA_condF, frA_condFZ]
  unfold EntA
  constructor
  · rintro ⟨hP, hR, hT, hQ, hS⟩
    exact ⟨⟨hP, hR⟩, hT, ⟨hQ, hS⟩⟩
  · rintro ⟨⟨hP, hR⟩, hT, ⟨hQ, hS⟩⟩
    exact ⟨hP, hR, hT, hQ, hS⟩

variable (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (IdxD D) (FpX X p))

theorem transA_of (hθ : IsSplitEquiv X p θ) (π : Op X p →+* ZMod (gOf p))
    (hker : RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)}) (hS : SplitA X p θ Q) (hA : AdaptA X p θ Q) :
    TransA X p θ Q π := fun x _ Y hY =>
  (locCong_iff_ent X p θ Q hθ π hker hS hA x Y hY).trans (ent_iff_nuG X p π Y)

def StAdaptA : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ SplitA X p θ Q ∧ AdaptA X p θ Q

theorem stFrameA_of_adapt (hC : LatCoreX) (h : StAdaptA X p) : StFrameA X p := by
  obtain ⟨θ, hθ, Q, hL, hS, hA⟩ := h
  obtain ⟨π, hπ, hker⟩ := stResZ_holds X p
  exact stFrameA_of_trans X hC p ⟨θ, hθ, Q, hL, π, hπ, hker, transA_of X p θ Q hθ π hker hS hA⟩

theorem reduction_image_of_adapted (hb : AdBridgeIso X.B.I) (hC : LatCoreX) (h : StAdaptA X p) : LevelReductionImage X hb p :=
  reduction_image_of_frame X hb p (stFrameA_of_adapt X p hC h)

end Loc

end MassDataIdxSteps
end
end

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

abbrev mQJ : Matrix (IdxD D) (IdxD D) (FpX X p) :=
  (Q : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ * (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ

theorem mQJ_unit : IsUnit (mQJ X p θ Q).det := by
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, Matrix.det_reindex_self]
  exact (Units.isUnit (Matrix.GeneralLinearGroup.det Q)).mul (isUnit_det_split_form X p θ)

theorem secondCoords_eq_mulVec (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q v = mQJ X p θ Q *ᵥ (pr2 θ v ∘ (idxEquiv X).symm) := by
  unfold crd2; rw [Matrix.mulVec_mulVec]

theorem crd_surj (a b : IdxD D → FpX X p) : ∃ x, crd1 X p θ Q x = a ∧ crd2 X p θ Q x = b := by
  set w1 := (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ a
  set w2 := (mQJ X p θ Q)⁻¹ *ᵥ b
  refine ⟨fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j)), ?_, ?_⟩
  · have : pr1 θ (fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j))) ∘ (idxEquiv X).symm = w1 := by
      funext i; simp [pr1]
    unfold crd1; rw [this, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  · have : pr2 θ (fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j))) ∘ (idxEquiv X).symm = w2 := by
      funext i; simp [pr2]
    rw [secondCoords_eq_mulVec, this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (mQJ_unit X p θ Q), Matrix.one_mulVec]

theorem crd_inj (x : Fin X.B.I.n → TpX X p) (h1 : crd1 X p θ Q x = 0) (h2 : crd2 X p θ Q x = 0) : x = 0 := by
  have e1 : pr1 θ x ∘ (idxEquiv X).symm = 0 := by
    have := congrArg (fun v => (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ v) h1
    simp only [crd1, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  have e2 : pr2 θ x ∘ (idxEquiv X).symm = 0 := by
    have := congrArg (fun v => (mQJ X p θ Q)⁻¹ *ᵥ v) h2
    simp only [secondCoords_eq_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (mQJ_unit X p θ Q),
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  funext j
  have a1 := congrFun e1 (idxEquiv X j)
  have a2 := congrFun e2 (idxEquiv X j)
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] at a1 a2
  have : θ (x j) = 0 := Prod.ext a1 a2
  simpa using congrArg θ.symm this

theorem oEp_int (hL : LatBasis X p θ (reindex₂ X p Q)) (t : TpX X p) (ht : t ∈ OEp X p) :
    (θ t).1 ∈ OvA X p ∧ (θ t).2 ∈ OvA X p := by
  obtain ⟨j⟩ : Nonempty (IdxD D) := ⟨zI⟩
  obtain ⟨x1, hx1a, hx1b⟩ := crd_surj X p θ Q (Pi.single j 1) 0
  obtain ⟨x2, hx2a, hx2b⟩ := crd_surj X p θ Q 0 (Pi.single j 1)
  have hint : IntVec (OvA X p) (Pi.single j (1 : FpX X p)) := fun i => by
    by_cases h : i = j
    · subst h; simp [ValuationSubring.one_mem]
    · simp [h, ValuationSubring.zero_mem]
  have hz : IntVec (OvA X p) (0 : IdxD D → FpX X p) := fun _ => ValuationSubring.zero_mem _
  have l1 := imA_lat_OEp X p ht ((latCrd_of X p θ Q hL x1).2 ⟨hx1a ▸ hint, hx1b ▸ hz⟩)
  have l2 := imA_lat_OEp X p ht ((latCrd_of X p θ Q hL x2).2 ⟨hx2a ▸ hz, hx2b ▸ hint⟩)
  have c1 := ((latCrd_of X p θ Q hL _).1 l1).1 j
  have c2 := ((latCrd_of X p θ Q hL _).1 l2).2 j
  rw [firstCoords_tensor_smul, hx1a] at c1
  rw [secondCoords_tensor_smul, hx2b] at c2
  simp at c1 c2
  exact ⟨c1, c2⟩

def OEpSplit : Prop := θ.symm (1, 0) ∈ OEp X p ∧ θ.symm (0, 1) ∈ OEp X p

theorem splitA_of_lat (hL : LatBasis X p θ (reindex₂ X p Q)) (hO : OEpSplit X p θ) : SplitA X p θ Q :=
  splitA_of X p θ Q (oEp_int X p θ Q hL) hO.1 hO.2 (latCrd_of X p θ Q hL) (crd_inj X p θ Q) (crd_surj X p θ Q)

theorem reduction_image_of_adapted_mod (hb : AdBridgeIso X.B.I) (hC : LatCoreX)
    (h : ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧ OEpSplit X p θ ∧
      ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ AdaptA X p θ Q) : LevelReductionImage X hb p := by
  obtain ⟨θ, hθ, hO, Q, hL, hA⟩ := h
  exact reduction_image_of_adapted X p hb hC ⟨θ, hθ, Q, hL, splitA_of_lat X p θ Q hL hO, hA⟩

end Loc

end MassDataIdxSteps
end
end
