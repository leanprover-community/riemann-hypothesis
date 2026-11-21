import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrincipalCongruenceInDefiniteLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContained
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalCongruence_in_definiteLevel : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J, (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨_, h⟩ = 1 := by
  first | exact @GlobalTheory.VFormCong.exists_cong_levEnv | exact GlobalTheory.VFormCong.exists_cong_levEnv | (intros; apply GlobalTheory.VFormCong.exists_cong_levEnv <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevCosetFin

open ReciprocityTheory.Aut

section Grp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem natCast_isUnit_AL {d : ℕ} (hd : 0 < d) : IsUnit (d : AL L) := by
  have e : (d : AL L) = algebraMap L (AL L) (d : L) := (map_natCast _ d).symm
  rw [e]
  exact (IsUnit.mk0 (d : L) (Nat.cast_ne_zero.2 hd.ne')).map _

theorem exists_finset_of_bdd (d : ℕ) (hd : 0 < d) (S : Set (GAf L n))
    (hS : ∀ κ ∈ S, ∀ i j, (d : AL L) * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L ∧
        (d : AL L) * ((κ⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L) :
    ∃ F : Finset (GAf L n), ∀ κ ∈ S, ∃ f ∈ F, f⁻¹ * κ ∈ Umax L n := by
  classical
  obtain ⟨Q, hQ, c, hc⟩ := GlobalTheory.IsotOrth.exists_finite_class (F := NumberField.maximalRealSubfield L) (E := L)
    (d * d) (Nat.mul_pos hd hd)
  haveI := hQ
  let cls : GAf L n → Fin n → Fin n → Q := fun κ i j =>
    if h : (d : AL L) * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L then c ⟨_, h⟩ else c 0
  have key : ∀ a ∈ S, ∀ b ∈ S, cls a = cls b → a⁻¹ * b ∈ Umax L n := by
    intro a ha b hb hab
    have hdiff : ∀ k l, ∃ y ∈ ALint L, (b.1 : Matrix (Fin n) (Fin n) (AL L)) k l -
        (a.1 : Matrix (Fin n) (Fin n) (AL L)) k l = (d : AL L) * y := by
      intro k l
      have e := congrFun (congrFun hab k) l
      simp only [cls, dif_pos (hS a ha k l).1, dif_pos (hS b hb k l).1] at e
      obtain ⟨z, hz⟩ := hc _ _ e.symm
      refine ⟨z.1, z.2, ?_⟩
      have hz' := congrArg Subtype.val hz
      apply (natCast_isUnit_AL (L := L) hd).mul_left_cancel
      push_cast at hz'
      rw [mul_sub, hz', mul_assoc]
    choose y hy hye using hdiff
    have h0 : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      have : (((a⁻¹ * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
      simpa using this
    have h1 : (((a⁻¹ * b).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 +
        ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) *
          ((b.1 : Matrix (Fin n) (Fin n) (AL L)) - (a.1 : Matrix (Fin n) (Fin n) (AL L))) := by
      rw [Matrix.mul_sub, h0, add_sub_cancel]
      rfl
    intro i j
    show (((a⁻¹ * b).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
    rw [h1, Matrix.add_apply, Matrix.mul_apply]
    refine add_mem ?_ (Subring.sum_mem _ fun k _ => ?_)
    · rw [Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · rw [Matrix.sub_apply, hye k j, ← mul_assoc, mul_comm _ (d : AL L)]
      exact mul_mem (hS a ha i k).2 (hy k j)
  let T : Set (Fin n → Fin n → Q) := cls '' S
  have hT : T.Finite := Set.toFinite T
  let rep : (Fin n → Fin n → Q) → GAf L n := fun t => if h : t ∈ T then h.choose else 1
  refine ⟨hT.toFinset.image rep, fun κ hκ => ?_⟩
  have ht : cls κ ∈ T := ⟨κ, hκ, rfl⟩
  have hr : rep (cls κ) = ht.choose := dif_pos ht
  refine ⟨rep (cls κ), Finset.mem_image.2 ⟨cls κ, hT.mem_toFinset.2 ht, rfl⟩, ?_⟩
  rw [hr]
  exact key _ ht.choose_spec.1 _ hκ ht.choose_spec.2

end Grp

end GlobalTheory.LevCosetFin

namespace GlobalTheory.LevCosetFin

section Den

variable {D : D7}

theorem comm_mem_intT {x : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F}
    (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)) x ∈ GlobalTheory.LatCongImage.intT D.host.F := by
  induction hx using Subring.closure_induction with
  | mem z hz =>
    apply Subring.subset_closure
    rcases hz with ⟨⟨s, t, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
    · right
      exact ⟨t, by simp⟩
    · left
      exact ⟨a, ha, by simp⟩
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end Den

end GlobalTheory.LevCosetFin

namespace GlobalTheory.LevCosetFin

section Den2

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_den (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (P : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (hF : D.host.F = maximalRealSubfield D.host.E) (hP : Formalism.IndefR.principalLevelFrame.StdPsi hF P)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∃ d : ℕ, 0 < d ∧ ∀ κ, (finHom V).rangeRestrict (P.ψ κ) ∈ (levEnv V β Ld).J → ∀ i j,
      (d : AL D.host.E) * (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) i j ∈ ALint D.host.E := by
  obtain ⟨⟨B, B', hBB', hB'B, hmat⟩, -⟩ := hP
  let cmr : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F →+* FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)).toAlgHom.toRingHom
  let βs := (β.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).map cmr
  let βi := ((β⁻¹).1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).map cmr
  obtain ⟨d, hd, hdm⟩ := GlobalTheory.LatCongImage.exists_nat_mul_mem_family D.host.F
    (fun p : ((Fin V.rank × Fin n) ⊕ (Fin n × Fin V.rank)) ⊕ ((Fin V.rank × Fin V.rank) ⊕ (Fin V.rank × Fin V.rank)) =>
      Sum.elim (Sum.elim (fun q => B q.1 q.2) (fun q => B' q.1 q.2))
        (Sum.elim (fun q => βs q.1 q.2) (fun q => βi q.1 q.2)) p)
  refine ⟨d ^ 4, by positivity, fun κ hκ i j => ?_⟩
  have h1 : Formalism.IndefR.Lev.finE V (P.ψ κ) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Formalism.IndefR.Lev.flag1L Ld) := hκ
  obtain ⟨y, hy⟩ := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev h1)
  have hM1 := congrArg (fun g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => (g.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) hy
  set Mf := (finHom V (P.ψ κ)).1 with hMf
  have hM2 : β.1 * ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map Subtype.val) *
      (β⁻¹).1 = Mf.map (Formalism.IndefR.Lev.swapAE D) := hM1
  let Ym := ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map Subtype.val).map cmr
  have hback : (Mf.map (Formalism.IndefR.Lev.swapAE D)).map cmr = Mf := by
    ext a b
    show (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F))
      ((Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E) (Mf a b)) = Mf a b
    rw [← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]
  have hM3 : Mf = βs * Ym * βi := by
    rw [← hback, ← hM2, Matrix.map_mul, Matrix.map_mul]
  set K := (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm with hK
  have hK2 : K = B' * Mf * B := by
    have e := hmat κ
    have e' : Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ) = Mf := rfl
    rw [e'] at e
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB'B, Matrix.one_mul, Matrix.mul_assoc, hB'B, Matrix.mul_one]
  have hκij : (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) i j = Formalism.IndefR.principalLevelFrame.tensCastR hF (K i j) := by
    rw [hK, Matrix.map_apply, RingEquiv.apply_symm_apply]
  let Bs' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • B'
  let Bs : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • B
  let βs' : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • βs
  let βi' : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • βi
  let Ms : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := βs' * Ym * βi'
  have hB'1 : ∀ a b, Bs' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * B' a b ∈ _; exact hdm (Sum.inl (Sum.inr (a, b)))
  have hB1 : ∀ a b, Bs a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * B a b ∈ _; exact hdm (Sum.inl (Sum.inl (a, b)))
  have hβs1 : ∀ a b, βs' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * βs a b ∈ _; exact hdm (Sum.inr (Sum.inl (a, b)))
  have hβi1 : ∀ a b, βi' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * βi a b ∈ _; exact hdm (Sum.inr (Sum.inr (a, b)))
  have hY1 : ∀ a b, Ym a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b =>
    comm_mem_intT (D := D) ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b).2
  have hMs : ∀ a b, Ms a b ∈ GlobalTheory.LatCongImage.intT D.host.F :=
    GlobalTheory.LatCongImage.mul_apply_mem _ _ _ (GlobalTheory.LatCongImage.mul_apply_mem _ _ _ hβs1 hY1) hβi1
  have hint : ((d ^ 4 : ℕ) : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * K i j ∈ GlobalTheory.LatCongImage.intT D.host.F := by
    have hK3 : ((d ^ 4 : ℕ) : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • K = Bs' * Ms * Bs := by
      rw [hK2, hM3]
      simp only [Bs', Bs, Ms, βs', βi', Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      congr 1
      push_cast
      ring
    have e := congrFun (congrFun hK3 i) j
    rw [Matrix.smul_apply, smul_eq_mul] at e
    rw [e]
    exact GlobalTheory.LatCongImage.mul_apply_mem _ _ _ (GlobalTheory.LatCongImage.mul_apply_mem _ _ _ hB'1 hMs) hB1 i j
  rw [hκij, ← map_natCast (Formalism.IndefR.principalLevelFrame.tensCastR hF) (d ^ 4), ← map_mul]
  exact GlobalTheory.LatCongImage.swap_mem D.host.F hF hint

end Den2

end GlobalTheory.LevCosetFin

open GlobalTheory.LevCosetFin in

theorem GlobalTheory.LevCosetFin.preimage_levEnv_finite_cosets : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ F : Finset (GAf D.host.E D.R.nV), ∀ κ, (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J → ∃ f ∈ F, f⁻¹ * κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := by
  intro D cf nch tp X M rep hA j t
  obtain ⟨d, hd, hden⟩ := exists_den (Vc D j) D.R.nV (hA.PV j) hA.hF (hA.stdV j) (X.R.βV j) (X.R.datVt j t)
  obtain ⟨F, hF⟩ := exists_finset_of_bdd d hd
    {κ | (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J}
    (fun κ hκ a b => ⟨hden κ hκ a b, hden κ⁻¹ (by
      show (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ⁻¹) ∈ _
      rw [map_inv, map_inv]
      exact inv_mem hκ) a b⟩)
  exact ⟨F, fun κ hκ => hF κ hκ⟩
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteLevel_preimage_finitely_many_cosets : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ F : Finset (GAf D.host.E D.R.nV), ∀ κ, (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J → ∃ f ∈ F, f⁻¹ * κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := by
  atlas_forward_decl GlobalTheory.LevCosetFin.preimage_levEnv_finite_cosets
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.VFormCls

open Formalism.IndefR.Bridge

theorem reps_inj {G Γ' : Type} [Group G] [Group Γ'] {ι : Γ' →* G} {J : Subgroup G} {I : Type} {y : I → G}
    (hy : IsReps ι J y) : Function.Injective y := by
  intro i i' h
  exact (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨1, 1, by simp [h]⟩

theorem transport {G G' Γ' : Type} [Group G] [Group G'] [Group Γ'] (Γ : Subgroup G) (ι : Γ' →* G')
    (hι : Function.Injective ι) (φ : G →* G') (hφ : Function.Bijective φ) (a : G)
    (hrat : ∀ h, h ∈ Γ ↔ ∃ γ, ι γ = φ (a⁻¹ * h * a)) (J' : Subgroup G') {I : Type} [Fintype I]
    (y : I → G') (hy : IsReps ι J' y) :
    ∃ T : Finset G, (∀ g : G, ∃! t, t ∈ T ∧ ∃ (γ : Γ) (κ : G), κ ∈ J'.comap φ ∧ g = (γ : G) * t * κ) ∧
      ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (F F' : G' → W),
        adInner ι J' y F F' = ∑ t ∈ T, ((Nat.card {γ : Γ // t⁻¹ * (γ : G) * t ∈ J'.comap φ} : ℕ) : ℂ)⁻¹ *
          inner ℂ (F (φ (a⁻¹ * t))) (F' (φ (a⁻¹ * t))) := by
  classical
  let e : G ≃* G' := MulEquiv.ofBijective φ hφ
  have he : ∀ x, φ (e.symm x) = x := fun x => e.apply_symm_apply x
  let t : I → G := fun i => a * e.symm (y i)
  have hty : ∀ i, φ (a⁻¹ * t i) = y i := by
    intro i; simp only [t, ← mul_assoc, inv_mul_cancel, one_mul, he]
  have tinj : Function.Injective t := by
    intro i i' h
    apply reps_inj hy
    rw [← hty i, ← hty i', h]

  have hrat' : ∀ γ : Γ, ∃ γ', ι γ' = φ (a⁻¹ * γ * a) := fun γ => (hrat γ).1 γ.2

  have key : ∀ (g : G) (i : I), (∃ (γ : Γ) (κ : G), κ ∈ J'.comap φ ∧ g = (γ : G) * t i * κ) ↔
      ∃ (γ' : Γ') (k : J'), φ (a⁻¹ * g) = ι γ' * y i * k := by
    intro g i
    constructor
    · rintro ⟨γ, κ, hκ, rfl⟩
      obtain ⟨γ', hγ'⟩ := hrat' γ
      refine ⟨γ', ⟨φ κ, hκ⟩, ?_⟩
      rw [hγ', ← hty i]
      simp only [t, map_mul, map_inv, he]
      group
    · rintro ⟨γ', k, h⟩
      have hγ : a * e.symm (ι γ') * a⁻¹ ∈ Γ := by
        rw [hrat]; exact ⟨γ', by simp [he, mul_assoc]⟩
      refine ⟨⟨_, hγ⟩, e.symm k, by simp [he], ?_⟩
      apply hφ.1
      have h2 : φ g = φ a * (ι γ' * y i * k) := by
        rw [← h, map_mul, map_inv]; group
      rw [h2]
      simp only [t, map_mul, map_inv, he]
      group
  choose c hc using hrat'
  refine ⟨Finset.univ.image t, ?_, ?_⟩
  · intro g
    obtain ⟨i, ⟨γ', k, hi⟩, huniq⟩ := hy (φ (a⁻¹ * g))
    refine ⟨t i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key g i).2 ⟨γ', k, hi⟩⟩, ?_⟩
    rintro s ⟨hs, hd⟩
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hs
    rw [huniq i' ((key g i').1 hd)]
  · intro W _ _ F F'
    rw [Finset.sum_image (fun i _ j _ h => tinj h)]
    unfold adInner
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hty i]
    congr 2
    refine congrArg (fun n : ℕ => (n : ℂ)) (Nat.card_congr (Equiv.symm ?_))
    refine
      { toFun := fun γ => ⟨c γ.1, ?_⟩
        invFun := fun γ' => ⟨⟨a * e.symm (ι γ'.1) * a⁻¹, (hrat _).2 ⟨γ'.1, by simp [he, mul_assoc]⟩⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [mem_stab, hc γ.1, ← hty i]
      have := γ.2
      rw [Subgroup.mem_comap] at this
      convert this using 1
      simp only [map_mul, map_inv]; group
    · have := γ'.2
      rw [mem_stab] at this
      rw [Subgroup.mem_comap]
      convert this using 1
      simp only [t, map_mul, map_inv, he]; group
    · intro γ
      apply Subtype.ext; apply Subtype.ext
      apply hφ.1
      simp only [map_mul, map_inv, he]
      rw [hc]
      simp only [map_mul, map_inv]
      group
    · intro γ'
      apply Subtype.ext
      apply hι
      rw [hc]
      simp [he, mul_assoc]

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

theorem adForms_right {G Γ W : Type} [Group G] [Group Γ] {ι : Γ →* G} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ) (g : G) (k : J) : F (g * k) = (χ k : ℂ) • F g := by
  have h0 := hF 1 g k
  simpa using h0

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame Formalism.L2.Theta

theorem ipA_eq {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) (μ : D.what₂.Tup) (i : Fin D.R.m)
    (x y : GA D (Vc D i) → (R.cV i).W) :
    (toLiftReal R F tupT hm hTop hinj).ipA μ i x y = (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ipVia (R.extV i (tupT μ)) x y :=
  rfl

set_option maxHeartbeats 1000000 in

theorem inner_eq {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : Fin D.R.m) :
    ∃ Fx : D.what₂.Mt μ (j.1 + 1) → (Bridge.Gf (Vc D j) → (X.R.cV j).W),
      (∀ x, Fx x ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
        (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ))).J (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ))).χ) ∧
      (∀ x, (X.R.cV j).ext (Fx x) = X.fn hμ j x) ∧
      ∀ x y, inner ℂ x y = (((RealDat.nP X.F false)⁻¹ : ℝ) : ℂ) *
        Bridge.adInner (Bridge.ratF (Vc D j)) (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ))).J
          (X.R.B.L j (X.tupT μ)).pres.y (Fx x) (Fx y) := by
  have hC := X.given.core
  have hHV := hC.models.HV j (X.tupT μ)
  have hex : ∀ x : D.what₂.Mt μ (j.1 + 1), ∃ h, X.R.extV j (X.tupT μ) h = X.fn hμ j x :=
    fun x => (X.IL.jMt μ hμ j x).2.1
  choose hx hhx using hex
  refine ⟨fun x => (X.R.HV j (X.tupT μ)).e (hx x), fun x => ?_, fun x => hhx x, fun x y => ?_⟩
  · have h := LinearMap.mem_range_self (X.R.HV j (X.tupT μ)).e (hx x)
    rw [hHV.2.1] at h
    exact h
  · have hmt := X.recR.tied.lift.mt μ hμ j x y
    rw [hmt]
    refine Eq.trans (ipA_eq X.R X.F X.tupT X.hm X.hTop X.hinj μ j (X.fn hμ j x) (X.fn hμ j y)) ?_
    congr 1
    unfold ipVia
    have h1 : X.fn hμ j x ∈ LinearMap.range (X.R.extV j (X.tupT μ)) := ⟨hx x, hhx x⟩
    have h2 : X.fn hμ j y ∈ LinearMap.range (X.R.extV j (X.tupT μ)) := ⟨hx y, hhx y⟩
    split_ifs with h
    · have e1 : h.1.choose = hx x := X.hinj j _ (h.1.choose_spec.trans (hhx x).symm)
      have e2 : h.2.choose = hx y := X.hinj j _ (h.2.choose_spec.trans (hhx y).symm)
      exact (congrArg₂ (fun a b => inner ℂ a b) e1 e2).trans (hHV.2.2 (hx x) (hx y))
    · exact absurd ⟨h1, h2⟩ h

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

open Formalism.IndefR Formalism.L2.Theta

set_option maxHeartbeats 4000000 in

theorem frame_bij {D : D7} {V : TH.HSp D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) :
    Function.Bijective ((finHom V).rangeRestrict.comp P.ψ) := by
  obtain ⟨hsplit, -, hinter, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  constructor
  · intro x y h
    apply P.inj
    have h1 : finHom V (P.ψ x) = finHom V (P.ψ y) := congrArg Subtype.val h
    have h2 : (P.ψ y)⁻¹ * P.ψ x = 1 := by
      apply hinter
      · show _ ∈ (finHom V).ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      · exact (GfC V).mul_mem ((GfC V).inv_mem (P.into y)) (P.into x)
    exact (inv_mul_eq_one.1 h2).symm
  · intro x
    obtain ⟨g, hg⟩ := x.2
    obtain ⟨a, ha, k, hk, rfl⟩ := hsplit g
    obtain ⟨h, hh⟩ := P.onto k hk
    have ha' : finHom V a = 1 := ha
    refine ⟨h, Subtype.ext ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.coe_rangeRestrict, ← hg, map_mul, ha', one_mul, hh]

theorem ratF_inj {D : D7} (V : TH.HSp D) : Function.Injective (Bridge.ratF V) := by
  rw [injective_iff_map_eq_one]
  intro γ h
  have h1 : finHom V (γ : GA D V) = 1 := congrArg Subtype.val h
  exact Subtype.ext (GlobalTheory.DefFree.AdelCls.rat_inj V γ γ.2
    ((GlobalTheory.DefFree.AdelCls.finU_eq_one_iff V _).2 (MonoidHom.mem_ker.2 h1)))

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.L2.Theta

set_option maxHeartbeats 4000000 in

theorem core (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (hA : GlobalTheory.NJoin.Agree X P.M P.rep) (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k)
    (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) :
    ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) (T : Finset (GAf D.host.E D.R.nV))
      (β : (P.M μ k h1 h2).wt.W →ₗ⋆[ℂ] (P.M μ k h1 h2).wt.W →ₗ[ℂ] ℂ) (c : ℝ),
      GlobalTheory.CoefDuty.IsInvForm (P.M μ k h1 h2).wt β ∧ GlobalTheory.CoefDuty.IsBounded J ∧
      (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧
      GlobalTheory.CoefDuty.IsClassReps J T ∧ 0 < c ∧
      (∀ x, (P.M μ k h1 h2).real x ∈ NG.TypeSp (P.M μ k h1 h2).wt.ρ J χ) ∧
      ∀ x y, inner ℂ x y = (c : ℂ) * GlobalTheory.CoefDuty.classSum (P.M μ k h1 h2).wt β J T
        ((P.M μ k h1 h2).real x) ((P.M μ k h1 h2).real y) := by
  subst hk
  obtain ⟨Fx, hmem, hext, hin⟩ := inner_eq X μ hμ j
  obtain ⟨N, hN, hopen⟩ := GlobalTheory.T.exists_principalCongruence_in_definiteLevel D P.cf P.C P.tp X P.M P.rep hA j (X.tupT μ)
  obtain ⟨Fb, hFb⟩ := GlobalTheory.T.definiteLevel_preimage_finitely_many_cosets D P.cf P.C P.tp X P.M P.rep hA j (X.tupT μ)
  have hcV := X.given.core.models.cV j
  have hφ := frame_bij (hA.PV j)
  set φ := (finHom (Vc D j)).rangeRestrict.comp (hA.PV j).ψ with hφdef
  set EV := levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ)) with hEV
  set eW := hA.eW μ hμ j with heW
  have hrat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
      ∃ γ, Bridge.ratF (Vc D j) γ = φ ((hA.a j)⁻¹ * h * hA.a j) := by
    intro h
    rw [hA.rat j h]
    constructor
    · rintro ⟨γ, hγ, e⟩
      exact ⟨⟨γ, hγ⟩, Subtype.ext e⟩
    · rintro ⟨γ, e⟩
      exact ⟨γ.1, γ.2, congrArg Subtype.val e⟩
  obtain ⟨T, hT, hsum⟩ := transport (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (Bridge.ratF (Vc D j)) (ratF_inj _) φ hφ
    (hA.a j) hrat EV.J (X.R.B.L j (X.tupT μ)).pres.y (X.R.B.L j (X.tupT μ)).pres.reps
  have hreal : ∀ x h, (P.M μ (j.1 + 1) h1 h2).real x h = eW (Fx x (φ ((hA.a j)⁻¹ * h))) := by
    intro x h
    rw [hA.real μ hμ j x h, ← hext x]
    have hin' : ((hA.PV j).ψ ((hA.a j)⁻¹ * h))⁻¹ ∈ GfC (Vc D j) := (GfC _).inv_mem ((hA.PV j).into _)
    show eW ((X.R.cV j).ρ ((hA.PV j).ψ ((hA.a j)⁻¹ * h))⁻¹ _) = _
    rw [hcV.1 _ hin']
    rfl
  let β : (P.M μ (j.1 + 1) h1 h2).wt.W →ₗ⋆[ℂ] (P.M μ (j.1 + 1) h1 h2).wt.W →ₗ[ℂ] ℂ :=
    ((innerₛₗ ℂ).comp eW.symm.toLinearMap).compl₂ eW.symm.toLinearMap
  have hβ : ∀ u v, β u v = inner ℂ (eW.symm u) (eW.symm v) := fun u v => rfl
  refine ⟨EV.J.comap φ, EV.χ.comp (φ.subgroupComap EV.J), T, β, (RealDat.nP X.F false)⁻¹, ⟨?_, ?_, ?_⟩, ?_, ?_, hT, ?_, ?_, ?_⟩
  · intro u v
    rw [hβ, hβ, inner_conj_symm]
  · intro u hu
    rw [hβ]
    exact (re_inner_self_pos (𝕜 := ℂ)).2 ((LinearEquiv.map_ne_zero_iff eW.symm).2 hu)
  · intro γ u v
    obtain ⟨γ', e⟩ := (hrat γ).1 γ.2
    have hw := hA.wt μ hμ j γ γ'.1 γ'.2 (congrArg Subtype.val e)
    have hs : ∀ w, eW.symm ((P.M μ (j.1 + 1) h1 h2).wt.ρ γ w) = (X.R.cV j).ρ γ'.1 (eW.symm w) := by
      intro w
      rw [LinearEquiv.symm_apply_eq, hw, LinearEquiv.apply_symm_apply]
    rw [hβ, hβ, hs, hs, hcV.2.1]
  · exact ⟨Fb, fun κ hκ => hFb κ hκ⟩
  · exact ⟨N, hN, fun κ hκ => hopen κ hκ⟩
  · unfold RealDat.nP
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  · intro x
    have hr : (P.M μ (j.1 + 1) h1 h2).real x ∈ NG.TypeSp (P.M μ (j.1 + 1) h1 h2).wt.ρ
        (P.M μ (j.1 + 1) h1 h2).J (P.M μ (j.1 + 1) h1 h2).χ := by
      rw [← (P.M μ (j.1 + 1) h1 h2).real_range]; exact LinearMap.mem_range_self _ _
    refine ⟨hr.1, fun κ => ?_⟩
    funext h
    show (P.M μ (j.1 + 1) h1 h2).real x (h * κ) = _
    rw [Pi.smul_apply, hreal, hreal, ← mul_assoc, map_mul]
    have hm := adForms_right (hmem x) (φ ((hA.a j)⁻¹ * h)) ⟨φ κ, κ.2⟩
    rw [hm]
    exact (eW.map_smul _ _).trans rfl
  · intro x y
    rw [hin x y, hsum (Fx x) (Fx y)]
    unfold GlobalTheory.CoefDuty.classSum
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hreal, hreal]
    simp only [hβ, LinearEquiv.symm_apply_apply]

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp),
    GlobalTheory.NJoin.Agree X P.M P.rep → ∀ i, ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ)
      (T : Finset (GAf D.host.E D.R.nV)) (β : (P.M.loc i).wt.W →ₗ⋆[ℂ] (P.M.loc i).wt.W →ₗ[ℂ] ℂ) (c : ℝ),
      GlobalTheory.CoefDuty.IsInvForm (P.M.loc i).wt β ∧ GlobalTheory.CoefDuty.IsBounded J ∧
      (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧
      GlobalTheory.CoefDuty.IsClassReps J T ∧ 0 < c ∧ (∀ x, (P.M.loc i).real x ∈ NG.TypeSp (P.M.loc i).wt.ρ J χ) ∧
      ∀ x y, inner ℂ x y = (c : ℂ) * GlobalTheory.CoefDuty.classSum (P.M.loc i).wt β J T ((P.M.loc i).real x)
        ((P.M.loc i).real y) := by
  intro hL D P X hA i
  have hμ : Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hr := D.nd.j_range i
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i := ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  exact core hL D P X hA _ hμ j _ hj hr.1 hr.2

end GlobalTheory.VFormCls

end
end
