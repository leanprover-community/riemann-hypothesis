import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdentityCellAdmissibleOfNormalisation
import Formalism.FlagUnipotentLattices.AutBoundOfMinkowskiBound
import Formalism.FlagUnipotentLattices.LiftFixesBaseVector
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ParabolicSumAdmissibleOfParabolic
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.HypothesesNumericalConsequences
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
import Formalism.FlagUnipotentLattices.IdealCountLeWAsm
import Formalism.FlagUnipotentLattices.IotaCountFullAsm
import Formalism.FlagUnipotentLattices.GramSubmersionSplit

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def nfH (S : HSpace E) : Formalism.HermitianLatticeCounting.S6.HermSpace E S.V where
  B := S.hT.flip
  herm x y := (a_herm y x).symm
  nondeg x h := S.nondeg.2 x h

def nfF (F : FlagG S r T) (hT : T ≠ 0) : Formalism.HermitianLatticeCounting.S6.FlagD (nfH S) r where
  e := F.fvec
  T := T
  indep := by
    have h : (fun a : Fin r => F.fvec a.castSucc) = F.e := funext (geo_fvec_cast F)
    rw [h]; exact F.e_indep
  iso a b := by rw [geo_fvec_cast, geo_fvec_cast]; exact F.e_iso b a
  zperp a := by rw [geo_fvec_cast, geo_fvec_last]; exact p_symm_zero S (F.z_orth a)
  zz := by rw [geo_fvec_last]; exact F.z_norm
  hT := hT

theorem nf_mem_perp {U : Submodule E S.V} {y : S.V} : y ∈ perpS S U ↔ ∀ x ∈ U, S.hT x y = 0 := Iff.rfl

theorem nf_Xa (F : FlagG S r T) (hT : T ≠ 0) (a : ℕ) : (nfF F hT).Xa a = F.Xa a := by
  have h : (fun b : Fin r => F.fvec b.castSucc) = F.e := funext (geo_fvec_cast F)
  show Submodule.span E ((fun b : Fin r => F.fvec b.castSucc) '' {b | b.val < a}) = _
  rw [h]; rfl

theorem nf_X_eq (F : FlagG S r T) : F.X = F.Xa r := by
  unfold FlagG.X FlagG.Xa
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩

theorem nf_X (F : FlagG S r T) (hT : T ≠ 0) : (nfF F hT).X = F.X := by
  show (nfF F hT).Xa r = _
  rw [nf_Xa, nf_X_eq]

theorem normal_form_z_eq (F : FlagG S r T) (hT : T ≠ 0) : (nfF F hT).z = F.z := geo_fvec_last F

theorem nf_II (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) :
    Formalism.HermitianLatticeCounting.S6.II (nfF F hT) (nfF F' hT') = Isp F F' := by
  show (nfF F hT).X ⊓ (nfF F' hT').X = _
  rw [nf_X, nf_X]; rfl

theorem normal_form_V0_eq (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) :
    Formalism.HermitianLatticeCounting.S6.V0 (nfF F hT) (nfF F' hT') = F.Xplus ⊔ F'.Xplus := by
  show (nfF F hT).X ⊔ (nfF F' hT').X ⊔ Submodule.span E {(nfF F hT).z, (nfF F' hT').z} = _
  rw [nf_X, nf_X, normal_form_z_eq, normal_form_z_eq, Submodule.span_insert]
  unfold FlagG.Xplus
  exact sup_sup_sup_comm _ _ _ _

theorem nf_Dl (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) (l : ℕ) (hl : l ≤ r + 1) :
    Dl F F' l = star (Formalism.HermitianLatticeCounting.S6.Dl (nfF F hT) (nfF F' hT') l hl) := by
  rw [tie_Dl_eq' F F' l hl]
  unfold Formalism.HermitianLatticeCounting.S6.Dl
  rw [← starRingEnd_apply, RingHom.map_det]
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Formalism.HermitianLatticeCounting.S6.Zhat, Matrix.of_apply, Zhat,
    brS, starRingEnd_apply]
  exact a_herm _ _

theorem nf_G (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) :
    Formalism.HermitianLatticeCounting.S6.Gval (nfF F hT) (nfF F' hT') = Gflag F F' := by
  unfold Formalism.HermitianLatticeCounting.S6.Gval Gflag
  rw [nf_Dl F F' hT hT' (r + 1) le_rfl, nf_Dl F F' hT hT' r (Nat.le_succ r), star_star, star_star]
  show _ - T * T' * _ = _
  ring

theorem nf_LieN (F : FlagG S r T) (hT : T ≠ 0) (Y : S.V →ₗ[E] S.V) (h : (nfF F hT).LieN Y) : Y ∈ F.LieN := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun x y => ?_, fun a _ _ => ?_, fun x hx => ?_⟩
  · have h := h1 y x
    rw [add_comm]; exact h
  · have hle : F.Xa a ≤ (F.Xa (a - 1)).comap Y := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      have h := h2 i
      rw [nf_Xa] at h
      have h' : Y (F.e i) ∈ F.Xa i.val := by rw [← geo_fvec_cast]; exact h
      have hi' : i.val < a := hi
      exact geo_Xa_mono F (by omega) h'
    exact fun x hx => hle hx
  · have h := h3 x (fun a => p_symm_zero S (hx (F.fvec a.castSucc)
      (by rw [geo_fvec_cast]; exact Submodule.subset_span ⟨a, rfl⟩)))
    rw [nf_X] at h; exact h

theorem nf_ell (F : FlagG S r T) (hT : T ≠ 0) (Y : S.V →ₗ[E] S.V) (s : E) (h : (nfF F hT).DPsi Y s) : F.ell Y = s := by
  obtain ⟨c, hc, h⟩ := h
  rw [← hc]
  unfold FlagG.ell
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h1 := h a
  rw [nf_Xa] at h1
  have h2 : Y (F.fvec a.succ) = c a • F.e a + (Y (F.fvec a.succ) - c a • F.e a) := by abel
  rw [h2]
  refine geo_coefX F a (c a) _ ?_
  rw [← geo_fvec_cast]; exact h1

theorem nf_rel (K : Type) [Field K] [Algebra K E] (htr : ∀ x : E, algebraMap K E (Algebra.trace K E x) = x + star x)
    (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) (h : Relevant K F F') :
    Formalism.HermitianLatticeCounting.S6.Relevant (nfF F hT) (nfF F' hT') := by
  intro Y hY hY' s s' hs hs'
  have h0 := h Y ⟨nf_LieN F hT Y hY, nf_LieN F' hT' Y hY'⟩
  unfold FlagG.dpsi at h0
  rw [nf_ell F hT Y s hs, nf_ell F' hT' Y s' hs'] at h0
  rw [← htr, ← htr, h0]

theorem nf_pos (F : LFlag S r T) (hT : T ≠ 0) (hP : PosX F) (σ : E →+* ℂ) : (nfF F.fl hT).PosDefAt σ := by
  intro w hw hX
  rw [nf_X] at hX
  refine hP σ w ?_ hX
  rw [← a_span_frame]
  exact a_orth_of_frame _ _ (fun i => p_symm_zero S (hw i))

theorem nf_level (F : FlagG S r T) (hT : T ≠ 0) (x : S.V) (a : Fin r) (al : E) (h : (nfF F hT).HasLevel x a al) :
    F.level x = a.val + 1 := by
  obtain ⟨hal, hx⟩ := h
  rw [nf_Xa] at hx
  have hx' : x - al • F.e a ∈ F.Xa a.val := by rw [← geo_fvec_cast]; exact hx
  have hmem : x ∈ F.Xa (a.val + 1) := by
    have h : x = (x - al • F.e a) + al • F.e a := by abel
    rw [h]
    exact Submodule.add_mem _ (geo_Xa_mono F (Nat.le_succ _) hx')
      (Submodule.smul_mem _ _ (geo_e_mem_Xa F a _ (Nat.lt_succ_self _)))
  have hnot : ∀ n ∈ {n | x ∈ F.Xa n}, a.val + 1 ≤ n := by
    intro n hn
    by_contra hlt
    have hn' : x ∈ F.Xa a.val := geo_Xa_mono F (by omega) hn
    have h1 : al • F.e a ∈ F.Xa a.val := by
      have h : al • F.e a = x - (x - al • F.e a) := by abel
      rw [h]; exact Submodule.sub_mem _ hn' hx'
    have h2 : F.e a ∈ F.Xa a.val := by
      have h := Submodule.smul_mem _ al⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hal, one_smul] at h
    exact F.e_indep.notMem_span_image (s := {i | i.1 < a.val}) (by simp) h2
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ hnot)

theorem nf_levels (F : FlagG S r T) (hT : T ≠ 0) (I : Submodule E S.V) (j : ℕ)
    (h1 : ∀ x ∈ I, x ≠ 0 → ∃ (a : Fin r) (al : E), (nfF F hT).HasLevel x a al ∧ j ≤ a.val)
    (h2 : ∀ a : Fin r, j ≤ a.val → ∃ x ∈ I, ∃ al : E, (nfF F hT).HasLevel x a al) (a : ℕ) :
    (∃ x ∈ I, x ≠ 0 ∧ F.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ r) := by
  constructor
  · rintro ⟨x, hx, hx0, rfl⟩
    obtain ⟨b, al, hl, hjb⟩ := h1 x hx hx0
    rw [nf_level F hT x b al hl]
    exact ⟨by omega, b.2⟩
  · rintro ⟨h1a, h2a⟩
    obtain ⟨x, hx, al, hl⟩ := h2 ⟨a - 1, by omega⟩ (by show j ≤ a - 1; omega)
    have hlev := nf_level F hT x _ al hl
    have hlev' : F.level x = a := by rw [hlev]; show a - 1 + 1 = a; omega
    refine ⟨x, hx, ?_, hlev'⟩
    rintro rfl
    have h0 : F.level 0 = 0 := Nat.sInf_eq_zero.2 (Or.inl (by show (0 : S.V) ∈ F.Xa 0; exact Submodule.zero_mem _))
    omega

theorem nf_fvec_mem (F : FlagG S r T) (a : Fin (r + 1)) : F.fvec a ∈ F.Xplus := by
  have h := a_span_frame (⟨F, F.z⟩ : LFlag S r T)
  have h' : F.fvec a ∈ Submodule.span E (Set.range (frame (⟨F, F.z⟩ : LFlag S r T))) := Submodule.subset_span ⟨a, rfl⟩
  rw [h] at h'; exact h'

theorem nf_perp (F : FlagG S r T) (U I : Submodule E S.V) (hU : F.Xplus ≤ U) (hIX : I ≤ F.X)
    (hk : ∀ x ∈ F.X, (∀ w ∈ U, S.hT x w = 0) ↔ x ∈ I)
    (hs : ∀ w : S.V, (∀ a, S.hT w (F.fvec a) = 0) → ∃ x ∈ F.X, ∀ v ∈ U, S.hT (w - x) v = 0) :
    perpS S U ⊓ F.X = I ∧ perpS S U ⊔ F.X = F.XplusPerp := by
  constructor
  · ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact (hk x h2).1 (fun w hw => p_symm_zero S (h1 w hw))
    · intro hx
      exact ⟨fun w hw => p_symm_zero S ((hk x (hIX hx)).2 hx w hw), hIX hx⟩
  · apply le_antisymm
    · refine sup_le (fun y hy x hx => hy x (hU hx)) ?_
      intro y hy x hx
      exact p_mem_orth.1 (a_X_le_orth_Xplus (⟨F, F.z⟩ : LFlag S r T) hy) x hx
    · intro w hw
      obtain ⟨x, hx, h⟩ := hs w (fun a => p_symm_zero S (hw _ (nf_fvec_mem F a)))
      have h' : w = (w - x) + x := by abel
      rw [h']
      exact Submodule.add_mem_sup (nf_mem_perp.2 (fun v hv => p_symm_zero S (h v hv))) hx

theorem nf_gen (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (hT' : T' ≠ 0) (j : ℕ) (hj : j ≤ r) (c : E)
    (h : Formalism.HermitianLatticeCounting.S6.NFFull (nfF F hT) (nfF F' hT') j hj c) :
    (∀ a : ℕ, (∃ x ∈ Isp F F', x ≠ 0 ∧ F.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ r)) ∧
    (∀ a : ℕ, (∃ x ∈ Isp F F', x ≠ 0 ∧ F'.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ r)) ∧
    (F'.z - c • F.z ∈ F.X ⊔ F'.X ∧ c * star c * T = T') ∧
    Dl F F' j ≠ 0 ∧
    (perpS S (F.Xplus ⊔ F'.Xplus) ⊓ F.X = Isp F F' ∧ perpS S (F.Xplus ⊔ F'.Xplus) ⊔ F.X = F.XplusPerp) ∧
    (perpS S (F.Xplus ⊔ F'.Xplus) ⊓ F'.X = Isp F F' ∧ perpS S (F.Xplus ⊔ F'.Xplus) ⊔ F'.X = F'.XplusPerp) := by
  obtain ⟨⟨-, -, hlev, hall, -, -, -, -, hz⟩, hcc, hD, -, -, hk, hk', hs, hs'⟩ := h
  rw [nf_II] at hlev hall
  rw [nf_X, nf_X, normal_form_z_eq, normal_form_z_eq] at hz
  simp only [normal_form_V0_eq, nf_II, nf_X] at hk hk' hs hs'
  refine ⟨nf_levels F hT _ j ?_ ?_, nf_levels F' hT' _ j ?_ ?_, ⟨hz, hcc⟩, ?_,
    nf_perp F _ _ le_sup_left inf_le_left hk hs, nf_perp F' _ _ le_sup_right inf_le_right hk' hs'⟩
  · intro x hx hx0
    obtain ⟨a, al, al', h1, -, h3, -⟩ := hlev x hx hx0
    exact ⟨a, al, h1, h3⟩
  · intro a ha
    obtain ⟨x, hx, al, al', h1, -⟩ := hall a ha
    exact ⟨x, hx, al, h1⟩
  · intro x hx hx0
    obtain ⟨a, al, al', -, h2, h3, -⟩ := hlev x hx hx0
    exact ⟨a, al', h2, h3⟩
  · intro a ha
    obtain ⟨x, hx, al, al', -, h2⟩ := hall a ha
    exact ⟨x, hx, al', h2⟩
  · rw [nf_Dl F F' hT hT' j (hj.trans (Nat.le_succ r))]
    exact star_ne_zero.2 hD

theorem nf_Xplus_eq (F : FlagG S r T) (F' : FlagG S r T') (hX : F'.X = F.X) (c : E) (hc : c ≠ 0)
    (hz : F'.z - c • F.z ∈ F.X) : F'.Xplus = F.Xplus := by
  unfold FlagG.Xplus
  rw [hX]
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_le.2 ?_)
    rintro _ rfl
    have h : F'.z = (F'.z - c • F.z) + c • F.z := by abel
    show F'.z ∈ _
    rw [h]
    exact Submodule.add_mem_sup hz (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · refine sup_le le_sup_left (Submodule.span_le.2 ?_)
    rintro _ rfl
    have h : F.z = (-c⁻¹) • (F'.z - c • F.z) + c⁻¹ • F'.z := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hc, neg_smul, neg_smul, one_smul]; abel
    show F.z ∈ _
    rw [h]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ hz) (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

end Gen

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : TermTie D)

theorem nf_T_ne (D : D7) (u : D.what₂.Word) : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (tie_Tu_pos D u).ne'




end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.HermitianLatticeCounting.S6

section Cov

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}











end Cov

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

section Schur

variable {G : Type} [Group G] (Sg : Subgroup G)
variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]



end Schur

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar


variable {D : D7} (X : TermTie D)




end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : TermTie D)



end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]


end HS

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : TermTie D)

def Ineq2a (D : D7) {u u' : D.what₂.Word} (Φ : Set (D.s.Term u u')) (c : ℝ) : Prop :=
  Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) →
    hsNormSq (KOf D.s u u' Φ) ≤ c * (∑' p : pairsIn D.s Φ, D.s.pval p.1).re


end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : TermTie D)



def ATie (X : TermTie D) : Prop := ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), X.Jt t = 0 → D.s.aTerm u u' t = 0



variable (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)






end Rec

section Fam

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))



end Fam

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : TermTie D)

def PFHost (D : D7) : Prop :=
  ∀ (l : ℕ) (x : D.host.E),
    ((Nloc (ddS D) D.R.rS l x : ℚ) : ℝ) = ∏ τ : D.what₂.Tau, absReal D.host.rdE (embS D τ) D.R.rS l x ^ 2



theorem two_pow_le_height_bound (b CH C : ℝ) (r m f : ℕ) (hb : 2 ≤ b) (hm : 2 * r + 2 = m) (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C) :
    (2 * b ^ (CH * (m : ℝ))) ^ (4 * r * f) ≤ Hb b C m f := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have e1 : 2 * b ^ (CH * (m : ℝ)) ≤ b ^ (CH * (m : ℝ) + 1) := by
    rw [Real.rpow_add_one hb0.ne']
    have hp := Real.rpow_pos_of_pos hb0 (CH * (m : ℝ))
    nlinarith
  have e2 : (2 * b ^ (CH * (m : ℝ))) ^ (4 * r * f) ≤ (b ^ (CH * (m : ℝ) + 1)) ^ (4 * r * f) :=
    pow_le_pow_left₀ (by positivity) e1 _
  have e3 : (b ^ (CH * (m : ℝ) + 1)) ^ (4 * r * f) = b ^ ((CH * (m : ℝ) + 1) * ((4 * r * f : ℕ) : ℝ)) :=
    (Real.rpow_mul_natCast hb0.le _ _).symm
  refine e2.trans (e3.le.trans ?_)
  unfold Hb
  refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
  have hmr : (m : ℝ) = 2 * (r : ℝ) + 2 := by rw [← hm]; push_cast; ring
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg _
  push_cast
  have h1 : CH * (m : ℝ) + 1 ≤ (CH + 1) * (m : ℝ) := by nlinarith
  have h2 : 4 * (r : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  calc (CH * (m : ℝ) + 1) * (4 * (r : ℝ) * f) ≤ ((CH + 1) * (m : ℝ)) * (2 * (m : ℝ) * f) := by
        apply mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hf0) (by positivity) (by positivity)
    _ = 2 * (CH + 1) * (m : ℝ) ^ 2 * f := by ring
    _ ≤ C * (m : ℝ) ^ 2 * f := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) hf0


def AmplitudeBoundWithoutNorms (large₂ : SizeData₂ D) (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (CH Cs C : ℝ) : Prop :=
  ∀ u : D.what₂.Word, LatticeIndexAndWeightTheory.TieOK X u → ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t →
    Real.sqrt (hsNormSq (X.Jt t)) ≤ Real.sqrt (Module.finrank ℂ (X.Hpi u) : ℝ) *
      (om u t * (C / D.R.k) ^ ((LatticeIndexAndWeightTheory.jOf X t : ℝ) * ((D.R.k : ℝ) - 1 - LatticeIndexAndWeightTheory.jOf X t) * D.R.f) *
        LatticeIndexAndWeightTheory.DelJ X t ^ (-(((D.R.k : ℝ) - 1 - LatticeIndexAndWeightTheory.jOf X t) / 2)) *
        Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        ∏ τ, LatticeIndexAndWeightTheory.sg X t (large₂.sc.b ^ (CH * (D.R.m : ℝ))) τ ^ (-(Cs * D.R.k)))


end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma
open scoped nonZeroDivisors NumberField

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def pfEmb : D.what₂.Tau ⊕ D.what₂.Tau → (D.host.E →+* ℂ)
  | Sum.inl τ => embS D τ
  | Sum.inr τ => (starRingEnd ℂ).comp (embS D τ)

theorem pf_conj_conj (φ : D.host.E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp φ) = φ := by
  ext x; simp

theorem pf_mem (τ : D.what₂.Tau) : embS D τ ∈ D.host.cmType :=
  ((factEmb D.R D.host).2 _).2 (D.eTau τ).2

theorem pf_inj {τ τ' : D.what₂.Tau} (h : embS D τ = embS D τ') : τ = τ' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem pf_bij : Function.Bijective (pfEmb D) := by
  have P1 := D.host.der.cmType.1
  have hsur : ∀ φ ∈ D.host.cmType, ∃ τ, embS D τ = φ := by
    intro φ hφ
    obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 φ
    have hg := ((factEmb D.R D.host).2 g).1 hφ
    refine ⟨D.eTau.symm ⟨g, hg⟩, ?_⟩
    unfold embS
    rw [Equiv.apply_symm_apply]
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg Sum.inl (pf_inj D h)
    · have h' : embS D τ = (starRingEnd ℂ).comp (embS D τ') := h
      exact absurd (h' ▸ pf_mem D τ) ((P1 _).1 (pf_mem D τ'))
    · have h' : (starRingEnd ℂ).comp (embS D τ) = embS D τ' := h
      exact absurd (h'.symm ▸ pf_mem D τ') ((P1 _).1 (pf_mem D τ))
    · have h' : embS D τ = embS D τ' := by
        have := congrArg (fun φ => (starRingEnd ℂ).comp φ) h
        simpa only [pfEmb, pf_conj_conj] using this
      exact congrArg Sum.inr (pf_inj D h')
  · intro φ
    by_cases hφ : φ ∈ D.host.cmType
    · obtain ⟨τ, rfl⟩ := hsur φ hφ
      exact ⟨Sum.inl τ, rfl⟩
    · have h2 : (starRingEnd ℂ).comp φ ∈ D.host.cmType := by
        rw [P1, pf_conj_conj]; exact hφ
      obtain ⟨τ, hτ⟩ := hsur _ h2
      refine ⟨Sum.inr τ, ?_⟩
      show (starRingEnd ℂ).comp (embS D τ) = φ
      rw [hτ, pf_conj_conj]

theorem pf_norm (x : D.host.E) : ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ∏ τ : D.what₂.Tau, ‖embS D τ x‖ ^ 2 := by
  rw [Formalism.MainNotions.LatticeGluingRadicals.j_norm_prod, ← (pf_bij D).prod_comp (fun φ : D.host.E →+* ℂ => ‖φ x‖), Fintype.prod_sum_type,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  have h : ‖pfEmb D (Sum.inr τ) x‖ = ‖embS D τ x‖ := by
    show ‖(starRingEnd ℂ) (embS D τ x)‖ = _
    exact RCLike.norm_conj _
  rw [h, sq]
  rfl

theorem pf_rd_pos : 0 < D.host.rdE := by
  unfold Host.rdE
  have h : (NumberField.discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
  positivity

theorem PFHost_of_discr (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) : PFHost D := by
  intro l x
  have hdd : ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = (D.host.rdE ^ D.R.f) ^ 2 := szf_normDD D hd
  have hrd := pf_rd_pos D
  unfold Nloc absReal
  rw [map_mul, map_zpow₀, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, Rat.cast_zpow, hdd, pf_norm]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, D.what₂.card_Tau]
  congr 1
  have e1 : (D.host.rdE ^ D.R.f) ^ 2 = D.host.rdE ^ ((2 * D.R.f : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, ← pow_mul, mul_comm]
  have e2 : ((D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ)))) ^ 2) ^ D.R.f =
      D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ)) * ((2 * D.R.f : ℕ) : ℝ)) := by
    rw [← pow_mul, Real.rpow_mul_natCast hrd.le]
  rw [e1, e2, ← Real.rpow_intCast, ← Real.rpow_mul hrd.le]
  congr 1
  push_cast
  ring

theorem PFHost_of_data {C0 : ℝ} (h : StandingNumericalData D C0) : PFHost D := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := h
  exact PFHost_of_discr D d13

variable {D} (X : TermTie D)



end Rec

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

open NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar










def chk_SCone (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (A : ℝ) : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
    ∀ reps : Finset (Submodule (𝓞 D.host.E) (D.sp.X 0).V),
      Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ (lf D F0)) reps → ∀ de : ℕ, 1 ≤ de →
      (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ *
          (cntPrim (D.sp.X 0).hT L' (D.R.k - 1) de : ℝ≥0∞)) ≤
        (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹) *
          ENNReal.ofReal (A ^ (1 * D.R.k * D.R.f) * Hb large₂.sc.b A D.R.m D.R.f ^ A *
            ((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (A * (1 : ℕ) + A * Real.log D.R.f))

def chk_MassSum (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
    ∀ reps : Finset (Submodule (𝓞 D.host.E) (D.sp.X 0).V),
      Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ (lf D F0)) reps →
      Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) =
        ∑ L' ∈ reps, ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℕ) : ℝ)⁻¹






end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

open NumberField

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}






end Gen


end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar



end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

theorem mk_core : Formalism.HermitianLatticeCounting.S6.MinkowskiBound := card_dvd_minkowskiNumber




end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

open NumberField

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def t3Q (F : LFlag S r T) (F' : LFlag S r T') : Submodule E S.V := orth S (Xsp F ⊔ Xsp F')

def t3L (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  Lsub Λ F ⊓ toO S (t3Q F F')

def t3L' (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  Lsub Λ F' ⊓ toO S (t3Q F F')

def lamOneLattice (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  (Λ ⊓ toO S (t3Q F F')) ⊔ toO S (Isp F.fl F'.fl)


variable (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T')
  (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z)

include hΛ hz hz'







end Gen

section Emb

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def t3BN (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  Λ ⊓ toO S (Xsp F ⊔ Xsp F')

def t3BD (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  XLam Λ F ⊔ XLam Λ F'




end Emb

section Fin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}







end Fin

section Rec

variable {D : D7} (X : TermTie D)

def DiscriminantBound {u : D.what₂.Word} (t : D.s.Term u u) : Prop :=
  (idx (hS D) (t3L (X.abelian₂ t) (X.fl t) (X.fl' t)) (lamOneLattice (X.abelian₂ t) (X.fl t) (X.fl' t)) : ℝ) *
      (idx (hS D) (t3BN (X.abelian₂ t) (X.fl t) (X.fl' t)) (t3BD (X.abelian₂ t) (X.fl t) (X.fl' t)) : ℝ) ≤
    LatticeIndexAndWeightTheory.DelJ X t / (LatticeIndexAndWeightTheory.b1T X t : ℝ) ^ 2



end Rec

section Halves

variable {D : D7} (X : TermTie D)

def pairingDiscriminantIndex {u : D.what₂.Word} (t : D.s.Term u u) : ℕ :=
  idx (hS D) (Formalism.HermitianLatticesTheory.dual (hS D).hT (XLam (X.abelian₂ t) (X.fl t)) ⊓ toO (hS D) (Xsp (X.fl' t)))
    (XLam (X.abelian₂ t) (X.fl' t) ⊔ toO (hS D) (LatticeIndexAndWeightTheory.Iof X t))

def DiscriminantIndexHalf {u : D.what₂.Word} (t : D.s.Term u u) : Prop :=
  idx (hS D) (t3L (X.abelian₂ t) (X.fl t) (X.fl' t)) (lamOneLattice (X.abelian₂ t) (X.fl t) (X.fl' t)) *
      idx (hS D) (t3BN (X.abelian₂ t) (X.fl t) (X.fl' t)) (t3BD (X.abelian₂ t) (X.fl t) (X.fl' t)) ≤ pairingDiscriminantIndex X t

def DiscriminantIndexSecondHalf {u : D.what₂.Word} (t : D.s.Term u u) : Prop :=
  (pairingDiscriminantIndex X t : ℝ) ≤ LatticeIndexAndWeightTheory.DelJ X t / (LatticeIndexAndWeightTheory.b1T X t : ℝ) ^ 2


end Halves

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

open NumberField

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Det

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}



end Det

section RecDet

variable {D : D7} (X : TermTie D)

def b1T' {u : D.what₂.Word} (t : D.s.Term u u) : ℕ :=
  idx (hS D) (XLam (X.abelian₂ t) (X.fl' t))
    ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl' t) (LatticeIndexAndWeightTheory.jOf X t))) ⊔ (X.abelian₂ t ⊓ toO (hS D) (LatticeIndexAndWeightTheory.Iof X t)))

def FrameDeterminantBound {u : D.what₂.Word} (t : D.s.Term u u) : Prop :=
  latDet (hS D) ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl t) (LatticeIndexAndWeightTheory.jOf X t))) ⊔
    (X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl' t) (LatticeIndexAndWeightTheory.jOf X t)))) ≤ LatticeIndexAndWeightTheory.DelJ X t

def BOneComparison {u : D.what₂.Word} (t : D.s.Term u u) : Prop := LatticeIndexAndWeightTheory.b1T X t ≤ b1T' X t



end RecDet

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Same

variable (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)





end Same

section Sizes

variable (D : D7) (large₂ : SizeData₂ D)

theorem log_scale_eq_L : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _

theorem one_lt_scale_L : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos

theorem two_le_scale_b : 2 ≤ large₂.sc.b := by
  have h1 := one_lt_scale_L D large₂
  have h2 : large₂.sc.L + 1 ≤ Real.exp large₂.sc.L := Real.add_one_le_exp _
  show 2 ≤ Real.exp large₂.sc.L
  linarith

theorem two_rank_add_two_eq_m : 2 * D.R.rS + 2 = D.R.m := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  simp only [Ranks.rS]; omega

theorem one_le_degree_f : 1 ≤ D.R.f := by
  have : 1 ≤ D.R.ord := D.R.ord_pos
  simp only [Ranks.f, Ranks.n]; omega


end Sizes

section Close

def k2C0 (C : ℝ) : ℝ := if h : 1 ≤ C then (Formalism.HermitianLatticeCounting.Final.S6.finalSum C h).choose else 0

def k2A (D : D7) (large₂ : SizeData₂ D) (C : ℝ) (j : ℕ) : ℝ :=
  Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L) * (C / D.R.k) ^ (j * (D.R.k - 1 - j) * D.R.f)

def k2B (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : ℝ := (∑ j ∈ Finset.Icc 1 D.R.rS, k2A D large₂ C j) ^ 2

theorem final_bound_closes (D : D7) (large₂ : SizeData₂ D) (C : ℝ) (hC : 1 ≤ C) (d : ℝ) (hd : 0 ≤ d)
    (hk : k2C0 C * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k) :
    2 * d * k2B D large₂ C ≤ d * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k)) := by
  have h := (Formalism.HermitianLatticeCounting.Final.S6.finalSum C hC).choose_spec.2 D.R.k D.R.rS D.R.f large₂.sc.b d (two_le_scale_b D large₂)
    (one_le_degree_f D) hd
  rw [two_rank_add_two_eq_m D, log_scale_eq_L D large₂] at h
  unfold k2C0 at hk
  rw [dif_pos hC] at hk
  exact h hk

end Close

section Main

variable {D : D7} {large₂ : SizeData₂ D} (X : TermTie D)

def RowPairWeightBound (u : D.what₂.Word) (Q : D.s.Pair u u → Prop) (M B : ℝ) : Prop :=
  ∀ S : Finset (D.s.Pair u u), (∀ p ∈ S, Q p) → ∑ p ∈ S, wP X p ≤ M * dimPi (hc := D.hcW) u * B

def k2Q (D : D7) (u : D.what₂.Word) (Φ : Set (D.s.Term u u)) (p : D.s.Pair u u) : Prop := p ∈ pairsIn D.s Φ

def PairBoundOnFamily (D : D7) (u : D.what₂.Word) (Φ : Set (D.s.Term u u)) : Prop :=
  Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) ∧
    (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f * gaG D * (∑' p : pairsIn D.s Φ, D.s.pval p.1).re ≤
      (D.duS u : ℝ) * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))


def k2G0 (D : D7) (u : D.what₂.Word) : Set (D.s.Term u u) := {t | LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t}






def IrrelevantAmplitudeZero (u : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u, D.s.Gterm t = 0 → ¬ D.s.relevant t → X.Jt t = 0

def k2QJ (u : D.what₂.Word) (j' j'' : ℕ) (p : D.s.Pair u u) : Prop :=
  LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.pfst p) ∧ LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.psnd p) ∧ LatticeIndexAndWeightTheory.jOf X (D.s.pfst p) = j' ∧ LatticeIndexAndWeightTheory.jOf X (D.s.psnd p) = j''


open Classical in

theorem row_bound_of_rank_bounds (u : D.what₂.Word) (Φ : Set (D.s.Term u u)) {M : ℝ} (A : ℕ → ℝ)
    (hI : ∀ p ∈ pairsIn D.s Φ, (LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.pfst p) ∧ LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement (D.s.psnd p)) ∨ wP X p = 0)
    (hj : ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t → 1 ≤ LatticeIndexAndWeightTheory.jOf X t)
    (hJ : ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, RowPairWeightBound X u (k2QJ X u j' j'') M (A j' * A j'')) :
    RowPairWeightBound X u (k2Q D u Φ) M ((∑ j ∈ Finset.Icc 1 D.R.rS, A j) ^ 2) := by
  intro S hS
  set I := Finset.Icc 1 D.R.rS with hIdef
  have key : ∀ p ∈ S, wP X p = ∑ j' ∈ I, ∑ j'' ∈ I, if k2QJ X u j' j'' p then wP X p else 0 := by
    intro p hp
    rcases hI p (hS p hp) with ⟨G1, G2⟩ | hz
    · have m1 : LatticeIndexAndWeightTheory.jOf X (D.s.pfst p) ∈ I := Finset.mem_Icc.2 ⟨hj _ G1, Nat.sub_le _ _⟩
      have m2 : LatticeIndexAndWeightTheory.jOf X (D.s.psnd p) ∈ I := Finset.mem_Icc.2 ⟨hj _ G2, Nat.sub_le _ _⟩
      rw [Finset.sum_eq_single (LatticeIndexAndWeightTheory.jOf X (D.s.pfst p)), Finset.sum_eq_single (LatticeIndexAndWeightTheory.jOf X (D.s.psnd p))]
      · rw [if_pos ⟨G1, G2, rfl, rfl⟩]
      · intro b _ hb
        exact if_neg (fun h => hb h.2.2.2.symm)
      · intro h; exact absurd m2 h
      · intro b _ hb
        exact Finset.sum_eq_zero fun c _ => if_neg (fun h => hb h.2.2.1.symm)
      · intro h; exact absurd m1 h
    · rw [hz]
      simp
  calc ∑ p ∈ S, wP X p = ∑ p ∈ S, ∑ j' ∈ I, ∑ j'' ∈ I, (if k2QJ X u j' j'' p then wP X p else 0) :=
        Finset.sum_congr rfl key
    _ = ∑ j' ∈ I, ∑ j'' ∈ I, ∑ p ∈ S, (if k2QJ X u j' j'' p then wP X p else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ j' ∈ I, ∑ j'' ∈ I, M * dimPi (hc := D.hcW) u * (A j' * A j'') := by
        refine Finset.sum_le_sum fun j' h' => Finset.sum_le_sum fun j'' h'' => ?_
        rw [← Finset.sum_filter]
        exact hJ j' h' j'' h'' _ (fun p hp => (Finset.mem_filter.1 hp).2)
    _ = M * dimPi (hc := D.hcW) u * (∑ j ∈ I, A j) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [Finset.mul_sum]



end Main

section Abstract

open Classical in

theorem double_sum_weighted_le {P Λ : Type*} (S : Finset P) (w : P → ℝ) (l' l'' : P → Λ) (a' a'' e' e'' : Λ → ℝ) (M A' A'' : ℝ)
    (hM : 0 ≤ M) (ha' : ∀ x, 0 ≤ a' x) (ha'' : ∀ x, 0 ≤ a'' x) (he'' : ∀ x, 0 ≤ e'' x) (hA' : 0 ≤ A')
    (h1 : ∀ x y, ∑ p ∈ S.filter (fun p => l' p = x ∧ l'' p = y), w p ≤ M * (e' x * e'' y))
    (h2' : ∑ x ∈ S.image l', a' x * e' x ≤ A') (h2'' : ∑ y ∈ S.image l'', a'' y * e'' y ≤ A'') :
    ∑ p ∈ S, w p * (a' (l' p) * a'' (l'' p)) ≤ M * (A' * A'') := by
  have hmaps : ∀ p ∈ S, (l' p, l'' p) ∈ (S.image l') ×ˢ (S.image l'') := fun p hp =>
    Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_product]
  calc ∑ x ∈ S.image l', ∑ y ∈ S.image l'', ∑ p ∈ S with (l' p, l'' p) = (x, y), w p * (a' (l' p) * a'' (l'' p))
      ≤ ∑ x ∈ S.image l', ∑ y ∈ S.image l'', M * ((a' x * e' x) * (a'' y * e'' y)) := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        have e1 : ∑ p ∈ S with (l' p, l'' p) = (x, y), w p * (a' (l' p) * a'' (l'' p)) =
            (∑ p ∈ S.filter (fun p => l' p = x ∧ l'' p = y), w p) * (a' x * a'' y) := by
          rw [Finset.sum_mul]
          have : S.filter (fun p => (l' p, l'' p) = (x, y)) = S.filter (fun p => l' p = x ∧ l'' p = y) := by
            ext p; simp [Prod.ext_iff]
          rw [this]
          refine Finset.sum_congr rfl fun p hp => ?_
          obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
          rw [h1, h2]
        rw [e1]
        calc (∑ p ∈ S.filter (fun p => l' p = x ∧ l'' p = y), w p) * (a' x * a'' y)
            ≤ (M * (e' x * e'' y)) * (a' x * a'' y) :=
              mul_le_mul_of_nonneg_right (h1 x y) (mul_nonneg (ha' x) (ha'' y))
          _ = M * ((a' x * e' x) * (a'' y * e'' y)) := by ring
    _ = M * ((∑ x ∈ S.image l', a' x * e' x) * (∑ y ∈ S.image l'', a'' y * e'' y)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ ≤ M * (A' * A'') := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        exact mul_le_mul h2' h2'' (Finset.sum_nonneg fun y _ => mul_nonneg (ha'' y) (he'' y)) hA'

theorem label_real_inequality (k j : ℕ) (Q Del H S G1 G2 Cs Cp r3 : ℝ) (hQ : 0 ≤ Q) (hDel : 0 < Del) (hDH : Del ≤ H * S ^ 2)
    (hH : 1 ≤ H) (hS : 1 ≤ S) (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2)
    (hexp : ((j : ℝ) + 1) + Cp * k + r3 ≤ Cs * k) :
    (Q * Del ^ (-(((k : ℝ) - 1 - j) / 2)) * G1 * S ^ (-(Cs * k))) * (Del ^ ((k : ℝ) / 2) * G2 * S ^ (Cp * k)) ≤
      Q * G1 * G2 * H ^ (((j : ℝ) + 1) / 2) * S ^ (-r3) := by
  have hS0 : 0 < S := by linarith
  have hH0 : 0 < H := by linarith
  have e1 := Formalism.HermitianLatticeCounting.Final.S6.expIdentity k j Del hDel
  have e2 : Del ^ (((j : ℝ) + 1) / 2) ≤ H ^ (((j : ℝ) + 1) / 2) * S ^ ((j : ℝ) + 1) := by
    calc Del ^ (((j : ℝ) + 1) / 2) ≤ (H * S ^ 2) ^ (((j : ℝ) + 1) / 2) :=
          Real.rpow_le_rpow hDel.le hDH (by positivity)
      _ = H ^ (((j : ℝ) + 1) / 2) * (S ^ 2) ^ (((j : ℝ) + 1) / 2) := Real.mul_rpow hH0.le (by positivity)
      _ = H ^ (((j : ℝ) + 1) / 2) * S ^ ((j : ℝ) + 1) := by
          congr 1
          rw [← Real.rpow_natCast S 2, ← Real.rpow_mul hS0.le]
          congr 1; push_cast; ring
  have e3 : S ^ ((j : ℝ) + 1) * S ^ (-(Cs * k)) * S ^ (Cp * k) ≤ S ^ (-r3) := by
    rw [← Real.rpow_add hS0, ← Real.rpow_add hS0]
    exact Real.rpow_le_rpow_of_exponent_le hS (by linarith)
  have hSa : 0 ≤ S ^ (-(Cs * k)) * S ^ (Cp * k) := by positivity
  calc (Q * Del ^ (-(((k : ℝ) - 1 - j) / 2)) * G1 * S ^ (-(Cs * k))) * (Del ^ ((k : ℝ) / 2) * G2 * S ^ (Cp * k))
      = Q * G1 * G2 * (Del ^ ((k : ℝ) / 2) * Del ^ (-(((k : ℝ) - 1 - j) / 2))) * (S ^ (-(Cs * k)) * S ^ (Cp * k)) := by ring
    _ = Q * G1 * G2 * Del ^ (((j : ℝ) + 1) / 2) * (S ^ (-(Cs * k)) * S ^ (Cp * k)) := by rw [e1]
    _ ≤ Q * G1 * G2 * (H ^ (((j : ℝ) + 1) / 2) * S ^ ((j : ℝ) + 1)) * (S ^ (-(Cs * k)) * S ^ (Cp * k)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 (by positivity)) hSa
    _ = Q * G1 * G2 * H ^ (((j : ℝ) + 1) / 2) * (S ^ ((j : ℝ) + 1) * S ^ (-(Cs * k)) * S ^ (Cp * k)) := by ring
    _ ≤ Q * G1 * G2 * H ^ (((j : ℝ) + 1) / 2) * S ^ (-r3) :=
        mul_le_mul_of_nonneg_left e3 (by positivity)

def k2R0 (N : ℕ) : ℕ := if h : 1 ≤ N then (Formalism.HermitianLatticeCounting.Final.S6.ratioBound N h).choose else 0

theorem sum_over_coranks_real (N Cn k r f : ℕ) (b g NT D' D'' S' S'' : ℝ) (hN3 : 3 * Cn ≤ N) (hN : 11 ≤ N) (hb : 2 ≤ b) (hf : 1 ≤ f)
    (hlf : Real.log f ≤ (r : ℝ) ^ 2) (hk : k2R0 N * (2 * r + 2) ^ 2 ≤ k) (hg0 : 0 < g) (hg : ((k : ℝ) * b) ^ 8 ≤ g)
    (hS' : 1 ≤ S') (hS'' : 1 ≤ S'') (hD' : 0 ≤ D') (hD'' : 0 ≤ D'') (hNT : 0 ≤ NT)
    (hDH' : D' ≤ b ^ (N * (2 * r + 2) ^ 2 * f) * S' ^ 2) (hDH'' : D'' ≤ b ^ (N * (2 * r + 2) ^ 2 * f) * S'' ^ 2)
    (hNTH : NT ≤ b ^ (N * (2 * r + 2) ^ 2 * f)) :
    1 + ∑ s ∈ Finset.Icc 1 (k - 1), ((Cn : ℝ) / g) ^ (s * k * f) * (D' * D'' * NT) ^ (Cn * s) *
          ((Cn * s * f : ℕ) : ℝ) ^ (4 * s * f) +
        (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k *
          ((b ^ (N * (2 * r + 2) ^ 2 * f)) ^ (10 * k) * (S' * S'') ^ (10 * k)) ≤
      3 * (S' * S'') ^ ((2 * Cn + 10) * k) := by
  set Hn := b ^ (N * (2 * r + 2) ^ 2 * f) with hHn
  have hN1 : 1 ≤ N := by omega
  have hH1 : 1 ≤ Hn := one_le_pow₀ (by linarith)
  have hSS : 1 ≤ S' * S'' := by nlinarith
  have hratio : ((N : ℝ) / g) ^ (k * f) * Hn ^ N * ((N * k * f : ℕ) : ℝ) ^ (4 * f) ≤ 1 / 2 := by
    have h := (Formalism.HermitianLatticeCounting.Final.S6.ratioBound N hN1).choose_spec k r f b g hb hf hlf
    unfold k2R0 at hk
    rw [dif_pos hN1] at hk
    exact h hk hg
  have hmid : ∑ s ∈ Finset.Icc 1 (k - 1), ((Cn : ℝ) / g) ^ (s * k * f) * (D' * D'' * NT) ^ (Cn * s) *
      ((Cn * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ (S' * S'') ^ (2 * Cn * k) := by
    have hsum := Formalism.HermitianLatticeCounting.Final.S6.ratioSum N k f g Hn hg0 hH1 hratio
    calc _ ≤ ∑ s ∈ Finset.Icc 1 (k - 1), (((N : ℝ) / g) ^ (s * k * f) * Hn ^ (N * s) *
          ((N * s * f : ℕ) : ℝ) ^ (4 * s * f)) * (S' * S'') ^ (2 * Cn * k) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hsk : s ≤ k := by have := (Finset.mem_Icc.1 hs).2; omega
          have h1 := Formalism.HermitianLatticeCounting.Final.S6.pairsLoss Cn s k D' D'' NT Hn S' S'' hsk hH1 hS' hS'' hD' hD'' hNT hDH' hDH'' hNTH
          have h2 : Hn ^ (3 * Cn * s) ≤ Hn ^ (N * s) := pow_le_pow_right₀ hH1 (Nat.mul_le_mul_right s hN3)
          have hCN : (Cn : ℝ) ≤ N := by exact_mod_cast (by omega : Cn ≤ N)
          have h3 : ((Cn : ℝ) / g) ^ (s * k * f) ≤ ((N : ℝ) / g) ^ (s * k * f) :=
            pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hCN hg0.le) _
          have h4 : ((Cn * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ ((N * s * f : ℕ) : ℝ) ^ (4 * s * f) := by
            refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
            exact_mod_cast Nat.mul_le_mul_right f (Nat.mul_le_mul_right s (by omega : Cn ≤ N))
          have h5 : (D' * D'' * NT) ^ (Cn * s) ≤ Hn ^ (N * s) * (S' * S'') ^ (2 * Cn * k) :=
            le_trans h1 (mul_le_mul_of_nonneg_right h2 (by positivity))
          calc ((Cn : ℝ) / g) ^ (s * k * f) * (D' * D'' * NT) ^ (Cn * s) * ((Cn * s * f : ℕ) : ℝ) ^ (4 * s * f)
              ≤ ((N : ℝ) / g) ^ (s * k * f) * (Hn ^ (N * s) * (S' * S'') ^ (2 * Cn * k)) * ((N * s * f : ℕ) : ℝ) ^ (4 * s * f) :=
                mul_le_mul (mul_le_mul h3 h5 (by positivity) (by positivity)) h4 (by positivity) (by positivity)
            _ = _ := by ring
      _ = (∑ s ∈ Finset.Icc 1 (k - 1), ((N : ℝ) / g) ^ (s * k * f) * Hn ^ (N * s) *
          ((N * s * f : ℕ) : ℝ) ^ (4 * s * f)) * (S' * S'') ^ (2 * Cn * k) := by rw [Finset.sum_mul]
      _ ≤ 1 * (S' * S'') ^ (2 * Cn * k) := mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = _ := one_mul _
  have hlast : (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k * (Hn ^ (10 * k) * (S' * S'') ^ (10 * k)) ≤
      (S' * S'') ^ (10 * k) := by
    have h := Formalism.HermitianLatticeCounting.Final.S6.sEqKClose N k f g Hn NT (by omega) hg0 hH1 hNT hNTH hratio
    have h2 : Hn ^ (10 * k) ≤ Hn ^ ((N - 1) * k) := pow_le_pow_right₀ hH1 (Nat.mul_le_mul_right k (by omega))
    have h0 : 0 ≤ (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k := by positivity
    calc _ = ((2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k * Hn ^ (10 * k)) * (S' * S'') ^ (10 * k) := by ring
      _ ≤ ((2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k * Hn ^ ((N - 1) * k)) * (S' * S'') ^ (10 * k) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h0) (by positivity)
      _ ≤ 1 * (S' * S'') ^ (10 * k) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := one_mul _
  have e1 : (1 : ℝ) ≤ (S' * S'') ^ ((2 * Cn + 10) * k) := one_le_pow₀ hSS
  have e2 : (S' * S'') ^ (2 * Cn * k) ≤ (S' * S'') ^ ((2 * Cn + 10) * k) :=
    pow_le_pow_right₀ hSS (Nat.mul_le_mul_right k (by omega))
  have e3 : (S' * S'') ^ (10 * k) ≤ (S' * S'') ^ ((2 * Cn + 10) * k) :=
    pow_le_pow_right₀ hSS (Nat.mul_le_mul_right k (by omega))
  linarith

end Abstract

section Labels

variable {D : D7} (X : TermTie D) {u : D.what₂.Word}

def k2lab (t : D.s.Term u u) : ℕ → D.host.E :=
  fun l => if l ≤ LatticeIndexAndWeightTheory.jOf X t then Dl (X.fl t).fl (X.fl' t).fl l else 0

def k2ends (D : D7) (j : ℕ) (δ : ℕ → D.host.E) : Finset ℕ := by
  classical exact (Finset.Icc 1 j).filter (fun l => δ l ≠ 0)

def k2Del (D : D7) (j : ℕ) (δ : ℕ → D.host.E) : ℝ := (Nloc (ddS D) D.R.rS j (δ j) : ℝ)

def k2sg (D : D7) (H1 : ℝ) (j : ℕ) (δ : ℕ → D.host.E) (τ : D.what₂.Tau) : ℝ :=
  (k2ends D j δ).fold max 1 (fun l => absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS))

def k2S (D : D7) (H1 : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : ℝ := ∏ τ, k2sg D H1 j δ τ

theorem ends_eq_minor_ends (t : D.s.Term u u) : LatticeIndexAndWeightTheory.ends X t = k2ends D (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) := by
  unfold LatticeIndexAndWeightTheory.ends blockEnds k2ends k2lab
  ext l
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [if_pos h1.2]; exact h2⟩
  · rintro ⟨h1, h2⟩
    rw [if_pos h1.2] at h2
    exact ⟨h1, h2⟩

theorem sigma_eq_minor_sigma (t : D.s.Term u u) (H1 : ℝ) (τ : D.what₂.Tau) :
    LatticeIndexAndWeightTheory.sg X t H1 τ = k2sg D H1 (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) τ := by
  unfold LatticeIndexAndWeightTheory.sg k2sg
  rw [ends_eq_minor_ends]
  refine Finset.fold_congr fun l hl => ?_
  have hl' : l ≤ LatticeIndexAndWeightTheory.jOf X t := by
    classical
    unfold k2ends at hl
    exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hl).1).2
  unfold k2lab
  rw [if_pos hl']

theorem discriminant_eq_minor_norm (t : D.s.Term u u) : LatticeIndexAndWeightTheory.DelJ X t = k2Del D (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) := by
  unfold LatticeIndexAndWeightTheory.DelJ LatticeIndexAndWeightTheory.NDl k2Del k2lab
  rw [if_pos le_rfl]

theorem one_le_minor_sigma (H1 : ℝ) (j : ℕ) (δ : ℕ → D.host.E) (τ : D.what₂.Tau) : 1 ≤ k2sg D H1 j δ τ := by
  unfold k2sg
  exact (Finset.le_fold_max 1).2 (Or.inl le_rfl)

theorem one_le_sigma_product (H1 : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : 1 ≤ k2S D H1 j δ := by
  unfold k2S
  have h := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : D.what₂.Tau => (1 : ℝ)) (g := fun τ => k2sg D H1 j δ τ)
    (fun _ _ => zero_le_one) (fun τ _ => one_le_minor_sigma H1 j δ τ)
  simpa using h

theorem minor_norm_nonneg (j : ℕ) (δ : ℕ → D.host.E) : 0 ≤ k2Del D j δ := by
  unfold k2Del Nloc
  exact_mod_cast FractionalIdeal.absNorm_nonneg _

end Labels

section Steps

variable {D : D7} (large₂ : SizeData₂ D) (X : TermTie D)

def k2a (CH Cs C : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : ℝ :=
  (C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * k2Del D j δ ^ (-(((D.R.k : ℝ) - 1 - j) / 2)) *
    Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(Cs * D.R.k))

def k2e (CH Ch Cp : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : ℝ :=
  k2Del D j δ ^ ((D.R.k : ℝ) / 2) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) *
    k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (Cp * D.R.k)

def LabelledPairBound (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (u : D.what₂.Word) (M CH Ch Cp : ℝ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (S : Finset (D.s.Pair u u)),
    (∀ p ∈ S, k2QJ X u j' j'' p ∧ k2lab X (D.s.pfst p) = δ' ∧ k2lab X (D.s.psnd p) = δ'') →
    ∑ p ∈ S, X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p)) ≤ M * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')

def MinorCosetSum (u : D.what₂.Word) (CH Cc : ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
    (∀ δ ∈ T, ∃ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t ∧ LatticeIndexAndWeightTheory.jOf X t = j ∧ k2lab X t = δ) →
    ∑ δ ∈ T, k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
      Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ))

def k2A1 (C Ch Cc : ℝ) (j : ℕ) : ℝ :=
  (C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
    Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) *
    Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ))

theorem one_le_height_bound {C : ℝ} (hC : 0 ≤ C) : 1 ≤ Hb large₂.sc.b C D.R.m D.R.f := by
  unfold Hb
  exact Real.one_le_rpow (by linarith [two_le_scale_b D large₂]) (by positivity)

theorem amplitude_label_nonneg {CH Cs C : ℝ} (hC : 0 ≤ C) (j : ℕ) (δ : ℕ → D.host.E) : 0 ≤ k2a large₂ CH Cs C j δ := by
  unfold k2a
  have h1 : 0 ≤ C / (D.R.k : ℝ) := by positivity
  have h2 := minor_norm_nonneg (D := D) j δ
  have h3 : 0 ≤ Hb large₂.sc.b C D.R.m D.R.f := by linarith [one_le_height_bound large₂ hC]
  have h4 : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by linarith [one_le_sigma_product (D := D) (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ]
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)) (Real.rpow_nonneg h3 _))
    (Real.rpow_nonneg h4 _)

theorem amplitude_exponent_nonneg {CH Ch Cp : ℝ} (hC : 0 ≤ Ch) (j : ℕ) (δ : ℕ → D.host.E) : 0 ≤ k2e large₂ CH Ch Cp j δ := by
  unfold k2e
  have h2 := minor_norm_nonneg (D := D) j δ
  have h3 : 0 ≤ Hb large₂.sc.b Ch D.R.m D.R.f := by linarith [one_le_height_bound large₂ hC]
  have h4 : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by linarith [one_le_sigma_product (D := D) (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ]
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg h2 _) (Real.rpow_nonneg h3 _)) (Real.rpow_nonneg h4 _)

def AmplitudeNormBound (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (u : D.what₂.Word) (CH Cs C : ℝ) : Prop :=
  ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t →
    aT X t ≤ Real.sqrt (dimPi (hc := D.hcW) u) * (om u t * k2a large₂ CH Cs C (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t))


theorem minor_norm_le_height {om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ} {CH Cs C : ℝ} (h2 : LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C)
    {u : D.what₂.Word} (hT : LatticeIndexAndWeightTheory.TieOK X u) (t : D.s.Term u u) (hG : LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t) :
    k2Del D (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) ≤
      Hb large₂.sc.b C D.R.m D.R.f * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) ^ 2 := by
  have h := (h2 u hT t hG).2.1
  rw [discriminant_eq_minor_norm] at h
  simp only [sigma_eq_minor_sigma] at h
  rw [Finset.prod_pow] at h
  exact h

theorem minor_norm_pos (h3 : LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X) {u : D.what₂.Word} (hT : LatticeIndexAndWeightTheory.TieOK X u) (t : D.s.Term u u) (hG : LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t) :
    0 < k2Del D (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) := by
  obtain ⟨hb, hg, hi, h⟩ := h3 u hT t hG
  rw [discriminant_eq_minor_norm] at h
  have hb' : (0 : ℝ) < (LatticeIndexAndWeightTheory.b1T X t : ℝ) ^ 2 := by positivity
  have h1 : (0 : ℝ) < (LatticeIndexAndWeightTheory.gT X t : ℝ) * (LatticeIndexAndWeightTheory.iT X t : ℝ) ^ 2 := by positivity
  have h2 := lt_of_lt_of_le h1 h
  by_contra hn
  have : k2Del D (LatticeIndexAndWeightTheory.jOf X t) (k2lab X t) / (LatticeIndexAndWeightTheory.b1T X t : ℝ) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) hb'.le
  linarith

theorem label_sum_bound {om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ} {CH Cs C Ch Cp Cc : ℝ} (hC : 0 ≤ C) (hCp : 0 ≤ Ch)
    (hCs : Cp + 4 ≤ Cs) (h2 : LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C) (h3 : LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X) {u : D.what₂.Word} (hT : LatticeIndexAndWeightTheory.TieOK X u)
    (hc : MinorCosetSum large₂ X u CH Cc) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.rS) (T : Finset (ℕ → D.host.E))
    (hTm : ∀ δ ∈ T, ∃ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t ∧ LatticeIndexAndWeightTheory.jOf X t = j ∧ k2lab X t = δ) :
    ∑ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ ≤ k2A1 large₂ C Ch Cc j := by
  set Q := (C / (D.R.k : ℝ)) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) with hQ
  set G1 := Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) with hG1
  set G2 := Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) with hG2
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg (by positivity) _
  have hH := one_le_height_bound large₂ hC (D := D)
  have hHp := one_le_height_bound large₂ hCp (D := D)
  have hG10 : 0 ≤ G1 := Real.rpow_nonneg (by linarith) _
  have hG20 : 0 ≤ G2 := Real.rpow_nonneg (by linarith) _
  have hjr : j ≤ D.R.rS := (Finset.mem_Icc.1 hj).2
  have hrk : (D.R.rS : ℝ) + 1 ≤ D.R.k := by
    have h1 := two_rank_add_two_eq_m D; have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.rS + 1 ≤ D.R.k)
  have hexp : ((j : ℝ) + 1) + Cp * D.R.k + 3 * (D.R.rS : ℝ) ≤ Cs * D.R.k := by
    have hj' : (j : ℝ) ≤ D.R.rS := by exact_mod_cast hjr
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have : (Cp + 4) * (D.R.k : ℝ) ≤ Cs * D.R.k := mul_le_mul_of_nonneg_right hCs hk0
    have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    nlinarith
  have each : ∀ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ ≤
      Q * G1 * G2 * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) *
        k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := by
    intro δ hδ
    obtain ⟨t, hG, rfl, rfl⟩ := hTm δ hδ
    exact label_real_inequality D.R.k (LatticeIndexAndWeightTheory.jOf X t) Q _ _ _ G1 G2 Cs Cp (3 * (D.R.rS : ℝ)) hQ0 (minor_norm_pos X h3 hT t hG)
      (minor_norm_le_height large₂ X h2 hT t hG) hH (one_le_sigma_product _ _ _) hG10 hG20 hexp
  calc ∑ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ
      ≤ ∑ δ ∈ T, Q * G1 * G2 * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) *
        k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := Finset.sum_le_sum each
    _ = Q * G1 * G2 * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) *
        ∑ δ ∈ T, k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ Q * G1 * G2 * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) *
        Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)) :=
        mul_le_mul_of_nonneg_left (hc j hj T hTm)
          (mul_nonneg (mul_nonneg (mul_nonneg hQ0 hG10) hG20) (Real.rpow_nonneg (by linarith) _))
    _ = k2A1 large₂ C Ch Cc j := rfl

end Steps

section Assembly

variable {D : D7} (large₂ : SizeData₂ D) (X : TermTie D)

open Classical in

theorem rank_pair_bound_of_steps {om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ} {CH Cs C Ch Cp Cc M : ℝ} (hC : 0 ≤ C) (hCp : 0 ≤ Ch)
    (hCc : 0 ≤ Cc) (hCs : Cp + 4 ≤ Cs) (hM : 0 ≤ M) (hom : ∀ u t, 0 < om u t) {u : D.what₂.Word}
    (h1 : AmplitudeNormBound large₂ X om u CH Cs C)
    (h2 : LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C) (h3 : LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X) (hT : LatticeIndexAndWeightTheory.TieOK X u)
    (hp : LabelledPairBound large₂ X om u M CH Ch Cp) (hc : MinorCosetSum large₂ X u CH Cc)
    (j' : ℕ) (hj' : j' ∈ Finset.Icc 1 D.R.rS) (j'' : ℕ) (hj'' : j'' ∈ Finset.Icc 1 D.R.rS) :
    RowPairWeightBound X u (k2QJ X u j' j'') M (k2A1 large₂ C Ch Cc j' * k2A1 large₂ C Ch Cc j'') := by
  intro S hS
  have hd : 0 ≤ dimPi (hc := D.hcW) u := by rw [← X.Hpi_dim u]; positivity
  have hA1 : ∀ j, 0 ≤ k2A1 large₂ C Ch Cc j := by
    intro j
    unfold k2A1
    have a1 : 0 ≤ C / (D.R.k : ℝ) := by positivity
    have a2 : 0 ≤ Hb large₂.sc.b C D.R.m D.R.f := by linarith [one_le_height_bound large₂ hC (D := D)]
    have a3 : 0 ≤ Hb large₂.sc.b Ch D.R.m D.R.f := by linarith [one_le_height_bound large₂ hCp (D := D)]
    have a4 : 0 ≤ Hb large₂.sc.b Cc D.R.m D.R.f := by linarith [one_le_height_bound large₂ hCc (D := D)]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg a1 _) (Real.rpow_nonneg a2 _))
      (Real.rpow_nonneg a3 _)) (Real.rpow_nonneg a2 _)) (Real.rpow_nonneg a4 _)
  have each : ∀ p ∈ S, wP X p ≤ dimPi (hc := D.hcW) u *
      ((X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p))) *
        (k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p)))) := by
    intro p hp'
    obtain ⟨G1, G2, e1, e2⟩ := hS p hp'
    have b1 := h1 _ G1
    have b2 := h1 _ G2
    rw [e1] at b1
    rw [e2] at b2
    have hsq := Real.mul_self_sqrt hd
    have b3 : aT X (D.s.pfst p) * aT X (D.s.psnd p) ≤
        (Real.sqrt (dimPi (hc := D.hcW) u) * (om u (D.s.pfst p) * k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)))) *
        (Real.sqrt (dimPi (hc := D.hcW) u) * (om u (D.s.psnd p) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p)))) :=
      mul_le_mul b1 b2 (aT_nonneg _ _)
        (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hom _ _).le (amplitude_label_nonneg large₂ hC _ _)))
    unfold wP
    calc X.wRow p * (aT X (D.s.pfst p) * aT X (D.s.psnd p))
        ≤ X.wRow p * ((Real.sqrt (dimPi (hc := D.hcW) u) * (om u (D.s.pfst p) * k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)))) *
        (Real.sqrt (dimPi (hc := D.hcW) u) * (om u (D.s.psnd p) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p))))) :=
          mul_le_mul_of_nonneg_left b3 (X.wRow_pos p).le
      _ = (Real.sqrt (dimPi (hc := D.hcW) u) * Real.sqrt (dimPi (hc := D.hcW) u)) *
          ((X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p))) *
        (k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p)))) := by ring
      _ = _ := by rw [hsq]
  have dbl := double_sum_weighted_le S (fun p => X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p)))
    (fun p => k2lab X (D.s.pfst p)) (fun p => k2lab X (D.s.psnd p))
    (k2a large₂ CH Cs C j') (k2a large₂ CH Cs C j'') (k2e large₂ CH Ch Cp j') (k2e large₂ CH Ch Cp j'') M
    (k2A1 large₂ C Ch Cc j') (k2A1 large₂ C Ch Cc j'') hM (amplitude_label_nonneg large₂ hC j') (amplitude_label_nonneg large₂ hC j'')
    (amplitude_exponent_nonneg large₂ hCp j'') (hA1 j')
    (fun x y => hp j' hj' j'' hj'' x y _ (fun p hp' => by
      obtain ⟨m1, m2, m3⟩ := Finset.mem_filter.1 hp'
      exact ⟨hS p m1, m2, m3⟩))
    (label_sum_bound large₂ X hC hCp hCs h2 h3 hT hc j' hj' _ (fun δ hδ => by
      obtain ⟨p, m1, rfl⟩ := Finset.mem_image.1 hδ
      exact ⟨_, (hS p m1).1, (hS p m1).2.2.1, rfl⟩))
    (label_sum_bound large₂ X hC hCp hCs h2 h3 hT hc j'' hj'' _ (fun δ hδ => by
      obtain ⟨p, m1, rfl⟩ := Finset.mem_image.1 hδ
      exact ⟨_, (hS p m1).2.1, (hS p m1).2.2.2, rfl⟩))
  calc ∑ p ∈ S, wP X p ≤ ∑ p ∈ S, dimPi (hc := D.hcW) u *
      ((X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p))) *
        (k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p)))) := Finset.sum_le_sum each
    _ = dimPi (hc := D.hcW) u * ∑ p ∈ S, ((X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p))) *
        (k2a large₂ CH Cs C j' (k2lab X (D.s.pfst p)) * k2a large₂ CH Cs C j'' (k2lab X (D.s.psnd p)))) := by rw [Finset.mul_sum]
    _ ≤ dimPi (hc := D.hcW) u * (M * (k2A1 large₂ C Ch Cc j' * k2A1 large₂ C Ch Cc j'')) := mul_le_mul_of_nonneg_left dbl hd
    _ = _ := by ring

def k2Cf (C Ch Cc : ℝ) : ℝ := 1 + C + C ^ 2 + Ch ^ 2 + Cc ^ 2

theorem rank_contribution_le {C Ch Cc : ℝ} (hC : 0 ≤ C) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.rS) :
    k2A1 large₂ C Ch Cc j ≤ k2A D large₂ (k2Cf C Ch Cc) j := by
  have hjr : j ≤ D.R.rS := (Finset.mem_Icc.1 hj).2
  have hm := two_rank_add_two_eq_m D
  have hmk := D.R.m_add_three_le_k
  have hjk : j ≤ D.R.k - 1 := by omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hb0 : 0 < large₂.sc.b := by linarith [two_le_scale_b D large₂]
  have hcast : ((j * (D.R.k - 1 - j) * D.R.f : ℕ) : ℝ) = (j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hjk, Nat.cast_sub hk1, Nat.cast_one]
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast hk1
  have hCf : C ≤ k2Cf C Ch Cc := by unfold k2Cf; nlinarith [sq_nonneg C, sq_nonneg Ch, sq_nonneg Cc]
  have hQ : (C / (D.R.k : ℝ)) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) ≤
      (k2Cf C Ch Cc / D.R.k) ^ (j * (D.R.k - 1 - j) * D.R.f) := by
    rw [← hcast, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hCf hk0.le) _
  have hHb : ∀ c y : ℝ, Hb large₂.sc.b c D.R.m D.R.f ^ y = Real.exp (large₂.sc.L * (c * (D.R.m : ℝ) ^ 2 * D.R.f * y)) := by
    intro c y
    unfold Hb
    rw [← Real.rpow_mul hb0.le, Real.rpow_def_of_pos hb0, log_scale_eq_L D large₂]
  have hL : 0 < large₂.sc.L := lt_trans one_pos (one_lt_scale_L D large₂)
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hrm : (D.R.rS : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : D.R.rS ≤ D.R.m)
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hr4 : (D.R.rS : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ hr0 hrm 4
  have hm4 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hj2 : ((j : ℝ) + 1) / 2 ≤ (D.R.m : ℝ) ^ 4 := by
    have : (j : ℝ) ≤ D.R.rS := by exact_mod_cast hjr
    linarith
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hexp : Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) *
      Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)) ≤
      Real.exp (k2Cf C Ch Cc * (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L) := by
    rw [hHb, hHb, hHb, hHb, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have key : C * (C * (D.R.rS : ℝ) ^ 4) + Ch * (Ch * (D.R.rS : ℝ) ^ 4) + C * (((j : ℝ) + 1) / 2) + Cc * (Cc * (D.R.rS : ℝ)) ≤
        k2Cf C Ch Cc * (D.R.m : ℝ) ^ 4 := by
      unfold k2Cf
      have t1 : C * (C * (D.R.rS : ℝ) ^ 4) ≤ C ^ 2 * (D.R.m : ℝ) ^ 4 := by
        have := mul_le_mul_of_nonneg_left hr4 (sq_nonneg C); nlinarith
      have t2 : Ch * (Ch * (D.R.rS : ℝ) ^ 4) ≤ Ch ^ 2 * (D.R.m : ℝ) ^ 4 := by
        have := mul_le_mul_of_nonneg_left hr4 (sq_nonneg Ch); nlinarith
      have t3 : C * (((j : ℝ) + 1) / 2) ≤ C * (D.R.m : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hj2 hC
      have t4 : Cc * (Cc * (D.R.rS : ℝ)) ≤ Cc ^ 2 * (D.R.m : ℝ) ^ 4 := by
        have := mul_le_mul_of_nonneg_left (le_trans hrm hm4) (sq_nonneg Cc); nlinarith
      have t5 : 0 ≤ (D.R.m : ℝ) ^ 4 := by positivity
      nlinarith
    have hfac : 0 ≤ large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f) := by positivity
    have := mul_le_mul_of_nonneg_left key hfac
    calc _ = large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f) * (C * (C * (D.R.rS : ℝ) ^ 4) + Ch * (Ch * (D.R.rS : ℝ) ^ 4) +
          C * (((j : ℝ) + 1) / 2) + Cc * (Cc * (D.R.rS : ℝ))) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  unfold k2A1 k2A
  have hQ0 : 0 ≤ (C / (D.R.k : ℝ)) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) := Real.rpow_nonneg (by positivity) _
  calc _ = (C / (D.R.k : ℝ)) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) *
        (Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) *
      Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ))) := by ring
    _ ≤ (k2Cf C Ch Cc / D.R.k) ^ (j * (D.R.k - 1 - j) * D.R.f) * Real.exp (k2Cf C Ch Cc * (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L) :=
        mul_le_mul hQ hexp (by rw [hHb, hHb, hHb, hHb]; positivity) (by
          have : 0 ≤ k2Cf C Ch Cc / (D.R.k : ℝ) := div_nonneg (le_trans hC hCf) hk0.le
          positivity)
    _ = _ := by ring

end Assembly

section Final

variable {D : D7} (large₂ : SizeData₂ D) (X : TermTie D)






def LineInequalityFamily (D : D7) (u : D.what₂.Word) : Prop :=
  Summable (fun p : pairsIn D.s (k2G0 D u) => ‖D.s.pval p.1‖) →
    hsNormSq (KOf D.s u u (k2G0 D u)) ≤
      (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f * gaG D * (∑' p : pairsIn D.s (k2G0 D u), D.s.pval p.1).re




def SingleTermRemainder (C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 Ch Cp Cc : ℝ) : Prop :=
  (∀ u, MinorCosetSum large₂ X u CH Cc) ∧
  ∀ u : D.what₂.Word, ∃ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (LatV D)),
    F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧
    ∀ om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ, (∀ u t, 0 < om u t) → LatticeIndexAndWeightTheory.TieOK X u → LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs ComplexParameterFamilyContinuity →
      LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X → LatticeIndexAndWeightTheory.TermWeightSumAboveBound D large₂ X om ComplexParameterFamilyContinuity →
      LatticeIndexAndWeightTheory.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 C4 → LatticeIndexAndWeightTheory.adm5 → LabelledPairBound large₂ X om u (massRows D F0 what₂) CH Ch Cp


end Final

section PairsS

variable {D : D7} (large₂ : SizeData₂ D) (X : TermTie D)

def k2s {u : D.what₂.Word} (p : D.s.Pair u u) : ℕ :=
  min D.R.k (Module.finrank D.host.E (Hp (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p))) -
    Module.finrank D.host.E
      (Lat.Th (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.beta p)))

def k2Fm (u : D.what₂.Word) (Cn : ℕ) (Dp Dpp : ℝ) (s : ℕ) : ℝ :=
  ((Cn : ℝ) / (gS D : ℝ)) ^ (s * D.R.k * D.R.f) * (Dp * Dpp * NT D u) ^ (Cn * s) * ((Cn * s * D.R.f : ℕ) : ℝ) ^ (4 * s * D.R.f)

def k2Fk (u : D.what₂.Word) (Hh SS : ℝ) : ℝ :=
  (2 / (gS D : ℝ)) ^ (D.R.k * D.R.k * D.R.f) * ((4 * D.R.k * D.R.f : ℕ) : ℝ) ^ (4 * D.R.k * D.R.f) * NT D u ^ D.R.k *
    (Hh ^ (10 * D.R.k) * SS ^ (10 * D.R.k))

def k2F (u : D.what₂.Word) (Cn : ℕ) (Dp Dpp Hh SS : ℝ) (s : ℕ) : ℝ :=
  if s = 0 then 1 else if s < D.R.k then k2Fm u Cn Dp Dpp s else if s = D.R.k then k2Fk u Hh SS else 0

def PairsOfCorank (om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ) (u : D.what₂.Word) (M CH Ch Cp C : ℝ) (Cn : ℕ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (s : ℕ) (S : Finset (D.s.Pair u u)),
    (∀ p ∈ S, k2QJ X u j' j'' p ∧ k2lab X (D.s.pfst p) = δ' ∧ k2lab X (D.s.psnd p) = δ'' ∧ k2s X p = s) →
    ∑ p ∈ S, X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p)) ≤
      M * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'') *
        k2F u Cn (k2Del D j' δ') (k2Del D j'' δ'') (Hb large₂.sc.b C D.R.m D.R.f)
          (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j' δ' * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j'' δ'') s

open Classical in

theorem sum_corank_terms_le (u : D.what₂.Word) (Cn : ℕ) (Dp Dpp Hh SS : ℝ) (hm : ∀ s, 0 ≤ k2Fm u Cn Dp Dpp s) (hk : 0 ≤ k2Fk u Hh SS)
    (T : Finset ℕ) :
    ∑ s ∈ T, k2F u Cn Dp Dpp Hh SS s ≤ 1 + ∑ s ∈ Finset.Icc 1 (D.R.k - 1), k2Fm u Cn Dp Dpp s + k2Fk u Hh SS := by
  have each : ∀ s, k2F u Cn Dp Dpp Hh SS s ≤ (if s = 0 then 1 else 0) +
      (if s ∈ Finset.Icc 1 (D.R.k - 1) then k2Fm u Cn Dp Dpp s else 0) + (if s = D.R.k then k2Fk u Hh SS else 0) := by
    intro s
    unfold k2F
    by_cases h0 : s = 0
    · rw [if_pos h0, if_pos h0]
      have a1 : 0 ≤ (if s ∈ Finset.Icc 1 (D.R.k - 1) then k2Fm u Cn Dp Dpp s else 0) := by split_ifs <;> simp [hm]
      have a2 : 0 ≤ (if s = D.R.k then k2Fk u Hh SS else 0) := by split_ifs <;> simp [hk]
      linarith
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : s < D.R.k
      · rw [if_pos h1, if_pos (Finset.mem_Icc.2 ⟨by omega, by omega⟩), if_neg (by omega)]
        simp
      · have hnot : s ∉ Finset.Icc 1 (D.R.k - 1) := fun h => h1 (by have := (Finset.mem_Icc.1 h); omega)
        rw [if_neg h1, if_neg hnot]
        simp
  calc ∑ s ∈ T, k2F u Cn Dp Dpp Hh SS s ≤ ∑ s ∈ T, ((if s = 0 then (1 : ℝ) else 0) +
      (if s ∈ Finset.Icc 1 (D.R.k - 1) then k2Fm u Cn Dp Dpp s else 0) + (if s = D.R.k then k2Fk u Hh SS else 0)) :=
        Finset.sum_le_sum fun s _ => each s
    _ = ∑ s ∈ T, (if s = 0 then (1 : ℝ) else 0) + ∑ s ∈ T, (if s ∈ Finset.Icc 1 (D.R.k - 1) then k2Fm u Cn Dp Dpp s else 0) +
        ∑ s ∈ T, (if s = D.R.k then k2Fk u Hh SS else 0) := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := by
        have b1 : ∑ s ∈ T, (if s = 0 then (1 : ℝ) else 0) ≤ 1 := by
          rw [Finset.sum_ite_eq' T 0 (fun _ => (1 : ℝ))]; split_ifs <;> simp
        have b3 : ∑ s ∈ T, (if s = D.R.k then k2Fk u Hh SS else 0) ≤ k2Fk u Hh SS := by
          rw [Finset.sum_ite_eq' T D.R.k (fun _ => k2Fk u Hh SS)]; split_ifs <;> simp [hk]
        have b2 : ∑ s ∈ T, (if s ∈ Finset.Icc 1 (D.R.k - 1) then k2Fm u Cn Dp Dpp s else 0) ≤
            ∑ s ∈ Finset.Icc 1 (D.R.k - 1), k2Fm u Cn Dp Dpp s := by
          rw [← Finset.sum_filter]
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => (Finset.mem_filter.1 hs).2) (fun s _ _ => hm s)
        linarith

theorem exponent_weight_absorb {CH Ch Cp : ℝ} (hCh : 0 ≤ Ch) (hr : 1 ≤ D.R.rS) (Cn : ℕ) (j : ℕ) (δ : ℕ → D.host.E) :
    2 * k2e large₂ CH Ch Cp j δ * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((2 * Cn + 10) * D.R.k) ≤
      k2e large₂ CH (Ch + 1) (Cp + 2 * Cn + 10) j δ := by
  set S := k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ with hS
  have hS1 : 1 ≤ S := one_le_sigma_product _ _ _
  have hS0 : 0 < S := by linarith
  have hb0 : 0 < large₂.sc.b := by linarith [two_le_scale_b D large₂]
  have hHb : ∀ c y : ℝ, Hb large₂.sc.b c D.R.m D.R.f ^ y = Real.exp (large₂.sc.L * (c * (D.R.m : ℝ) ^ 2 * D.R.f * y)) := by
    intro c y
    unfold Hb
    rw [← Real.rpow_mul hb0.le, Real.rpow_def_of_pos hb0, log_scale_eq_L D large₂]
  have hL := one_lt_scale_L D large₂
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast one_le_degree_f D
  have hrR : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hr
  have hr4 : (1 : ℝ) ≤ (D.R.rS : ℝ) ^ 4 := one_le_pow₀ hrR
  have h2 : 2 * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) ≤
      Hb large₂.sc.b (Ch + 1) D.R.m D.R.f ^ ((Ch + 1) * (D.R.rS : ℝ) ^ 4) := by
    rw [hHb, hHb]
    have e1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    calc 2 * Real.exp (large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2 * D.R.f * (Ch * (D.R.rS : ℝ) ^ 4)))
        ≤ Real.exp 1 * Real.exp (large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2 * D.R.f * (Ch * (D.R.rS : ℝ) ^ 4))) :=
          mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
      _ = Real.exp (1 + large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2 * D.R.f * (Ch * (D.R.rS : ℝ) ^ 4))) := by rw [Real.exp_add]
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          have hq : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 * D.R.f * (D.R.rS : ℝ) ^ 4 := by
            have : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := one_le_pow₀ (by linarith)
            calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
              _ ≤ _ := mul_le_mul (mul_le_mul this hfR zero_le_one (by positivity)) hr4 zero_le_one (by positivity)
          have hq2 : 1 ≤ large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f * (D.R.rS : ℝ) ^ 4) := by nlinarith
          have hq3 : 0 ≤ large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f * (D.R.rS : ℝ) ^ 4) * (2 * Ch) := by positivity
          calc 1 + large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2 * D.R.f * (Ch * (D.R.rS : ℝ) ^ 4))
              ≤ large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f * (D.R.rS : ℝ) ^ 4) +
                large₂.sc.L * ((D.R.m : ℝ) ^ 2 * D.R.f * (D.R.rS : ℝ) ^ 4) * (2 * Ch) +
                large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2 * D.R.f * (Ch * (D.R.rS : ℝ) ^ 4)) := by linarith
            _ = _ := by ring
  have h3 : S ^ ((Cp + 2 * Cn + 10) * (D.R.k : ℝ)) = S ^ (Cp * (D.R.k : ℝ)) * S ^ ((2 * Cn + 10) * D.R.k) := by
    rw [← Real.rpow_natCast S ((2 * Cn + 10) * D.R.k), ← Real.rpow_add hS0]
    congr 1; push_cast; ring
  unfold k2e
  rw [← hS, h3]
  have hD : 0 ≤ k2Del D j δ ^ ((D.R.k : ℝ) / 2) := Real.rpow_nonneg (minor_norm_nonneg j δ) _
  calc 2 * (k2Del D j δ ^ ((D.R.k : ℝ) / 2) * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4) * S ^ (Cp * (D.R.k : ℝ))) *
        S ^ ((2 * Cn + 10) * D.R.k)
      = (2 * Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) *
        (k2Del D j δ ^ ((D.R.k : ℝ) / 2) * (S ^ (Cp * (D.R.k : ℝ)) * S ^ ((2 * Cn + 10) * D.R.k))) := by ring
    _ ≤ Hb large₂.sc.b (Ch + 1) D.R.m D.R.f ^ ((Ch + 1) * (D.R.rS : ℝ) ^ 4) *
        (k2Del D j δ ^ ((D.R.k : ℝ) / 2) * (S ^ (Cp * (D.R.k : ℝ)) * S ^ ((2 * Cn + 10) * D.R.k))) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring

theorem height_bound_le_nat_pow {C : ℝ} (N : ℕ) (hCN : C ≤ N) :
    Hb large₂.sc.b C D.R.m D.R.f ≤ large₂.sc.b ^ (N * (2 * D.R.rS + 2) ^ 2 * D.R.f) := by
  unfold Hb
  rw [two_rank_add_two_eq_m D, ← Real.rpow_natCast large₂.sc.b (N * D.R.m ^ 2 * D.R.f)]
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith [two_le_scale_b D large₂]
  refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
  push_cast
  have h0 : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f := by positivity
  have := mul_le_mul_of_nonneg_right hCN h0
  calc C * (D.R.m : ℝ) ^ 2 * D.R.f = C * ((D.R.m : ℝ) ^ 2 * D.R.f) := by ring
    _ ≤ N * ((D.R.m : ℝ) ^ 2 * D.R.f) := this
    _ = _ := by ring

open Classical in

theorem pairs_of_corank_pairs {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0)
    {om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ} {CH Cs C Ch Cp M : ℝ} (Cn N : ℕ) (hCh : 0 ≤ Ch) (hM : 0 ≤ M)
    (hN3 : 3 * Cn ≤ N) (hN : 11 ≤ N) (hCN : C ≤ N) (hCT : CT ≤ N) (hk : k2R0 N * D.R.m ^ 2 ≤ D.R.k) {u : D.what₂.Word}
    (h2 : LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs C) (hT : LatticeIndexAndWeightTheory.TieOK X u) (hS : PairsOfCorank large₂ X om u M CH Ch Cp C Cn) :
    LabelledPairBound large₂ X om u M CH (Ch + 1) (Cp + 2 * Cn + 10) := by
  intro j' hj' j'' hj'' δ' δ'' S hSm
  have hCh1 : 0 ≤ Ch + 1 := by linarith
  rcases S.eq_empty_or_nonempty with rfl | ⟨p0, hp0⟩
  · simp only [Finset.sum_empty]
    exact mul_nonneg hM (mul_nonneg (amplitude_exponent_nonneg large₂ hCh1 _ _) (amplitude_exponent_nonneg large₂ hCh1 _ _))
  obtain ⟨⟨G1, G2, e1, e2⟩, l1, l2⟩ := hSm p0 hp0
  have hr : 1 ≤ D.R.rS := le_trans (Finset.mem_Icc.1 hj').1 (Finset.mem_Icc.1 hj').2
  set S' := k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j' δ' with hS'
  set S'' := k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j'' δ'' with hS''
  set Hn := large₂.sc.b ^ (N * (2 * D.R.rS + 2) ^ 2 * D.R.f) with hHn
  have hS'1 : 1 ≤ S' := one_le_sigma_product _ _ _
  have hS''1 : 1 ≤ S'' := one_le_sigma_product _ _ _
  have hHbn := height_bound_le_nat_pow large₂ (D := D) N hCN
  have hD' : k2Del D j' δ' ≤ Hn * S' ^ 2 := by
    have h := minor_norm_le_height large₂ X h2 hT _ G1
    rw [e1, l1] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hHbn (by positivity))
  have hD'' : k2Del D j'' δ'' ≤ Hn * S'' ^ 2 := by
    have h := minor_norm_le_height large₂ X h2 hT _ G2
    rw [e2, l2] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hHbn (by positivity))
  have hb := two_le_scale_b D large₂
  have hk5 : (5 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m
    exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hkb1 : (1 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := one_le_pow₀ (by nlinarith)
  have hg : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (gS D : ℝ) := by
    unfold gS
    push_cast
    have g0 := (hH.2.2.1 0).1
    have g1 := (hH.2.2.1 1).1
    nlinarith
  have hg0 : (0 : ℝ) < (gS D : ℝ) := by linarith
  have hNT0 : 0 ≤ NT D u := by unfold NT; positivity
  have hNT : NT D u ≤ Hn := by
    have hTu := (hH.2.2.2.2.2.2.1 u).1
    unfold NT
    calc ((D.mem u).A.T : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ (CT * (D.R.m : ℝ))) ^ D.R.f := pow_le_pow_left₀ (Nat.cast_nonneg _) hTu _
      _ = large₂.sc.b ^ (CT * (D.R.m : ℝ) * D.R.f) := by
          rw [← Real.rpow_natCast (large₂.sc.b ^ (CT * (D.R.m : ℝ))) D.R.f, ← Real.rpow_mul (by linarith)]
      _ ≤ Hn := by
          rw [hHn, two_rank_add_two_eq_m D, ← Real.rpow_natCast large₂.sc.b (N * D.R.m ^ 2 * D.R.f)]
          refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
          push_cast
          have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
          have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
          have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
          have a1 : CT * (D.R.m : ℝ) ≤ N * (D.R.m : ℝ) ^ 2 := by
            have : CT * (D.R.m : ℝ) ≤ N * (D.R.m : ℝ) := mul_le_mul_of_nonneg_right hCT (by linarith)
            have : (N : ℝ) * (D.R.m : ℝ) ≤ N * (D.R.m : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hN0
            linarith
          exact mul_le_mul_of_nonneg_right a1 hf0
  have hreal := sum_over_coranks_real N Cn D.R.k D.R.rS D.R.f large₂.sc.b (gS D : ℝ) (NT D u) (k2Del D j' δ') (k2Del D j'' δ'') S' S''
    hN3 hN hb (one_le_degree_f D) hH.2.2.2.2.2.1 (by rw [two_rank_add_two_eq_m D]; exact hk) hg0 hg hS'1 hS''1 (minor_norm_nonneg _ _) (minor_norm_nonneg _ _)
    hNT0 hD' hD'' hNT
  have hFm0 : ∀ s, 0 ≤ k2Fm u Cn (k2Del D j' δ') (k2Del D j'' δ'') s := by
    intro s
    unfold k2Fm
    have := minor_norm_nonneg (D := D) j' δ'
    have := minor_norm_nonneg (D := D) j'' δ''
    positivity
  have hHb0 : 0 ≤ Hb large₂.sc.b C D.R.m D.R.f := by unfold Hb; exact Real.rpow_nonneg (by linarith) _
  have hFk0 : 0 ≤ k2Fk u (Hb large₂.sc.b C D.R.m D.R.f) (S' * S'') := by unfold k2Fk; positivity
  have hFk : k2Fk u (Hb large₂.sc.b C D.R.m D.R.f) (S' * S'') ≤ k2Fk u Hn (S' * S'') := by
    unfold k2Fk
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hHb0 hHbn _) (by positivity)
  set E0 := k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'' with hE0
  have hE00 : 0 ≤ E0 := mul_nonneg (amplitude_exponent_nonneg large₂ hCh _ _) (amplitude_exponent_nonneg large₂ hCh _ _)
  have hmaps : ∀ p ∈ S, k2s X p ∈ S.image (k2s X) := fun p hp => Finset.mem_image_of_mem _ hp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ s ∈ S.image (k2s X), ∑ p ∈ S with k2s X p = s, X.wRow p * (om u (D.s.pfst p) * om u (D.s.psnd p))
      ≤ ∑ s ∈ S.image (k2s X), M * E0 * k2F u Cn (k2Del D j' δ') (k2Del D j'' δ'') (Hb large₂.sc.b C D.R.m D.R.f) (S' * S'') s := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact hS j' hj' j'' hj'' δ' δ'' s _ (fun p hp => by
          obtain ⟨m1, m2⟩ := Finset.mem_filter.1 hp
          exact ⟨(hSm p m1).1, (hSm p m1).2.1, (hSm p m1).2.2, m2⟩)
    _ = M * E0 * ∑ s ∈ S.image (k2s X), k2F u Cn (k2Del D j' δ') (k2Del D j'' δ'') (Hb large₂.sc.b C D.R.m D.R.f) (S' * S'') s := by
        rw [Finset.mul_sum]
    _ ≤ M * E0 * (3 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hM hE00)
        refine le_trans (sum_corank_terms_le u Cn _ _ _ _ hFm0 hFk0 _) ?_
        refine le_trans ?_ hreal
        have : k2Fk u Hn (S' * S'') = (2 / (gS D : ℝ)) ^ (D.R.k * D.R.k * D.R.f) * ((4 * D.R.k * D.R.f : ℕ) : ℝ) ^ (4 * D.R.k * D.R.f) *
            NT D u ^ D.R.k * (Hn ^ (10 * D.R.k) * (S' * S'') ^ (10 * D.R.k)) := rfl
        rw [← this]
        have hmid : ∑ s ∈ Finset.Icc 1 (D.R.k - 1), k2Fm u Cn (k2Del D j' δ') (k2Del D j'' δ'') s =
            ∑ s ∈ Finset.Icc 1 (D.R.k - 1), ((Cn : ℝ) / (gS D : ℝ)) ^ (s * D.R.k * D.R.f) *
              (k2Del D j' δ' * k2Del D j'' δ'' * NT D u) ^ (Cn * s) * ((Cn * s * D.R.f : ℕ) : ℝ) ^ (4 * s * D.R.f) := rfl
        rw [← hmid]
        linarith
    _ ≤ M * (k2e large₂ CH (Ch + 1) (Cp + 2 * Cn + 10) j' δ' * k2e large₂ CH (Ch + 1) (Cp + 2 * Cn + 10) j'' δ'') := by
        have s1 := exponent_weight_absorb large₂ (CH := CH) (Cp := Cp) hCh hr Cn j' δ'
        have s2 := exponent_weight_absorb large₂ (CH := CH) (Cp := Cp) hCh hr Cn j'' δ''
        rw [← hS'] at s1
        rw [← hS''] at s2
        have n1 : 0 ≤ 2 * k2e large₂ CH Ch Cp j' δ' * S' ^ ((2 * Cn + 10) * D.R.k) :=
          mul_nonneg (mul_nonneg zero_le_two (amplitude_exponent_nonneg large₂ hCh _ _)) (by positivity)
        have n2 : 0 ≤ 2 * k2e large₂ CH Ch Cp j'' δ'' * S'' ^ ((2 * Cn + 10) * D.R.k) :=
          mul_nonneg (mul_nonneg zero_le_two (amplitude_exponent_nonneg large₂ hCh _ _)) (by positivity)
        have s3 := mul_le_mul s1 s2 n2 (amplitude_exponent_nonneg large₂ hCh1 _ _)
        have hpos : 0 ≤ E0 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k) := mul_nonneg hE00 (by positivity)
        have s4 : E0 * (3 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k)) ≤
            (2 * k2e large₂ CH Ch Cp j' δ' * S' ^ ((2 * Cn + 10) * D.R.k)) * (2 * k2e large₂ CH Ch Cp j'' δ'' * S'' ^ ((2 * Cn + 10) * D.R.k)) := by
          have : (2 * k2e large₂ CH Ch Cp j' δ' * S' ^ ((2 * Cn + 10) * D.R.k)) * (2 * k2e large₂ CH Ch Cp j'' δ'' * S'' ^ ((2 * Cn + 10) * D.R.k)) =
              4 * (E0 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k)) := by rw [hE0, mul_pow]; ring
          rw [this]; linarith
        calc M * E0 * (3 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k)) = M * (E0 * (3 * (S' * S'') ^ ((2 * Cn + 10) * D.R.k))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_trans s4 s3) hM

def CorankRemainder (C' Cl Cg cb Cu cT CT C0 CH Cs ComplexParameterFamilyContinuity C4 Ch Cp Cc : ℝ) (Cn : ℕ) : Prop :=
  (∀ u, MinorCosetSum large₂ X u CH Cc) ∧
  ∀ u : D.what₂.Word, ∃ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (LatV D)),
    F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧
    ∀ om : ∀ u : D.what₂.Word, D.s.Term u u → ℝ, (∀ u t, 0 < om u t) → LatticeIndexAndWeightTheory.TieOK X u → LatticeIndexAndWeightTheory.T2 D large₂ X om CH Cs ComplexParameterFamilyContinuity →
      LatticeIndexAndWeightTheory.LatticeIndicesFiniteBound D X → LatticeIndexAndWeightTheory.TermWeightSumAboveBound D large₂ X om ComplexParameterFamilyContinuity →
      LatticeIndexAndWeightTheory.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 C4 → LatticeIndexAndWeightTheory.adm5 → PairsOfCorank large₂ X om u (massRows D F0 what₂) CH Ch Cp ComplexParameterFamilyContinuity Cn


end PairsS

section Fam

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))







end Fam

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section NGa

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

open MeasureTheory in

theorem ng_scale (hOK : M.OK) (x : Eˣ) :
    ∃ c : NNReal, ∀ s : Set E, IsOpen s → M.mu ((fun y => (x : E) * y) '' s) = c * M.mu s := by
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  have := hOK.borel
  have := hOK.haar.haar
  obtain ⟨hO, hC, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top M.L
  have hlc : LocallyCompactSpace E :=
    hC.locallyCompactSpace_of_mem_nhds_of_addGroup (hO.mem_nhds M.L.O.zero_mem)
  let e : E ≃+ E := AddAut.mulLeft (x⁻¹)
  have he : ∀ y, e y = ((x⁻¹ : Eˣ) : E) * y := fun y => rfl
  have hes : ∀ y, e.symm y = (x : E) * y := by
    intro y
    apply e.injective
    rw [AddEquiv.apply_symm_apply, he, ← mul_assoc, Units.inv_mul, one_mul]
  have hc1 : Continuous e := by
    have : (e : E → E) = fun y => ((x⁻¹ : Eˣ) : E) * y := funext he
    rw [this]; fun_prop
  have hc2 : Continuous e.symm := by
    have : (e.symm : E → E) = fun y => (x : E) * y := funext hes
    rw [this]; fun_prop
  have hH : (Measure.map e M.mu).IsAddHaarMeasure := e.isAddHaarMeasure_map M.mu hc1 hc2
  refine ⟨(Measure.map e M.mu).addHaarScalarFactor M.mu, fun s hs => ?_⟩
  have h1 := Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen (Measure.map e M.mu) M.mu hs
  rw [Measure.map_apply hc1.measurable hs.measurableSet] at h1
  have h2 : e ⁻¹' s = (fun y => (x : E) * y) '' s := by
    ext y
    constructor
    · intro hy
      exact ⟨e y, hy, by show (x : E) * e y = y; rw [he, ← mul_assoc, Units.mul_inv, one_mul]⟩
    · rintro ⟨z, hz, rfl⟩
      show e ((x : E) * z) ∈ s
      rw [he, ← mul_assoc, Units.inv_mul, one_mul]; exact hz
  rw [h2] at h1
  rw [h1]; rfl

theorem ng_modK (hOK : M.OK) {x : E} (hx : IsUnit x) : 0 < M.modK x ∧ (x ∈ M.L.O → M.modK x ≤ 1) := by
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  have := hOK.borel
  have := hOK.haar.haar
  obtain ⟨hO, hC, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top M.L
  obtain ⟨hRo, hRc, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.R_top M hOK
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨c, hc⟩ := ng_scale hOK u
  have hm : M.modK (u : E) = c := by
    unfold Model.modK
    rw [hc _ hRo, hOK.haar.volR, mul_one]; rfl
  have hOpos : 0 < M.mu (M.L.O : Set E) := hO.measure_pos M.mu ⟨0, M.L.O.zero_mem⟩
  have hOfin : M.mu (M.L.O : Set E) < ⊤ := hC.measure_lt_top
  constructor
  · rw [hm]
    have h1 : IsOpen ((fun y => (u : E) * y) '' (M.L.O : Set E)) := by
      have : (fun y => (u : E) * y) '' (M.L.O : Set E) = (fun y => ((u⁻¹ : Eˣ) : E) * y) ⁻¹' (M.L.O : Set E) := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          show ((u⁻¹ : Eˣ) : E) * ((u : E) * z) ∈ M.L.O
          rw [← mul_assoc, Units.inv_mul, one_mul]; exact hz
        · intro hy
          exact ⟨_, hy, by show (u : E) * (((u⁻¹ : Eˣ) : E) * y) = y; rw [← mul_assoc, Units.mul_inv, one_mul]⟩
      rw [this]
      exact hO.preimage (by fun_prop)
    have h2 : 0 < M.mu ((fun y => (u : E) * y) '' (M.L.O : Set E)) :=
      h1.measure_pos M.mu ⟨(u : E) * 0, 0, M.L.O.zero_mem, rfl⟩
    rw [hc _ hO] at h2
    have h3 : (c : ENNReal) ≠ 0 := fun h => by rw [h, zero_mul] at h2; exact lt_irrefl _ h2
    have h4 : c ≠ 0 := fun h => h3 (by rw [h]; rfl)
    exact_mod_cast pos_iff_ne_zero.2 h4
  · intro hx
    rw [hm]
    have h1 : (fun y => (u : E) * y) '' (M.L.O : Set E) ⊆ (M.L.O : Set E) := by
      rintro _ ⟨z, hz, rfl⟩
      exact M.L.O.mul_mem hx hz
    have h2 := MeasureTheory.measure_mono (μ := M.mu) h1
    rw [hc _ hO] at h2
    by_contra hlt
    push Not at hlt
    have h3 : (1 : ENNReal) < c := by exact_mod_cast hlt
    have h4 : M.mu (M.L.O : Set E) < c * M.mu (M.L.O : Set E) := by
      calc M.mu (M.L.O : Set E) = 1 * M.mu (M.L.O : Set E) := (one_mul _).symm
        _ < c * M.mu (M.L.O : Set E) := ENNReal.mul_lt_mul_left hOpos.ne' hOfin.ne h3
    exact absurd h2 (not_le.2 h4)

theorem norm_basic_character_eq_one (hOK : M.OK) (x : E) : ‖M.L.psi0 x‖ = 1 := by
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  obtain ⟨-, hC, hU⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top M.L
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hπ0 : (π : F) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)

  have key : ∀ y : E, ‖M.L.psi0 y‖ ≤ 1 := by
    intro y
    obtain ⟨m, hm⟩ := hU π hπ y
    have hm := hm m le_rfl
    set u : E := algebraMap F E ((π : F)⁻¹) ^ m with hu
    have huπ : u * algebraMap F E π ^ m = 1 := by
      rw [hu, ← mul_pow, ← map_mul, inv_mul_cancel₀ hπ0, map_one, one_pow]
    have hK : IsCompact ((fun z => u * z) '' (M.L.O : Set E)) := hC.image (by fun_prop)
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun z => M.L.psi0 z) M.L.local_additive_char_continuous.continuousOn
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hlt
    have hmem : (n : ℕ) • y ∈ (fun z => u * z) '' (M.L.O : Set E) := by
      refine ⟨n • (algebraMap F E π ^ m * y), M.L.O.nsmul_mem hm n, ?_⟩
      show u * (n • (algebraMap F E π ^ m * y)) = n • y
      rw [mul_smul_comm, ← mul_assoc, huπ, one_mul]
    have h1 := hB _ hmem
    rw [AddChar.map_nsmul_eq_pow, norm_pow] at h1
    exact absurd h1 (not_le.2 hn)
  have h1 := key x
  have h2 := key (-x)
  have h3 : M.L.psi0 x * M.L.psi0 (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h4 : ‖M.L.psi0 x‖ * ‖M.L.psi0 (-x)‖ = 1 := by rw [← norm_mul, h3, norm_one]
  have h5 : 0 ≤ ‖M.L.psi0 x‖ := norm_nonneg _
  nlinarith

theorem two_le_residue_card (hOK : M.OK) : 2 ≤ qF F := by
  have := hOK.loc
  unfold qF
  have : Finite 𝓀[F] := inferInstance
  exact Finite.one_lt_card

open MeasureTheory in
theorem ng_modK_nonunit (hOK : M.OK) (a : 𝒪[F]) (ha0 : (a : F) ≠ 0) (hau : ¬ IsUnit a) :
    M.modK (algebraMap F E a) ≤ (((qF F : ℝ)) ^ 2)⁻¹ := by
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  have := hOK.borel
  have := hOK.haar.haar
  have hnt := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
  obtain ⟨hO, hC, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top M.L
  obtain ⟨hRo, hRc, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.R_top M hOK
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  obtain ⟨θ, hθO, hθc, D, hD0, hD⟩ := Formalism.MainNotions.LocalModelPeriodLattices.exists_theta M.L
  have hua : IsUnit (algebraMap F E (a : F)) := ha0.isUnit.map _
  obtain ⟨u, hu⟩ := hua
  obtain ⟨c, hc⟩ := ng_scale hOK u
  have hm : M.modK (algebraMap F E (a : F)) = c := by
    unfold Model.modK
    rw [← hu, hc _ hRo, hOK.haar.volR, mul_one]; rfl

  let OO : AddSubgroup E := M.L.O.toAddSubgroup
  let am : E →+ E := AddMonoidHom.mulLeft (algebraMap F E (a : F))
  have ham : Function.Injective am := by
    intro x y hxy
    have h1 : (u : E) * x = (u : E) * y := by rw [hu]; exact hxy
    exact u.isUnit.mul_left_cancel h1
  let ψ : 𝒪[F] × 𝒪[F] →+ E :=
    { toFun := fun p => algebraMap F E (p.1 : F) + algebraMap F E (p.2 : F) * θ
      map_zero' := by simp
      map_add' := by
        intro p p'
        simp only [Prod.fst_add, Prod.snd_add, Subring.coe_add, map_add]
        ring }
  have hψ : ∀ p, ψ p = algebraMap F E (p.1 : F) + algebraMap F E (p.2 : F) * θ := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ h0
    rw [hψ] at h0
    simp only at h0
    have h1 : algebraMap F E (x : F) - algebraMap F E (y : F) * θ = 0 := by
      have := congrArg M.L.cj h0
      rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hθc, map_zero] at this
      rw [← this]; ring
    have h2 : algebraMap F E (2 * (x : F)) = 0 := by
      rw [map_mul, map_ofNat]
      linear_combination h0 + h1
    have hx : (x : F) = 0 := by
      have := hinj (h2.trans (map_zero _).symm)
      simpa using this
    have h3 : algebraMap F E ((y : F) * (D : F)) = 0 := by
      rw [map_mul, ← hD]
      have h4 : algebraMap F E (y : F) * θ = 0 := by rw [hx, map_zero, zero_add] at h0; exact h0
      rw [← mul_assoc, h4, zero_mul]
    have hy : (y : F) = 0 := by
      have := hinj (h3.trans (map_zero _).symm)
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hD0
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  let A' : AddSubgroup E := (⊤ : AddSubgroup (𝒪[F] × 𝒪[F])).map ψ
  let J : AddSubgroup 𝒪[F] := (Ideal.span {a}).toAddSubgroup
  have hA'O : A' ≤ OO := by
    rintro _ ⟨p, -, rfl⟩
    exact M.L.O.add_mem (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L p.1)
      (M.L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L p.2) hθO)

  have h2D : (2 * (D : F)) ≠ 0 := mul_ne_zero two_ne_zero hD0
  obtain ⟨w, hw⟩ := (h2D.isUnit.map (algebraMap F E))
  have hsub : (fun y => (w : E) * y) '' (M.L.O : Set E) ⊆ (A' : Set E) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, c', ht, hc', he⟩ := Formalism.MainNotions.LocalModelPeriodLattices.decomp M.L θ hθc D hD x
    have htO : t ∈ 𝒪[F] := Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L t (by
      rw [ht]; exact M.L.O.add_mem hx (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ hx))
    have hcO : c' ∈ 𝒪[F] := Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L c' (by
      rw [hc']; exact M.L.O.mul_mem (M.L.O.sub_mem hx (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ hx)) hθO)
    refine ⟨(D * ⟨t, htO⟩, ⟨c', hcO⟩), trivial, ?_⟩
    show algebraMap F E ((D : F) * t) + algebraMap F E c' * θ = (w : E) * x
    rw [hw, he]
  have hwo : IsOpen ((fun y => (w : E) * y) '' (M.L.O : Set E)) := by
    have : (fun y => (w : E) * y) '' (M.L.O : Set E) = (fun y => ((w⁻¹ : Eˣ) : E) * y) ⁻¹' (M.L.O : Set E) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show ((w⁻¹ : Eˣ) : E) * ((w : E) * z) ∈ M.L.O
        rw [← mul_assoc, Units.inv_mul, one_mul]; exact hz
      · intro hy
        exact ⟨_, hy, by show (w : E) * (((w⁻¹ : Eˣ) : E) * y) = y; rw [← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [this]
    exact hO.preimage (by fun_prop)
  have hA'o : IsOpen (A' : Set E) :=
    AddSubgroup.isOpen_of_mem_nhds A' (Filter.mem_of_superset (hwo.mem_nhds ⟨0, M.L.O.zero_mem, mul_zero _⟩) hsub)
  have hOOc : IsCompact (OO : Set E) := hC
  have hidx1 := (Formalism.MainNotions.LocalModelPeriodLattices.measure_eq_relIndex_mul M.mu A' OO hA'O hA'o hOOc).1

  have haO : OO.map am ≤ OO := by
    rintro _ ⟨x, hx, rfl⟩
    exact M.L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L a) hx
  have hset : ((OO.map am : AddSubgroup E) : Set E) = (fun y => (u : E) * y) '' (M.L.O : Set E) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [hu]; rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [hu]; rfl⟩
  have haOo : IsOpen ((OO.map am : AddSubgroup E) : Set E) := by
    rw [hset]
    have : (fun y => (u : E) * y) '' (M.L.O : Set E) = (fun y => ((u⁻¹ : Eˣ) : E) * y) ⁻¹' (M.L.O : Set E) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show ((u⁻¹ : Eˣ) : E) * ((u : E) * z) ∈ M.L.O
        rw [← mul_assoc, Units.inv_mul, one_mul]; exact hz
      · intro hy
        exact ⟨_, hy, by show (u : E) * (((u⁻¹ : Eˣ) : E) * y) = y; rw [← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [this]
    exact hO.preimage (by fun_prop)
  obtain ⟨hN0, hN⟩ := Formalism.MainNotions.LocalModelPeriodLattices.measure_eq_relIndex_mul M.mu (OO.map am) OO haO haOo hOOc

  have hmap : A'.map am = (J.prod J).map ψ := by
    ext z
    constructor
    · rintro ⟨_, ⟨p, -, rfl⟩, rfl⟩
      refine ⟨(a * p.1, a * p.2), ⟨Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a),
        Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)⟩, ?_⟩
      show algebraMap F E ((a : F) * (p.1 : F)) + algebraMap F E ((a : F) * (p.2 : F)) * θ =
        algebraMap F E (a : F) * (algebraMap F E (p.1 : F) + algebraMap F E (p.2 : F) * θ)
      rw [map_mul, map_mul]; ring
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      obtain ⟨x1, hx1⟩ := Ideal.mem_span_singleton'.1 hx
      obtain ⟨y1, hy1⟩ := Ideal.mem_span_singleton'.1 hy
      refine ⟨ψ (x1, y1), ⟨(x1, y1), trivial, rfl⟩, ?_⟩
      show algebraMap F E (a : F) * (algebraMap F E (x1 : F) + algebraMap F E (y1 : F) * θ) =
        algebraMap F E (x : F) + algebraMap F E (y : F) * θ
      have hx2 : (x : F) = (x1 : F) * (a : F) := by rw [← Subring.coe_mul]; exact congrArg Subtype.val hx1.symm
      have hy2 : (y : F) = (y1 : F) * (a : F) := by rw [← Subring.coe_mul]; exact congrArg Subtype.val hy1.symm
      rw [hx2, hy2, map_mul, map_mul]
      ring
  have e1 : (A'.map am).relIndex (OO.map am) = A'.relIndex OO :=
    AddSubgroup.relIndex_map_map_of_injective A' OO ham
  have e2 : (A'.map am).relIndex A' = J.index * J.index := by
    rw [hmap, AddSubgroup.relIndex_map_map_of_injective (J.prod J) ⊤ hψinj, AddSubgroup.relIndex_top_right,
      AddSubgroup.index_prod]
  have hle1 : A'.map am ≤ OO.map am := AddSubgroup.map_mono hA'O
  have hle2 : A'.map am ≤ A' := by
    rw [hmap]; exact AddSubgroup.map_mono le_top
  have e3 := AddSubgroup.relIndex_mul_relIndex (A'.map am) (OO.map am) OO hle1 haO
  have e4 := AddSubgroup.relIndex_mul_relIndex (A'.map am) A' OO hle2 hA'O
  have e5 : (OO.map am).relIndex OO = J.index * J.index := by
    rw [e1] at e3
    rw [e2] at e4
    have : A'.relIndex OO * (OO.map am).relIndex OO = A'.relIndex OO * (J.index * J.index) := by
      rw [e3, ← e4, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hidx1) this
  have hJ0 : J.index ≠ 0 := fun h => hN0 (by rw [e5, h, zero_mul])
  have hJm : J ≤ (IsLocalRing.maximalIdeal 𝒪[F]).toAddSubgroup := by
    intro x hx
    have h1 : Ideal.span {a} ≤ IsLocalRing.maximalIdeal 𝒪[F] := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact (IsLocalRing.mem_maximalIdeal a).2 hau
    exact h1 hx
  have hq : qF F ≤ J.index := by
    have h1 : (IsLocalRing.maximalIdeal 𝒪[F]).toAddSubgroup.index ∣ J.index := AddSubgroup.index_dvd_of_le hJm
    have h2 : (IsLocalRing.maximalIdeal 𝒪[F]).toAddSubgroup.index = qF F := rfl
    rw [h2] at h1
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hJ0) h1

  have hpos : 0 < M.mu ((OO.map am : AddSubgroup E) : Set E) := haOo.measure_pos M.mu ⟨0, (OO.map am).zero_mem⟩
  have hfin : M.mu ((OO.map am : AddSubgroup E) : Set E) < ⊤ :=
    lt_of_le_of_lt (measure_mono haO) hC.measure_lt_top
  have h7 : M.mu ((OO.map am : AddSubgroup E) : Set E) = c * M.mu (M.L.O : Set E) := by rw [hset, hc _ hO]
  have h8 : (c : ENNReal) * ((OO.map am).relIndex OO : ENNReal) = 1 := by
    have h9 : M.mu ((OO.map am : AddSubgroup E) : Set E) =
        (c * ((OO.map am).relIndex OO : ENNReal)) * M.mu ((OO.map am : AddSubgroup E) : Set E) := by
      conv_lhs => rw [h7]
      have : M.mu (M.L.O : Set E) = M.mu (OO : Set E) := rfl
      rw [this, hN, mul_assoc]
    have h10 : (1 : ENNReal) * M.mu ((OO.map am : AddSubgroup E) : Set E) =
        (c * ((OO.map am).relIndex OO : ENNReal)) * M.mu ((OO.map am : AddSubgroup E) : Set E) := by
      rw [one_mul]; exact h9
    exact ((ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h10).symm
  have h11 : (c : ℝ) * ((OO.map am).relIndex OO : ℝ) = 1 := by
    have := congrArg ENNReal.toReal h8
    simpa using this
  rw [hm]
  have hNq : ((qF F : ℝ)) ^ 2 ≤ ((OO.map am).relIndex OO : ℝ) := by
    rw [e5]; push_cast
    have : (qF F : ℝ) ≤ (J.index : ℝ) := by exact_mod_cast hq
    nlinarith [Nat.cast_nonneg (α := ℝ) (qF F)]
  have hq0 : (0 : ℝ) < (qF F : ℝ) ^ 2 := by
    have := two_le_residue_card hOK
    positivity
  rw [le_inv_comm₀ (by
    rcases (NNReal.coe_nonneg c).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at h11; exact absurd h11 zero_ne_one) hq0]
  have : ((c : ℝ))⁻¹ = ((OO.map am).relIndex OO : ℝ) := by
    exact inv_eq_of_mul_eq_one_right h11
  rw [this]; exact hNq

theorem ng_sum_castLE {n l : ℕ} (hl : l ≤ n) (g : Fin n → E) (hg : ∀ i : Fin n, l ≤ i.val → g i = 0) :
    ∑ i, g i = ∑ j : Fin l, g (Fin.castLE hl j) := by
  classical
  have h1 : ∑ j : Fin l, g (Fin.castLE hl j) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb hl), g i := by
    rw [Finset.sum_map]; rfl
  rw [h1]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply hg
  by_contra h
  push Not at h
  exact hi (Finset.mem_map.2 ⟨⟨i.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem ng_minor {n l : ℕ} (hl : l ≤ n) (Lo Z Up : Matrix (Fin n) (Fin n) E)
    (hLo : ∀ a d, a < d → Lo a d = 0) (hLo1 : ∀ a, Lo a a = 1)
    (hUp : ∀ c b, b < c → Up c b = 0) (hUp1 : ∀ a, Up a a = 1) :
    ((Lo * Z * Up).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have hsub : (Lo * Z * Up).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Lo.submatrix (Fin.castLE hl) (Fin.castLE hl) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Up.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [ng_sum_castLE hl _ (fun e he => by
      rw [hUp e (Fin.castLE hl b) (by
        rw [Fin.lt_def]; exact lt_of_lt_of_le b.2 he), mul_zero])]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [ng_sum_castLE hl _ (fun d hd => by
      rw [hLo (Fin.castLE hl a) d (by
        rw [Fin.lt_def]; exact lt_of_lt_of_le a.2 hd), zero_mul])]
  have hT1 : (Lo.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have h' : i < j := hij
    exact hLo _ _ (by rw [Fin.lt_def]; exact h')
  have hT2 : (Up.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id := by
    intro i j hij
    have h' : j < i := hij
    exact hUp _ _ (by rw [Fin.lt_def]; exact h')
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ hT1,
    Matrix.det_of_isUpperTriangular hT2]
  simp [hLo1, hUp1]

variable {H : HermSp M V} {r : ℕ}

theorem ng_Dl_term {P : FPair H r} {n n' : V ≃ₗ[E] V} (hn : n ∈ P.A.NSet) (hn' : n' ∈ P.B.NSet) (l : ℕ) :
    H.Dl (fun b => n (P.A.f b)) (fun b => n' (P.B.f b)) l = P.Dm l := by
  choose A h1 h2 h3 using N_row P.A hn
  choose B k1 k2 k3 using N_row P.B hn'
  unfold FPair.Dm HermSp.Dl
  by_cases hl : l ≤ r + 1
  · rw [dif_pos hl, dif_pos hl]
    have e : H.Zhat (fun b => n (P.A.f b)) (fun b => n' (P.B.f b)) =
        (Matrix.of fun a d => M.L.cj (A a d)) * H.Zhat P.A.f P.B.f * (Matrix.of fun c b => B b c) := by
      ext a b
      simp only [HermSp.Zhat, Matrix.of_apply, Matrix.mul_apply]
      rw [h3 a, k3 b, h_sum_left]
      simp only [h_sum_right]
      exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)
    rw [e]
    exact ng_minor hl _ _ _ (fun a d had => by simp [h1 a d had]) (fun a => by simp [h2 a])
      (fun c b hbc => by simp [k1 b c hbc]) (fun a => by simp [k2 a])
  · rw [dif_neg hl, dif_neg hl]

section Std

variable {Fr : FrameD H r} {L : Submodule M.L.O (H.Wb Fr.f)}

theorem ng_h_es_e (i b : Fin r) : H.h (Fr.es i) (Fr.e b) = if b = i then 1 else 0 := by
  show H.h (Fr.es i) (Fr.f b.castSucc) = _
  rw [H.h_herm (Fr.f b.castSucc) (Fr.es i), Fr.h_es]
  split_ifs <;> simp

theorem ng_prF_e (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.e b) = 0 := by
  classical
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  have z1 : ∑ i, H.h v (Fr.es i) * H.h (Fr.e i) (Fr.e b) = 0 :=
    Finset.sum_eq_zero (fun i _ => by
      rw [show H.h (Fr.e i) (Fr.e b) = 0 from Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last i).ne), mul_zero])
  have z2 : ∑ i, H.h v (Fr.e i) * H.h (Fr.es i) (Fr.e b) = H.h v (Fr.e b) := by
    rw [Finset.sum_eq_single b]
    · rw [ng_h_es_e, if_pos rfl, mul_one]
    · intro i _ hi; rw [ng_h_es_e, if_neg (Ne.symm hi), mul_zero]
    · intro h; exact absurd (Finset.mem_univ b) h
  rw [z1, z2]; ring

theorem ng_prF_es (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.es b) = 0 := by
  classical
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  have z1 : ∑ i, H.h v (Fr.es i) * H.h (Fr.e i) (Fr.es b) = H.h v (Fr.es b) := by
    rw [Finset.sum_eq_single b]
    · rw [show H.h (Fr.e b) (Fr.es b) = 1 from by have := Fr.h_es b b; rwa [if_pos rfl] at this, mul_one]
    · intro i _ hi
      rw [show H.h (Fr.e i) (Fr.es b) = 0 from by have := Fr.h_es i b; rwa [if_neg hi] at this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ b) h
  have z2 : ∑ i, H.h v (Fr.e i) * H.h (Fr.es i) (Fr.es b) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [Fr.h_ss, mul_zero])
  rw [z1, z2]; ring

theorem ng_expand (v y : V) : H.h v y = ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) y + H.h (Fr.prF v) y +
    ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) y := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]; ring

theorem ng_prF_prF (v w : V) : H.h (Fr.prF v) w = H.h (Fr.prF v) (Fr.prF w) := by
  rw [H.h_herm w (Fr.prF v), ng_expand (Fr := Fr) w (Fr.prF v)]
  have z1 : ∑ a, H.h w (Fr.es a) * H.h (Fr.e a) (Fr.prF v) = 0 :=
    Finset.sum_eq_zero (fun a _ => by rw [H.h_herm (Fr.prF v) (Fr.e a), ng_prF_e, map_zero, mul_zero])
  have z2 : ∑ a, H.h w (Fr.e a) * H.h (Fr.es a) (Fr.prF v) = 0 :=
    Finset.sum_eq_zero (fun a _ => by rw [H.h_herm (Fr.prF v) (Fr.es a), ng_prF_es, map_zero, mul_zero])
  rw [z1, z2, zero_add, add_zero, ← H.h_herm]

theorem ng_gen_int (hL : Fr.IsInner L) {v w : V}
    (hv : (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
      ∃ x : ↥(H.perp (H.X Fr.f)), (x : V) = Fr.prF v ∧ H.mkW Fr.f x ∈ L)
    (hw : (∀ a, H.h w (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h w (Fr.e a) ∈ M.L.O) ∧
      ∃ x : ↥(H.perp (H.X Fr.f)), (x : V) = Fr.prF w ∧ H.mkW Fr.f x ∈ L) : H.h v w ∈ M.L.O := by
  obtain ⟨v1, v2, x, hx, hxL⟩ := hv
  obtain ⟨w1, w2, y, hy, hyL⟩ := hw
  rw [ng_expand (Fr := Fr) v w, ng_prF_prF]
  refine M.L.O.add_mem (M.L.O.add_mem (M.L.O.sum_mem fun a _ => M.L.O.mul_mem (v1 a) ?_) ?_)
    (M.L.O.sum_mem fun a _ => M.L.O.mul_mem (v2 a) ?_)
  · rw [H.h_herm w (Fr.e a)]; exact Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (w2 a)
  · rw [← hx, ← hy]; exact (hL.2.1 x).1 hxL y hyL
  · rw [H.h_herm w (Fr.es a)]; exact Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (w1 a)

theorem ng_LamStd_int (hL : Fr.IsInner L) {v w : V} (hv : v ∈ Fr.LamStd L) (hw : w ∈ Fr.LamStd L) :
    H.h v w ∈ M.L.O := by
  have step : ∀ w', ((∀ a, H.h w' (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h w' (Fr.e a) ∈ M.L.O) ∧
      ∃ x : ↥(H.perp (H.X Fr.f)), (x : V) = Fr.prF w' ∧ H.mkW Fr.f x ∈ L) →
      ∀ v', v' ∈ Fr.LamStd L → H.h v' w' ∈ M.L.O := by
    intro w' hw' v' hv'
    unfold FrameD.LamStd at hv'
    induction hv' using Submodule.span_induction with
    | mem v hv => exact ng_gen_int hL hv hw'
    | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
    | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
    | smul c x _ hx =>
      have : H.h (c • x) w' = (c : E) * H.h x w' := H.h_smul_left (c : E) x _
      rw [this]; exact M.L.O.mul_mem c.2 hx
  rw [H.h_herm w v]
  apply Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O
  unfold FrameD.LamStd at hw
  induction hw using Submodule.span_induction with
  | mem w hw => rw [H.h_herm v w]; exact Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (step w hw v hv)
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
  | smul c x _ hx =>
    have : H.h (c • x) v = (c : E) * H.h x v := H.h_smul_left (c : E) x _
    rw [this]; exact M.L.O.mul_mem c.2 hx

end Std

theorem ng_norm_om {P : FPair H r} (hOK : M.OK) (t : Term V M r) : ‖om P t‖ = 1 := by
  unfold om FrameD.psiOf
  rw [norm_mul, norm_inv, norm_basic_character_eq_one hOK, norm_basic_character_eq_one hOK]
  simp

theorem ng_gram_base (P : FPair H r) : (H.gram (Sum.elim P.A.f P.B.f)).det = (-1) ^ (r + 1) * P.Gv := by
  set c : E →+* E := (M.L.cj : E ≃ₐ[F] E).toAlgHom.toRingHom with hc
  have hcx : ∀ x, c x = M.L.cj x := fun _ => rfl
  set Zh := H.Zhat P.A.f P.B.f with hZh
  have hG : H.gram (Sum.elim P.A.f P.B.f) =
      Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -(algebraMap F E P.A.T) else 0) Zh
        (Zh.transpose.map c) (Matrix.diagonal fun i => if i = Fin.last r then -(algebraMap F E P.B.T) else 0) := by
    ext i j
    rcases i with a | a <;> rcases j with b | b
    · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab
        by_cases ha : a = Fin.last r
        · subst ha; simp [P.A.h_zz]
        · simp [ha, P.A.h_iso a a (Or.inl ha)]
      · rw [if_neg hab]
        by_cases ha : a = Fin.last r
        · exact P.A.h_iso b a (Or.inl (fun h => hab (by rw [ha, h])))
        · exact P.A.h_iso b a (Or.inr ha)
    · simp [HermSp.gram, hZh, HermSp.Zhat]
    · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁, Matrix.map_apply,
        Matrix.transpose_apply, hZh, HermSp.Zhat, hcx]
      exact H.h_herm _ _
    · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab
        by_cases ha : a = Fin.last r
        · subst ha; simp [P.B.h_zz]
        · simp [ha, P.B.h_iso a a (Or.inl ha)]
      · rw [if_neg hab]
        by_cases ha : a = Fin.last r
        · exact P.B.h_iso b a (Or.inl (fun h => hab (by rw [ha, h])))
        · exact P.B.h_iso b a (Or.inr ha)
  rw [hG, Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.gramDetGen E r (Zh.transpose.map c) Zh]
  have d1 : (Zh.transpose.map c).det = M.L.cj Zh.det := by
    rw [← hcx, RingHom.map_det, ← Matrix.det_transpose]
    rfl
  have d2 : ((Zh.transpose.map c).submatrix Fin.castSucc Fin.castSucc).det =
      M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [← hcx, RingHom.map_det, ← Matrix.det_transpose]
    rfl
  have e1 : P.Dm (r + 1) = Zh.det := by
    unfold FPair.Dm HermSp.Dl
    rw [dif_pos le_rfl]
    rfl
  have e2 : P.Dm r = (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    unfold FPair.Dm HermSp.Dl
    rw [dif_pos (Nat.le_succ r)]
    rfl
  rw [d1, d2]
  unfold FPair.Gv HermSp.Gdet HermSp.normE
  change _ = (-1) ^ (r + 1) * (P.Dm (r + 1) * M.L.cj (P.Dm (r + 1)) - algebraMap F E (P.A.T * P.B.T) * (P.Dm r * M.L.cj (P.Dm r)))
  rw [e1, e2, map_mul]
  ring

theorem ng_theta_mem (M : Model F E) : ∃ a : 𝒪[F], (a : F) = theta M ∧ (a : F) ≠ 0 := by
  unfold theta
  split
  · exact ⟨1, rfl, one_ne_zero⟩
  · rename_i g _
    exact ⟨g.q, rfl, fun h => g.q_irr.ne_zero (Subtype.ext h)⟩

theorem ng_gram_MM (t : Term V M r) :
    (H.gram (H.MMfam t)).det =
      algebraMap F E (((theta M)⁻¹) ^ (2 * (r + 1))) * (H.gram (Sum.elim t.f t.f')).det := by
  rcases hs : M.split with _ | g
  · have hm : H.MMfam t = Sum.elim t.f t.f' := by
      unfold HermSp.MMfam
      split
      · rfl
      · rename_i g hg
        rw [hs] at hg
        cases hg
    rw [hm, theta_eq_one hs]; simp
  · have hm : H.MMfam t = Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
      unfold HermSp.MMfam
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    have hθ : theta M = (g.q : F) := by
      unfold theta
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    set c : E := algebraMap F E ((g.q : F)⁻¹) with hc
    rw [hm, hθ, gram_det_change (Sum.elim t.f t.f') _
      (Matrix.fromBlocks 1 0 (-(c • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) (c • 1))]
    · rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, one_mul,
        mul_one, map_pow, hc, AlgEquiv.commutes, map_pow]
      ring
    · classical
      rintro (a | a)
      · simp [Fintype.sum_sum_type, Matrix.one_apply]
      · simp [Fintype.sum_sum_type, Matrix.one_apply, smul_sub]
        abel

theorem ng_smulLat {c c' : E} (hcc : c' * c = 1) {abelian₂ : Submodule M.L.O V} {x : V} (hx : x ∈ H.smulLat c abelian₂) :
    c' • x ∈ abelian₂ := by
  unfold HermSp.smulLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    show c' • c • v ∈ abelian₂
    rw [smul_smul, hcc, one_smul]; exact hv
  | zero => rw [smul_zero]; exact abelian₂.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact abelian₂.add_mem hx hy
  | smul o x _ hx =>
    have : c' • (o • x) = o • (c' • x) := by
      show c' • ((o : E) • x) = (o : E) • (c' • x)
      rw [smul_smul, smul_smul, mul_comm]
    rw [this]; exact abelian₂.smul_mem o hx

theorem ng_det_mem {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι E) (h : ∀ a b, G a b ∈ M.L.O) :
    G.det ∈ M.L.O := by
  let G₀ : Matrix ι ι M.L.O := fun a b => ⟨G a b, h a b⟩
  have hG₀ : G = G₀.map M.L.O.subtype := by ext a b; rfl
  rw [hG₀, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact G₀.det.2

variable {P : FPair H r}

theorem ng_term_int {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {v w : V} (hv : v ∈ t.abelian₂)
    (hw : w ∈ t.abelian₂) : H.h v w ∈ M.L.O := by
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, _, _⟩ := ht
  have hnU := (mem_NSet_of_mem_N P.A hn).1
  rw [hL] at hv hw
  obtain ⟨v0, hv0, rfl⟩ := hv
  obtain ⟨w0, hw0, rfl⟩ := hw
  show H.h (n v0) (n w0) ∈ _
  rw [hnU]
  exact ng_LamStd_int d.hL hv0 hw0

theorem ng_term_f {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) (b : Fin (r + 1)) :
    t.f b ∈ t.abelian₂ ∧ t.f' b ∈ t.abelian₂ := by
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  constructor
  · rw [hf, hL]; exact ⟨P.A.f b, f_mem_LamStd d.hL b, rfl⟩
  · rw [hf', hL']; exact ⟨P.B.f b, f_mem_LamStd d.hL' b, rfl⟩

theorem ng_term_MM {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.MMfam t j ∈ t.abelian₂ := by
  have hf := ng_term_f ht
  rcases hs : M.split with _ | g
  · have hm : H.MMfam t = Sum.elim t.f t.f' := by
      unfold HermSp.MMfam
      split
      · rfl
      · rename_i g hg
        rw [hs] at hg
        cases hg
    rw [hm]
    rcases j with b | b
    · exact (hf b).1
    · exact (hf b).2
  · have hm : H.MMfam t = Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
      unfold HermSp.MMfam
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    rw [hm]
    rcases j with b | b
    · exact (hf b).1
    · have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
      exact ng_smulLat (H := H) (by rw [← map_mul, inv_mul_cancel₀ hq, map_one]) ((ht.2.2.2.2 g hs).1 b)

theorem ng_term_gram {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) :
    (H.gram (H.MMfam t)).det = (H.gram P.MMgen).det := by
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  obtain ⟨A, hA, hA'⟩ := N_matrix P.A (mem_NSet_of_mem_N P.A hn)
  obtain ⟨B, hB, hB'⟩ := N_matrix P.B (mem_NSet_of_mem_N P.B hn')
  unfold FPair.MMgen
  rw [ng_gram_MM, ng_gram_MM]
  congr 1
  show _ = (H.gram (Sum.elim P.A.f P.B.f)).det
  rw [gram_det_change (Sum.elim P.A.f P.B.f) (Sum.elim t.f t.f') (Matrix.fromBlocks A 0 0 B)]
  · rw [Matrix.det_fromBlocks_zero₂₁, hA, hB]; simp
  · rintro (a | a)
    · simp [Fintype.sum_sum_type, hf, hA' a]
    · simp [Fintype.sum_sum_type, hf', hB' a]

theorem ng_term_Dm {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) (l : ℕ) : P.Dm l ∈ M.L.O := by
  have hint := fun v hv w hw => ng_term_int ht (v := v) (w := w) hv hw
  have hff := ng_term_f ht
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  rw [← ng_Dl_term (mem_NSet_of_mem_N P.A hn) (mem_NSet_of_mem_N P.B hn') l, ← hf, ← hf']
  unfold HermSp.Dl
  split_ifs with hl
  · exact ng_det_mem _ (fun a b => hint _ (hff _).2 _ (hff _).1)
  · exact M.L.O.zero_mem

theorem ng_G_unit (hG : P.Gv ≠ 0) : IsUnit P.Gv := by
  have hfix : M.L.cj P.Gv = P.Gv := by
    unfold FPair.Gv HermSp.Gdet HermSp.normE
    simp only [map_sub, map_mul, M.L.cj_cj, AlgEquiv.commutes]
    ring
  obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
  have ha0 : a ≠ 0 := fun h => hG (by rw [← ha, h, map_zero])
  rw [← ha]
  exact ha0.isUnit.map (algebraMap F E)

theorem ng_gramMM_unit (hG : P.Gv ≠ 0) : IsUnit (H.gram P.MMgen).det := by
  obtain ⟨a, ha, ha0⟩ := ng_theta_mem M
  unfold FPair.MMgen
  rw [ng_gram_MM]
  show IsUnit (_ * (H.gram (Sum.elim P.A.f P.B.f)).det)
  rw [ng_gram_base]
  refine IsUnit.mul (IsUnit.map (algebraMap F E) ?_) (IsUnit.mul (IsUnit.pow _ isUnit_one.neg) (ng_G_unit hG))
  rw [← ha]
  exact (pow_ne_zero _ (inv_ne_zero ha0)).isUnit

theorem ng_factors (hOK : M.OK) (hG : P.Gv ≠ 0) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) :
    (0 < M.modK (algebraMap F E (theta M)) ∧ M.modK (algebraMap F E (theta M)) ≤ 1) ∧
    (0 < M.modK (H.gram P.MMgen).det ∧ M.modK (H.gram P.MMgen).det ≤ 1) ∧
    (0 < ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) ∧
      ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, ha, ha0⟩ := ng_theta_mem M
    have h := ng_modK hOK (x := algebraMap F E (theta M)) (by rw [← ha]; exact ha0.isUnit.map _)
    exact ⟨h.1, h.2 (by rw [← ha]; exact Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L a)⟩
  · have h := ng_modK hOK (ng_gramMM_unit (P := P) hG)
    refine ⟨h.1, h.2 ?_⟩
    rw [← ng_term_gram ht]
    exact ng_det_mem _ (fun a b => ng_term_int ht (ng_term_MM ht _) (ng_term_MM ht _))
  · have hl : ∀ l ∈ P.ends, 0 < M.modK (P.Dm l * M.L.cj (P.Dm l)) ∧ M.modK (P.Dm l * M.L.cj (P.Dm l)) ≤ 1 := by
      intro l hl
      have hu : IsUnit (P.Dm l) := by
        unfold FPair.ends at hl
        exact (((@Finset.mem_filter _ _ (Classical.decPred _) _ _).1 hl).2).2
      have h := ng_modK hOK (hu.mul (hu.map M.L.cj))
      exact ⟨h.1, h.2 (M.L.O.mul_mem (ng_term_Dm ht l) (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l)))⟩
    exact ⟨Finset.prod_pos (fun l h => (hl l h).1),
      Finset.prod_le_one (fun l h => (hl l h).1.le) (fun l h => (hl l h).2)⟩

omit [TopologicalSpace E] [MeasurableSpace E] [CommRing E] in
theorem ng_real_one {a b c : ℝ} (a0 : 0 < a) (a1 : a ≤ 1) (b0 : 0 < b) (b1 : b ≤ 1) (c0 : 0 < c) (c1 : c ≤ 1) :
    1 ≤ (a * b * c) ^ (-(1 / 2 : ℝ)) := by
  refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) ?_ (by norm_num)
  calc a * b * c ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num


omit [TopologicalSpace E] [MeasurableSpace E] [CommRing E] in
theorem ng_real_q {a b c q : ℝ} (hq : 0 < q) (a0 : 0 < a) (a1 : a ≤ 1) (b0 : 0 < b) (b1 : b ≤ 1) (c0 : 0 < c) (c1 : c ≤ 1)
    (h : a ≤ (q ^ 2)⁻¹ ∨ b ≤ (q ^ 2)⁻¹) : q ≤ (a * b * c) ^ (-(1 / 2 : ℝ)) := by
  have hx : a * b * c ≤ (q ^ 2)⁻¹ := by
    rcases h with h | h
    · calc a * b * c ≤ a * 1 * 1 := by gcongr
        _ = a := by ring
        _ ≤ _ := h
    · calc a * b * c ≤ 1 * b * 1 := by gcongr
        _ = b := by ring
        _ ≤ _ := h
  have e : ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) = q := by
    rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv, ← Real.sqrt_eq_rpow, Real.sqrt_sq hq.le]
  calc q = ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) := e.symm
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hx (by norm_num)

theorem ng_q_le_Hp (hOK : M.OK) (hG : P.Gv ≠ 0) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t)
    (hB : BBne (H := H) t) : (qF F : ℝ) ≤ P.Hp := by
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, c0, c1⟩ := ng_factors hOK hG ht
  have hq : (0 : ℝ) < qF F := by
    have := two_le_residue_card hOK
    exact_mod_cast (by omega : 0 < qF F)
  have hnt := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
  unfold FPair.Hp
  refine ng_real_q hq a0 a1 b0 b1 c0 c1 ?_
  rcases hs : M.split with _ | g
  · right
    have hfix : M.L.cj P.Gv = P.Gv := by
      unfold FPair.Gv HermSp.Gdet HermSp.normE
      simp only [map_sub, map_mul, M.L.cj_cj, AlgEquiv.commutes]
      ring
    obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
    have hdet : (H.gram P.MMgen).det = algebraMap F E ((-1) ^ (r + 1) * a) := by
      rw [gram_det_eq P hs, ← ha, map_mul, map_pow, map_neg, map_one]
    have hmem : (H.gram P.MMgen).det ∈ M.L.O := by
      rw [← ng_term_gram ht]
      exact ng_det_mem _ (fun a b => ng_term_int ht (ng_term_MM ht _) (ng_term_MM ht _))
    have haO : (-1) ^ (r + 1) * a ∈ 𝒪[F] := Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (by rw [← hdet]; exact hmem)
    have ha0 : (-1) ^ (r + 1) * a ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (fun h => hG ?_)
      rw [← ha, h, map_zero]
    rw [hdet]
    refine ng_modK_nonunit hOK ⟨_, haO⟩ ha0 (fun hu => ?_)
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    refine not_BBne_of (ng_term_MM ht) (fun v hv j => ng_term_int ht hv (ng_term_MM ht j)) ?_ hB
    rw [ng_term_gram ht]
    refine ⟨hmem, algebraMap F E (y : F), Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L y, ?_⟩
    rw [hdet, ← map_mul]
    have : ((-1) ^ (r + 1) * a) * (y : F) = 1 := congrArg Subtype.val hy
    rw [this, map_one]
  · left
    have hθ : theta M = (g.q : F) := by
      unfold theta
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    rw [hθ]
    exact ng_modK_nonunit hOK g.q (fun h => g.q_irr.ne_zero (Subtype.ext h)) g.q_irr.not_isUnit

def NgOrth (P : FPair H r) (k : V) : Prop := (∀ b, H.h k (P.A.f b) = 0) ∧ ∀ b, H.h k (P.B.f b) = 0

theorem ng_frame_back (Fr : FrameD H r) {g : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet) (a : Fin (r + 1)) :
    ∃ row : Fin (r + 1) → E, Fr.f a = ∑ b, row b • g (Fr.f b) := by
  obtain ⟨row, -, -, h⟩ := N_row Fr (NSet_inv Fr hg) a
  refine ⟨row, ?_⟩
  have h1 : g ((g⁻¹ : V ≃ₗ[E] V) (Fr.f a)) = Fr.f a := LinearEquiv.apply_symm_apply g _
  rw [← h1, h, map_sum]
  exact Finset.sum_congr rfl (fun b _ => by rw [map_smul])

theorem ng_orth_back (Fr : FrameD H r) {g : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet) {k : V}
    (h : ∀ b, H.h k (g (Fr.f b)) = 0) (a : Fin (r + 1)) : H.h k (Fr.f a) = 0 := by
  obtain ⟨row, hrow⟩ := ng_frame_back Fr hg a
  rw [hrow, h_sum_right]
  exact Finset.sum_eq_zero (fun b _ => by rw [h b, mul_zero])

theorem ng_mulVec_gram {ι : Type} [Fintype ι] (m : ι → V) (c : ι → E) (j : ι) :
    ((H.gram m).mulVec c) j = H.h (∑ i, c i • m i) (m j) := by
  rw [h_sum_left]
  simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem ng_split {ι : Type} [Fintype ι] [DecidableEq ι] (abelian₂ : Submodule M.L.O V) (m : ι → V)
    (hmem : ∀ j, m j ∈ abelian₂) (hint : ∀ v ∈ abelian₂, ∀ j, H.h v (m j) ∈ M.L.O) (hu : IsUnitO M (H.gram m).det)
    (v : V) (hv : v ∈ abelian₂) :
    ∃ m0 ∈ Submodule.span M.L.O (Set.range m), v - m0 ∈ abelian₂ ∧ ∀ j, H.h (v - m0) (m j) = 0 := by
  set G := H.gram m with hG
  let G₀ : Matrix ι ι M.L.O := fun a b => ⟨G a b, hint (m b) (hmem b) a⟩
  have hG₀ : G = G₀.map M.L.O.subtype := by ext a b; rfl
  have hadj : ∀ a b, G.adjugate a b ∈ M.L.O := by
    intro a b
    rw [hG₀, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    exact (G₀.adjugate a b).2
  obtain ⟨_, y0, hy0, hdy⟩ := hu
  set y : ι → E := fun j => H.h v (m j) with hy
  set c : ι → E := y0 • G.adjugate.mulVec y with hc
  have hcO : ∀ i, c i ∈ M.L.O := by
    intro i
    simp only [hc, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact M.L.O.mul_mem hy0 (M.L.O.sum_mem (fun j _ => M.L.O.mul_mem (hadj i j) (hint v hv j)))
  have hGc : G.mulVec c = y := by
    rw [hc, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, mul_comm y0, hdy, one_smul]
  have hm0 : ∑ i, c i • m i ∈ Submodule.span M.L.O (Set.range m) := by
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have : c i • m i = (⟨c i, hcO i⟩ : M.L.O) • m i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨_, hm0, abelian₂.sub_mem hv ?_, fun j => ?_⟩
  · exact (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hmem j)) hm0
  · rw [h_sub_left, ← ng_mulVec_gram, ← hG, hGc]
    simp [hy]

theorem ng_zero {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → V) (hu : IsUnit (H.gram m).det) {u : V}
    (hsp : u ∈ Submodule.span E (Set.range m)) (ho : ∀ j, H.h u (m j) = 0) : u = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hsp
  have h0 : (H.gram m).mulVec c = 0 := by
    funext j
    rw [ng_mulVec_gram]; exact ho j
  have h1 : (H.gram m).det • c = 0 := by
    have e : (H.gram m).adjugate.mulVec ((H.gram m).mulVec c) = (H.gram m).det • c := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← e, h0, Matrix.mulVec_zero]
  have h2 : c = 0 := by
    funext i
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact (hu.mul_right_eq_zero).1 this
  rw [h2]; simp

theorem ng_MM_L (hs : M.split = none) (t : Term V M r) : H.MMfam t = Sum.elim t.f t.f' := by
  unfold HermSp.MMfam
  split
  · rfl
  · rename_i g hg
    rw [hs] at hg
    cases hg

theorem ng_term_split (hP : P.PrimeTo) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {v : V}
    (hv : v ∈ t.abelian₂) :
    ∃ m0 ∈ Submodule.span M.L.O (Set.range (Sum.elim t.f t.f')), v - m0 ∈ t.abelian₂ ∧ NgOrth P (v - m0) := by
  have hs := hP.1
  have hu : IsUnitO M (H.gram (Sum.elim t.f t.f')).det := by
    rw [← ng_MM_L hs t, ng_term_gram ht, gram_det_eq P hs]
    exact isUnitO_mul (isUnitO_neg_one_pow _) hP.2.1
  have hmem : ∀ j, Sum.elim t.f t.f' j ∈ t.abelian₂ := by rw [← ng_MM_L hs t]; exact ng_term_MM ht
  obtain ⟨m0, h1, h2, h3⟩ := ng_split t.abelian₂ _ hmem (fun v hv j => ng_term_int ht hv (hmem j)) hu v hv
  refine ⟨m0, h1, h2, ?_⟩
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  constructor
  · refine ng_orth_back P.A (mem_NSet_of_mem_N P.A hn) (fun b => ?_)
    have := h3 (Sum.inl b)
    rwa [Sum.elim_inl, hf] at this
  · refine ng_orth_back P.B (mem_NSet_of_mem_N P.B hn') (fun b => ?_)
    have := h3 (Sum.inr b)
    rwa [Sum.elim_inr, hf'] at this

theorem ng_span_base {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {x : V}
    (hx : x ∈ Submodule.span M.L.O (Set.range (Sum.elim t.f t.f'))) :
    x ∈ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)) := by
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rcases j with b | b
    · obtain ⟨row, -, -, h⟩ := N_row P.A (mem_NSet_of_mem_N P.A hn) b
      rw [Sum.elim_inl, hf]
      show n (P.A.f b) ∈ _
      rw [h]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
    · obtain ⟨row, -, -, h⟩ := N_row P.B (mem_NSet_of_mem_N P.B hn') b
      rw [Sum.elim_inr, hf']
      show n' (P.B.f b) ∈ _
      rw [h]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul o x _ hx => exact Submodule.smul_mem _ (o : E) hx


theorem ng_orth_perp (Fr : FrameD H r) {k : V} (h : ∀ b, H.h k (Fr.f b) = 0) : k ∈ H.perp (H.X Fr.f) := by
  intro x hx
  unfold HermSp.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h _
  | zero => rw [H.h_herm 0 _, H.h_zero_left, map_zero]
  | add x y _ _ hx hy => rw [H.h_herm (x + y) _, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_herm (c • x) _, H.h_smul_left, map_mul, ← H.h_herm, hx, mul_zero]



def NGOneClass (P : FPair H r) : Prop :=
  ∀ n₁ ∈ P.A.N, ∀ n₁' ∈ P.B.N, ∀ n₂ ∈ P.A.N, ∀ n₂' ∈ P.B.N,
    (∀ a b, H.h (n₁' (P.B.f b)) (n₁ (P.A.f a)) ∈ M.L.O) → (∀ a b, H.h (n₂' (P.B.f b)) (n₂ (P.A.f a)) ∈ M.L.O) →
    ∃ s ∈ P.St,
      Submodule.span M.L.O (Set.range fun b => s (n₁ (P.A.f b))) = Submodule.span M.L.O (Set.range fun b => n₂ (P.A.f b)) ∧
      Submodule.span M.L.O (Set.range fun b => s (n₁' (P.B.f b))) = Submodule.span M.L.O (Set.range fun b => n₂' (P.B.f b))

def NGMassOne (P : FPair H r) : Prop := ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → mu P t = 1



theorem ng_img_mul (g g' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * g') Λ = img g (img g' Λ) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨g' x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

theorem ng_img_one (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hv; exact ⟨v, hv, rfl⟩

theorem ng_img_inv {g : V ≃ₗ[E] V} {Λ Λ' : Submodule M.L.O V} (h : img g Λ = Λ') : img g⁻¹ Λ' = Λ := by
  rw [← h, ← ng_img_mul, inv_mul_cancel, ng_img_one]

theorem ng_img_mono (g : V ≃ₗ[E] V) {Λ Λ' : Submodule M.L.O V} (h : Λ ≤ Λ') : img g Λ ≤ img g Λ' :=
  Submodule.map_mono h

theorem ng_mem_Aut {g : V ≃ₗ[E] V} {Λ : Submodule M.L.O V} : g ∈ Aut Λ ↔ img g Λ = Λ := by
  constructor
  · intro hg
    unfold Aut at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ng_img_one Λ
    | mul x y _ _ hx hy => rw [ng_img_mul, hy, hx]
    | inv x _ hx => exact ng_img_inv hx
  · intro h; exact Subgroup.subset_closure h

def ngM (f f' : Fin (r + 1) → V) : Submodule M.L.O V := Submodule.span M.L.O (Set.range (Sum.elim f f'))




def ngME (P : FPair H r) : Submodule E V := Submodule.span E (Set.range (Sum.elim P.A.f P.B.f))









def NGBaseInt (P : FPair H r) : Prop := ∀ a b, H.h (P.B.f b) (P.A.f a) ∈ M.L.O

def NGUnimod (P : FPair H r) : Prop :=
  ∀ s ∈ P.St, volRel (P.K0.map (MulAut.conj s).toMonoidHom) P.K0 = 1


def ngLm (e : ℕ → ℕ → E) (l : ℕ) : E := (Matrix.of fun a b : Fin l => e a b).det

def ngW (E : Type) [CommRing E] (s : ℕ) : Matrix (Fin s) (Fin s) E :=
  Matrix.of fun a b => if a.val + b.val + 1 = s then 1 else 0

omit [TopologicalSpace E] [MeasurableSpace E] in
theorem ng_W_sq (s : ℕ) : ngW E s * ngW E s = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have ha := a.2
  have hb := b.2
  rw [Finset.sum_eq_single (⟨s - 1 - a.val, by omega⟩ : Fin s)]
  · simp only [ngW, Matrix.of_apply]
    rw [if_pos (by omega), one_mul]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, if_pos (by omega)]
    · rw [if_neg hab, if_neg]
      intro h; apply hab; apply Fin.ext; omega
  · intro c _ hc'
    simp only [ngW, Matrix.of_apply]
    rw [if_neg, zero_mul]
    intro h; apply hc'; apply Fin.ext
    show c.val = s - 1 - a.val
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

omit [TopologicalSpace E] [MeasurableSpace E] in
theorem ng_lm_cons (t : Eˣ) (s : ℕ+) (bs : List (Eˣ × ℕ+)) (m : ℕ) :
    ngLm (ptEntryL ((t, s) :: bs)) ((s : ℕ) + m) = ((t : E) • ngW E (s : ℕ)).det * ngLm (ptEntryL bs) m := by
  unfold ngLm
  rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := (s : ℕ)) (n := m))]
  have e : (Matrix.of fun a b : Fin ((s : ℕ) + m) => ptEntryL ((t, s) :: bs) a b).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks ((t : E) • ngW E (s : ℕ)) 0 0 (Matrix.of fun a b : Fin m => ptEntryL bs a b) := by
    ext i j
    rcases i with a | a <;> rcases j with b | b
    · have ha := a.2
      have hb := b.2
      simp only [Matrix.submatrix_apply, Matrix.of_apply, finSumFinEquiv_apply_left, Fin.val_castAdd, ptEntryL,
        Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, ngW, smul_eq_mul]
      rw [if_pos ⟨ha, hb⟩]
      split_ifs <;> simp
    · have ha := a.2
      simp only [Matrix.submatrix_apply, Matrix.of_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd, ptEntryL, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      rw [if_neg (by omega), if_neg (by omega)]
    · have hb := b.2
      simp only [Matrix.submatrix_apply, Matrix.of_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd, ptEntryL, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [if_neg (by omega), if_neg (by omega)]
    · simp only [Matrix.submatrix_apply, Matrix.of_apply, finSumFinEquiv_apply_right,
        Fin.val_natAdd, ptEntryL, Matrix.fromBlocks_apply₂₂]
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  rw [e, Matrix.det_fromBlocks_zero₂₁]




def NGOrbit0 (P : FPair H r) : Prop :=
  ∀ n ∈ P.A.N, ∀ n' ∈ P.B.N, (∀ a b, H.h (n' (P.B.f b)) (n (P.A.f a)) ∈ M.L.O) →
    ∃ s ∈ P.St,
      Submodule.span M.L.O (Set.range fun b => s (P.A.f b)) = Submodule.span M.L.O (Set.range fun b => n (P.A.f b)) ∧
      Submodule.span M.L.O (Set.range fun b => s (P.B.f b)) = Submodule.span M.L.O (Set.range fun b => n' (P.B.f b))




structure NGCore2 (k : ℕ) (R : Reps P) (d0 : Datum P) (c : ℕ) (S : Term V M r → Prop) where
  Ds : Finset R.RD
  off : ∀ d : R.RD, d ∉ Ds → R.RT d.1 = ∅
  summ : ∀ d : R.RD, Summable (fun t : R.RT d.1 => mu P t.1)
  Ty : Type
  fin : Fintype Ty
  typ : Term V M r → Ty
  be : Ty → ℝ
  I : Ty → ℝ
  card : (Fintype.card Ty : ℝ) ≤ P.Hp ^ (c * (r + 1) ^ 2)
  be1 : ∀ τ, 1 ≤ be τ
  I0 : ∀ τ, 0 ≤ I τ
  Ibe : ∀ τ, I τ ≤ be τ
  c2 : ∀ (τ : Ty) (d : Ds), massS R d.1.1 (fun t => S t ∧ typ t = τ) ≤ P.Hp ^ (c * (r + 1) ^ 2) * I τ ^ (k - 1)
  c1 : ∀ τ : Ty, ∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 (fun t => S t ∧ typ t = τ) ≤
    P.Hp ^ (c * (r + 1) ^ 2) * (be τ ^ (k - 1))⁻¹ * ∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1

structure NGCore1 (k : ℕ) (R : Reps P) (d0 : Datum P) (c : ℕ) (C₀ : ℝ) extends
    NGCore2 k R d0 c (BBne (H := H)) where
  isBe : Ty → Prop
  Ial : ∀ τ, ¬ isBe τ → I τ ≤ be τ / (qF F : ℝ)
  e : ∀ (τ : Ty) (d : Ds), isBe τ → ‖amp R d.1.1 (fun t => BBne (H := H) t ∧ typ t = τ)‖ ≤
    C₀ * (qF F : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * massS R d.1.1 (fun t => BBne (H := H) t ∧ typ t = τ)

def NGCore2.toSteps {k : ℕ} {R : Reps P} {d0 : Datum P} {c : ℕ} {S : Term V M r → Prop} (X : NGCore2 k R d0 c S)
    (hOK : M.OK) (hH : 1 ≤ P.Hp) : NGSteps2 k R d0 c S where
  Ds := X.Ds
  off := X.off
  summ := X.summ
  om1 := ng_norm_om hOK
  Ty := X.Ty
  fin := X.fin
  typ := X.typ
  be := X.be
  I := X.I
  H1 := hH
  card := X.card
  be1 := X.be1
  I0 := X.I0
  Ibe := X.Ibe
  c2 := X.c2
  c1 := X.c1

def NGCore1.toSteps {k : ℕ} {R : Reps P} {d0 : Datum P} {c : ℕ} {C₀ : ℝ} (X : NGCore1 k R d0 c C₀)
    (hOK : M.OK) (hG : P.Gv ≠ 0) (hH : 1 ≤ P.Hp) (hk : 4 * r + 7 ≤ k) : NGSteps1 k R d0 c C₀ where
  toNGSteps2 := X.toNGCore2.toSteps hOK hH
  hk := hk
  q2 := two_le_residue_card hOK
  qH := fun ⟨d, t, ht, hB⟩ => ng_q_le_Hp hOK hG ((R.hRT d.1).1 ht) hB
  isBe := X.isBe
  Ial := X.Ial
  e := X.e

end NGa

def NGStepsAll' (k r c : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) →
        (∀ (R : Reps P) (d0 : Datum P), Nonempty (NGCore1 k R d0 c C₀) ∧
            Nonempty (NGCore2 k R d0 c (fun t => ¬ BBne (H := H) t)) ∧ Nonempty (NGCore2 k R d0 c (fun _ => True))) ∧
          (P.PrimeTo → ∀ R : Reps P, NGEqStep' P R)




def NGLeft (k r c : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) →
        (P.PrimeTo → NGOrbit0 P ∧ NGUnimod P) ∧
        (¬ P.PrimeTo → ∀ (R : Reps P) (d0 : Datum P), Nonempty (NGCore1 k R d0 c C₀) ∧
            Nonempty (NGCore2 k R d0 c (fun t => ¬ BBne (H := H) t)) ∧ Nonempty (NGCore2 k R d0 c (fun _ => True)))



end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section NGb

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

def NgLow {R : Type} [Zero R] [One R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ a b, a < b → A a b = 0) ∧ ∀ a, A a a = 1

def NgUp {R : Type} [Zero R] [One R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ a b, b < a → A a b = 0) ∧ ∀ a, A a a = 1

def NGMat (P : FPair H r) : Prop :=
  ∀ Lo Up : Matrix (Fin (r + 1)) (Fin (r + 1)) E, NgLow Lo → NgUp Up →
    (∀ a b, (Lo * H.Zhat P.A.f P.B.f * Up) a b ∈ M.L.O) →
    ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, NgLow A ∧ NgUp A' ∧ (∀ a b, A a b ∈ M.L.O) ∧ (∀ a b, A' a b ∈ M.L.O) ∧
      A * (Lo * H.Zhat P.A.f P.B.f * Up) * A' = H.Zhat P.A.f P.B.f

end NGb

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

section Mat

variable {E : Type} [CommRing E] {n : ℕ}

def NgmLow (A : Matrix (Fin n) (Fin n) E) : Prop := (∀ a, A a a = 1) ∧ ∀ a b, a < b → A a b = 0

def NgmUp (A : Matrix (Fin n) (Fin n) E) : Prop := (∀ a, A a a = 1) ∧ ∀ a b, b < a → A a b = 0

def NgmInt (O : Subring E) (A : Matrix (Fin n) (Fin n) E) : Prop := ∀ a b, A a b ∈ O

def ngmMono (σ : Fin n → Fin n) (t : Fin n → E) : Matrix (Fin n) (Fin n) E := fun a b => if b = σ a then t a else 0

theorem NgmLow.mul {A B : Matrix (Fin n) (Fin n) E} (hA : NgmLow A) (hB : NgmLow B) : NgmLow (A * B) := by
  constructor
  · intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.1, hB.1, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hB.2 k a h, mul_zero]
      · rw [hA.2 a k h, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a b hab
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases le_or_gt k a with h | h
    · rw [hB.2 k b (lt_of_le_of_lt h hab), mul_zero]
    · rw [hA.2 a k h, zero_mul]

theorem ngm_up_iff {A : Matrix (Fin n) (Fin n) E} : NgmUp A ↔ NgmLow A.transpose :=
  ⟨fun h => ⟨h.1, fun a b hab => h.2 b a hab⟩, fun h => ⟨h.1, fun a b hab => h.2 b a hab⟩⟩

theorem NgmUp.mul {A B : Matrix (Fin n) (Fin n) E} (hA : NgmUp A) (hB : NgmUp B) : NgmUp (A * B) := by
  rw [ngm_up_iff, Matrix.transpose_mul]
  exact (ngm_up_iff.1 hB).mul (ngm_up_iff.1 hA)

theorem NgmInt.mul {O : Subring E} {A B : Matrix (Fin n) (Fin n) E} (hA : NgmInt O A) (hB : NgmInt O B) :
    NgmInt O (A * B) := fun a b => by
  rw [Matrix.mul_apply]
  exact O.sum_mem (fun k _ => O.mul_mem (hA a k) (hB k b))




def NgmLP (O : Subring E) (A B : Matrix (Fin n) (Fin n) E) : Prop :=
  NgmLow A ∧ NgmInt O A ∧ NgmLow B ∧ NgmInt O B ∧ A * B = 1 ∧ B * A = 1

def NgmUP (O : Subring E) (A B : Matrix (Fin n) (Fin n) E) : Prop :=
  NgmUp A ∧ NgmInt O A ∧ NgmUp B ∧ NgmInt O B ∧ A * B = 1 ∧ B * A = 1



theorem ngm_inv_mul {A₁ B₁ A₂ B₂ : Matrix (Fin n) (Fin n) E} (h₁ : A₁ * B₁ = 1) (h₂ : A₂ * B₂ = 1) :
    (A₂ * A₁) * (B₁ * B₂) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc A₁, h₁, Matrix.one_mul, h₂]

theorem NgmLP.mul {O : Subring E} {A₁ B₁ A₂ B₂ : Matrix (Fin n) (Fin n) E} (h₂ : NgmLP O A₂ B₂) (h₁ : NgmLP O A₁ B₁) :
    NgmLP O (A₂ * A₁) (B₁ * B₂) :=
  ⟨h₂.1.mul h₁.1, h₂.2.1.mul h₁.2.1, h₁.2.2.1.mul h₂.2.2.1, h₁.2.2.2.1.mul h₂.2.2.2.1,
    ngm_inv_mul h₁.2.2.2.2.1 h₂.2.2.2.2.1, ngm_inv_mul h₂.2.2.2.2.2 h₁.2.2.2.2.2⟩

theorem NgmUP.mul {O : Subring E} {A₁ B₁ A₂ B₂ : Matrix (Fin n) (Fin n) E} (h₂ : NgmUP O A₂ B₂) (h₁ : NgmUP O A₁ B₁) :
    NgmUP O (A₂ * A₁) (B₁ * B₂) :=
  ⟨h₂.1.mul h₁.1, h₂.2.1.mul h₁.2.1, h₁.2.2.1.mul h₂.2.2.1, h₁.2.2.2.1.mul h₂.2.2.2.1,
    ngm_inv_mul h₁.2.2.2.2.1 h₂.2.2.2.2.1, ngm_inv_mul h₂.2.2.2.2.2 h₁.2.2.2.2.2⟩


def ngmR (p : Fin n) (v : Fin n → E) : Matrix (Fin n) (Fin n) E := fun a a' => if a' = p then v a else 0

def ngmC (c : Fin n) (u : Fin n → E) : Matrix (Fin n) (Fin n) E := fun b' b => if b' = c then u b else 0











def NgmInv (σ : Fin n → Fin n) (i : ℕ) (Lo Up : Matrix (Fin n) (Fin n) E) : Prop :=
  NgmLow Lo ∧ NgmUp Up ∧ (∀ a a' : Fin n, a'.val < i → a ≠ a' → Lo a a' = 0) ∧
    (∀ a' b : Fin n, a'.val < i → b ≠ σ a' → Up (σ a') b = 0) ∧ (∀ a' b' : Fin n, a'.val < i → b' ≠ σ a' → Up b' (σ a') = 0)





end Mat

section Pt

open Formalism.MainNotions.S.Loc

variable {E : Type} [CommRing E]

def ngmSig : List (Eˣ × ℕ+) → ℕ → ℕ
  | [], i => i
  | (_, s) :: bs, i => if i < (s : ℕ) then (s : ℕ) - 1 - i else (s : ℕ) + ngmSig bs (i - s)

def ngmT : List (Eˣ × ℕ+) → ℕ → Eˣ
  | [], _ => 1
  | (t, s) :: bs, i => if i < (s : ℕ) then t else ngmT bs (i - s)




end Pt

section NGc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}



end NGc

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section NGc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}



section Glue

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def ngsC (H : HermSp M V) (m : ι → V) (v : V) : ι → E := (H.gram m)⁻¹.mulVec (fun j => H.h v (m j))

theorem ngsC_add (m : ι → V) (v w : V) : ngsC H m (v + w) = ngsC H m v + ngsC H m w := by
  unfold ngsC
  rw [← Matrix.mulVec_add]
  congr 1
  funext j
  exact H.h_add_left _ _ _

theorem ngsC_smul (m : ι → V) (c : E) (v : V) : ngsC H m (c • v) = c • ngsC H m v := by
  unfold ngsC
  rw [← Matrix.mulVec_smul]
  congr 1
  funext j
  exact H.h_smul_left _ _ _

def ngsT (H : HermSp M V) (m m' : ι → V) : V →ₗ[E] V where
  toFun v := v - ∑ i, ngsC H m v i • m i + ∑ i, ngsC H m v i • m' i
  map_add' v w := by
    simp only [ngsC_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c v := by
    simp only [ngsC_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, ← Finset.smul_sum, smul_add, smul_sub]










end Glue












variable {P : FPair H r}



end NGc

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.MainNotions.S.LocNG

section Grp

variable {G : Type*} [Group G]



end Grp

section Lat

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]


def NguFinRep (M : Model F E) (c : E) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (rep : Q → E), ∀ o ∈ M.L.O, ∃ q, ∃ o' ∈ M.L.O, o - rep q = c * o'







variable {H : HermSp M V} {r : ℕ} {P : FPair H r}




end Lat

section Left

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc ValuativeRel

def NGLeft1 (k r c : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) →
        (P.PrimeTo → NGOrbit0 P) ∧
        (¬ P.PrimeTo → ∀ (R : Reps P) (d0 : Datum P), Nonempty (NGCore1 k R d0 c C₀) ∧
            Nonempty (NGCore2 k R d0 c (fun t => ¬ BBne (H := H) t)) ∧ Nonempty (NGCore2 k R d0 c (fun _ => True)))




end Left

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section NGe

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}





end NGe

end Formalism.MainNotions.KappaEndpoints

end

noncomputable section

namespace Formalism.MainNotions.KappaEndpoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section NGf

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}



end NGf

section Left2

def NGLeft2 (k r c : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) →
        ¬ P.PrimeTo → ∀ (R : Reps P) (d0 : Datum P), Nonempty (NGCore1 k R d0 c C₀) ∧
            Nonempty (NGCore2 k R d0 c (fun t => ¬ BBne (H := H) t)) ∧ Nonempty (NGCore2 k R d0 c (fun _ => True))




end Left2

end Formalism.MainNotions.KappaEndpoints

end
