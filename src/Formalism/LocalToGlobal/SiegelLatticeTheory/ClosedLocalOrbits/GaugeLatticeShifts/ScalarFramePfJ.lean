import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Concrete

variable {D : D7} (Z : LocDat D) (p : PlF D)

def IotaEl (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ g : Loc.SplitG (Z.M p).L, (Z.M p).split = some g →
    IotaG (locH Z p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ)
      (fun a => sF Z p a • baseChange₂ D p (f a)) (fun b => sF' Z p b • baseChange₂ D p (g1 b))
      (fun b => sF' Z p b • baseChange₂ D p (g2 b)) (betaP p β)

theorem omp_combine (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (P K : (D.s.atP p).Ep) :
    (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g1)) -
      (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g2)) =
    (P * K) • baseChange₂ D p (GDl f g2 (D.R.rS + 1) • Gom' f g1 - GDl f g1 (D.R.rS + 1) • Gom' f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2 <;> ring

theorem om_combine (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (P K : (D.s.atP p).Ep) :
    (Z.M p).L.cj (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (β (Gom f g1))) -
      (Z.M p).L.cj (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom f g2)) =
    ((Z.M p).L.cj P * K) • baseChange₂ D p (star (GDl f g2 (D.R.rS + 1)) • β (Gom f g1) -
      star (GDl f g1 (D.R.rS + 1)) • Gom f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, map_mul, map_mul,
    cj_iota (Z.hcj p), cj_iota (Z.hcj p)]
  congr 2 <;> ring


end Concrete

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FrameAct

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

abbrev Xs (h : Fin (r + 1) → S.V) : Submodule E S.V :=
  Submodule.span E (Set.range fun a : Fin r => h a.castSucc)

theorem frameAct_castSucc_mem (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (hξ : ∀ a b, b < a → ξ a b = 0) (a : Fin r) : frameAct h ξ a.castSucc ∈ Xs h := by
  show ∑ c, ((ξ c a.castSucc : 𝓞 E) : E) • h c ∈ _
  have h0 : ((ξ (Fin.last r) a.castSucc : 𝓞 E) : E) = 0 := by
    rw [hξ _ _ (Fin.castSucc_lt_last a)]
    rfl
  rw [Fin.sum_univ_castSucc, h0, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_last_sub (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (hl : ξ (Fin.last r) (Fin.last r) = 1) : frameAct h ξ (Fin.last r) - h (Fin.last r) ∈ Xs h := by
  show ∑ c, ((ξ c (Fin.last r) : 𝓞 E) : E) • h c - h (Fin.last r) ∈ _
  have h1 : ((ξ (Fin.last r) (Fin.last r) : 𝓞 E) : E) = 1 := by
    rw [hl]
    rfl
  rw [Fin.sum_univ_castSucc, h1, one_smul, add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_mem_span (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (b : Fin (r + 1)) : frameAct h ξ b ∈ Submodule.span E (Set.range h) :=
  Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_frameAct (h : Fin (r + 1) → S.V) (ξ ξ' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) :
    frameAct (frameAct h ξ) ξ' = frameAct h (ξ * ξ') := by
  funext b
  simp only [frameAct, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  push_cast
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem frameAct_one (h : Fin (r + 1) → S.V) : frameAct h 1 = h := by
  funext b
  simp only [frameAct, Matrix.one_apply]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [hc]
  · intro hb; exact absurd (Finset.mem_univ b) hb

theorem det_unitri {n : ℕ} {R : Type*} [CommRing R] (ξ : Matrix (Fin n) (Fin n) R)
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : ξ.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => h1 i j hij)]
  simp [h2]

theorem frameAct_inv_back (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : frameAct (frameAct h ξ⁻¹) ξ = h := by
  rw [frameAct_frameAct, Matrix.nonsing_inv_mul _ (by rw [det_unitri ξ h1 h2]; exact isUnit_one),
    frameAct_one]

theorem Xs_frameAct_inv (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : Xs (frameAct h ξ⁻¹) = Xs h := by
  have hi := inv_unitri ξ h1 h2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact frameAct_castSucc_mem h _ hi.1 a
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have := frameAct_castSucc_mem (frameAct h ξ⁻¹) ξ h1 a
    rwa [frameAct_inv_back h ξ h1 h2] at this

theorem span_frameAct_inv (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    Submodule.span E (Set.range (frameAct h ξ⁻¹)) = Submodule.span E (Set.range h) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact frameAct_mem_span h _ a
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have := frameAct_mem_span (frameAct h ξ⁻¹) ξ a
    rwa [frameAct_inv_back h ξ h1 h2] at this

end FrameAct

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GZ

variable {D : D7}

theorem unitri_map (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    (∀ a b, b < a → η.map (fun x => (x : D.host.E)) a b = 0) ∧ (∀ a, η.map (fun x => (x : D.host.E)) a a = 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.map_apply, h1 a b hab]; rfl
  · rw [Matrix.map_apply, h2 a]; rfl

theorem GZ_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V) (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    GZ u (frameAct h η) = GZ u h * η.map (fun x => (x : D.host.E)) := by
  ext a b
  simp only [GZ, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, frameAct, brS, map_sum, map_smul,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem GDl_frameAct_top (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    GDl u (frameAct h η) (D.R.rS + 1) = GDl u h (D.R.rS + 1) := by
  have hm := unitri_map η h1 h2
  unfold GDl
  rw [dif_pos le_rfl, dif_pos le_rfl]
  have e : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      M.submatrix (Fin.castLE (le_refl _)) (Fin.castLE (le_refl _)) = M := fun M => by ext i j; rfl
  rw [e, e, GZ_frameAct, Matrix.det_mul, det_unitri _ hm.1 hm.2, mul_one]

theorem GDl_frameAct_r (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    GDl u (frameAct h η) D.R.rS = GDl u h D.R.rS := by
  have hm := unitri_map η h1 h2
  unfold GDl
  rw [dif_pos (Nat.le_succ _), dif_pos (Nat.le_succ _), GZ_frameAct]
  have ecs : (Fin.castLE (Nat.le_succ D.R.rS) : Fin D.R.rS → Fin (D.R.rS + 1)) = Fin.castSucc :=
    funext fun i => Fin.ext rfl
  rw [ecs]
  have e : (GZ u h * η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc =
      (GZ u h).submatrix Fin.castSucc Fin.castSucc *
      (η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
      hm.1 _ _ (Fin.castSucc_lt_last j), mul_zero, add_zero]
    rfl
  rw [e, Matrix.det_mul, det_unitri ((η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc)
    (fun a b hab => hm.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hab)) (fun a => hm.2 _), mul_one]

theorem Gom'_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    Gom' u (frameAct h η) = Gom' u h := by
  have hm := unitri_map η h1 h2
  set ηE := η.map (fun x => (x : D.host.E)) with hηE
  have hkey : ηE * (ηE.adjugate * (GZ u h).adjugate) = (GZ u h).adjugate := by
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, det_unitri _ hm.1 hm.2, one_smul, Matrix.one_mul]
  unfold Gom'
  rw [GZ_frameAct, Matrix.adjugate_mul_distrib]
  simp only [frameAct, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have := congrFun (congrFun hkey c) (Fin.last _)
  rw [Matrix.mul_apply] at this
  rw [← this]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem Gom_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    Gom u (frameAct h η) = Gom u h := by
  have hm := unitri_map η h1 h2
  set ηE := η.map (fun x => (x : D.host.E)) with hηE
  have hadj : ηE.adjugate = ηE⁻¹ := by
    rw [Matrix.inv_def, det_unitri _ hm.1 hm.2, Ring.inverse_one, one_smul]
  have hinv := inv_unitri ηE hm.1 hm.2
  unfold Gom
  rw [GZ_frameAct, Matrix.adjugate_mul_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last _), hadj, hinv.2, one_mul]
  · intro k _ hk
    rw [hadj, hinv.1 _ _ (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end GZ

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open PI.ScalarPairDr.W (mem_orth hT_swap orth_orth finrank_orth fvec_castSucc fvec_last mem_orth_Xplus
  X_le_orth_Xplus mem_ThPairs hT_add_left hT_sub_left hT_smul_left)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem exists_hos : ∃ _P : HeightOneSpectrum (𝓞 E), True := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (NumberField.RingOfIntegers.not_isField E)
  exact ⟨⟨p, hp, hp0⟩, trivial⟩

theorem X_le_spanE_of_conv (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (g : ℕ) (hc : IsFixedConv Λ g F) :
    Xsp F ≤ spanE S (XLam Λ F) := by
  obtain ⟨P, -⟩ := exists_hos (E := E)
  have := P.isPrime
  obtain ⟨c, hc0, -, heq⟩ := hc.1 P
  rw [Xsp, FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have h1 : c a • F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
    rw [heq]
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨a, rfl⟩⟩
  obtain ⟨s, hs, hsx⟩ := h1
  have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h, map_zero])
    rw [this]
    exact P.asIdeal.zero_mem
  have hmem : s • (c a • F.fl.e a) ∈ spanE S (XLam Λ F) := Submodule.subset_span hsx
  have e : F.fl.e a = ((algebraMap (𝓞 E) E s) * c a)⁻¹ • (s • (c a • F.fl.e a)) := by
    rw [algebra_compatible_smul E s, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hs0 (hc0 a)),
      one_smul]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ hmem

theorem Xs_fvec (F : FlagG S r T) : Xs (S := S) F.fvec = F.X := by
  have h : (fun a : Fin r => F.fvec a.castSucc) = F.e := funext fun a => fvec_castSucc F a
  show Submodule.span E (Set.range fun a : Fin r => F.fvec a.castSucc) = _
  rw [h]
  rfl

theorem Xflag_top (F : LFlag S r T) : Xflag F r = Xsp F := by
  rw [Xflag, FlagG.Xa, Xsp, FlagG.X]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩

theorem hT_X_X (F : FlagG S r T) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : S.hT x y = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  refine key y (fun a => ?_) x hx
  rw [hT_swap]
  have h1 : S.hT y (F.e a) = 0 := key (F.e a) (fun b => F.e_iso b a) y hy
  rw [h1, star_zero]

theorem hT_z_X (F : FlagG S r T) {y : S.V} (hy : y ∈ F.X) : S.hT F.z y = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  rw [hT_swap, key F.z F.z_orth y hy, star_zero]

theorem hT_X_alt (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT x F.z = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  exact key F.z F.z_orth x hx

theorem theta_eq (Λ : Submodule (𝓞 E) S.V) (k : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β : S.V ≃ₗ[E] S.V) (hn : finrank E S.V = k + 2 * r + 1)
    (hd1 : finrank E (UUE Λ F F') = 2 * r + 2) (hd2 : finrank E (UUE Λ F F'') = 2 * r + 2)
    (hU1 : UUE Λ F F' = Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)))
    (hG' : Gval F F' ≠ 0) (hs : s0 Λ F F' F'' β k = 1) :
    Th Λ F F' F'' β = Hp Λ F F' ∧ Th'' Λ F F' F'' β = Hp Λ F F'' := by
  have hH1 : finrank E (Hp Λ F F') + 1 = k := by
    have := finrank_orth S (UUE Λ F F')
    rw [Hp]
    omega
  have hH2 : finrank E (Hp Λ F F'') + 1 = k := by
    have := finrank_orth S (UUE Λ F F'')
    rw [Hp]
    omega
  have hTh : finrank E (Th Λ F F' F'' β) + 1 = k := by
    unfold s0 at hs
    omega
  have hThle : Th Λ F F' F'' β ≤ Hp Λ F F' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).1
  refine ⟨Submodule.eq_of_le_of_finrank_eq hThle (by omega), ?_⟩
  have hTh''le : Th'' Λ F F' F'' β ≤ Hp Λ F F'' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).2.1
  refine Submodule.eq_of_le_of_finrank_eq hTh''le ?_
  let f := (LinearMap.snd E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    have hm := (mem_ThPairs Λ F F' F'' β p.1).1 p.2
    have h2 : p.1.2 = 0 := hp
    have hx1 : p.1.1 ∈ F.fl.X := by
      have := hm.2.2.1
      rwa [h2, sub_zero] at this
    have h1 : p.1.1 = 0 := by
      refine PI.ScalarPairDr.W.eq_zero_of_orth F.fl F'.fl hG' hx1 fun b => ?_
      have hm1 := hm.1
      rw [Hp, mem_orth] at hm1
      exact hm1 _ (by rw [hU1]; exact Submodule.subset_span ⟨Sum.inr b, rfl⟩)
    exact Subtype.ext (Prod.ext h1 h2)
  have hrange : LinearMap.range f = Th'' Λ F F' F'' β := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, hrange, finrank_bot] at h1
  have h2 : finrank E (Th Λ F F' F'' β) ≤ finrank E (ThPairs Λ F F' F'' β) :=
    Submodule.finrank_map_le _ _
  have h3 := Submodule.finrank_mono hTh''le
  omega

theorem ylift_tr (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hTh : Th Λ F F' F'' β = Hp Λ F F') {y : S.V} (hy : y ∈ UUE Λ F F'') (hyo : y ∈ orth S (Xplus F)) :
    y ∈ UUE Λ F F' := by
  rw [← orth_orth S (UUE Λ F F'), mem_orth]
  intro v hv
  have hv' : v ∈ Th Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT p.2 y = 0 := by
    have := (mem_orth S).1 hm.2.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (p.1 - p.2) y = 0 := (mem_orth S).1 hyo _ (Submodule.mem_sup_left hm.2.2.1)
  have : p.1 = (p.1 - p.2) + p.2 := by abel
  show S.hT p.1 y = 0
  rw [this, hT_add_left, e1, e2, add_zero]

theorem ylift_tr' (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y : S.V} (hy : y ∈ UUE Λ F F') (hyo : y ∈ orth S (Xplus F)) :
    y ∈ UUE Λ F F'' := by
  rw [← orth_orth S (UUE Λ F F''), mem_orth]
  intro v hv
  have hv' : v ∈ Th'' Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT p.1 y = 0 := by
    have := (mem_orth S).1 hm.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (p.1 - p.2) y = 0 := (mem_orth S).1 hyo _ (Submodule.mem_sup_left hm.2.2.1)
  have : p.2 = p.1 - (p.1 - p.2) := by abel
  show S.hT p.2 y = 0
  rw [this, hT_sub_left, e1, e2, sub_zero]

theorem ylift_beta (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hiso : ∀ x y, S.hT (β x) (β y) = S.hT x y) (hX : ∀ x ∈ Xsp F'', β.symm x ∈ Xsp F')
    (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y : S.V} (hy : y ∈ UUE Λ F F') (hyo : y ∈ orth S (Xsp F')) :
    β y ∈ UUE Λ F F'' := by
  rw [← orth_orth S (UUE Λ F F''), mem_orth]
  intro v hv
  have hv' : v ∈ Th'' Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT (β p.1) (β y) = 0 := by
    rw [hiso]
    have := (mem_orth S).1 hm.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (β p.1 - p.2) (β y) = 0 := by
    have h := hX _ hm.2.2.2
    have : β p.1 - p.2 = β (β.symm (β p.1 - p.2)) := (β.apply_symm_apply _).symm
    rw [this, hiso]
    exact (mem_orth S).1 hyo _ h
  have : p.2 = β p.1 - (β p.1 - p.2) := by abel
  show S.hT p.2 (β y) = 0
  rw [this, hT_sub_left, e1, e2, sub_zero]

end Lat

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cof

variable {D : D7}

theorem GZ_apply (u v : Fin (D.R.rS + 1) → (VS D).V) (a b : Fin (D.R.rS + 1)) :
    GZ u v a b = (VS D).hT (u a) (v b) := rfl

theorem GDl_top' (u v : Fin (D.R.rS + 1) → (VS D).V) : GDl u v (D.R.rS + 1) = (GZ u v).det := by
  unfold GDl
  rw [dif_pos le_rfl]
  congr 1

theorem GDl_r' (u v : Fin (D.R.rS + 1) → (VS D).V) :
    GDl u v D.R.rS = ((GZ u v).submatrix Fin.castSucc Fin.castSucc).det := by
  unfold GDl
  rw [dif_pos (Nat.le_succ _)]
  have ecs : (Fin.castLE (Nat.le_succ D.R.rS) : Fin D.R.rS → Fin (D.R.rS + 1)) = Fin.castSucc :=
    funext fun i => Fin.ext rfl
  rw [ecs]

theorem om'_pair (u v : Fin (D.R.rS + 1) → (VS D).V) (a : Fin (D.R.rS + 1)) :
    (VS D).hT (u a) (Gom' u v) = if a = Fin.last _ then GDl u v (D.R.rS + 1) else 0 := by
  have key := congrFun (congrFun (Matrix.mul_adjugate (GZ u v)) a) (Fin.last _)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at key
  rw [GDl_top']
  unfold Gom'
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [show (∑ b, (GZ u v).adjugate b (Fin.last _) * (VS D).hT (u a) (v b)) =
      ∑ b, GZ u v a b * (GZ u v).adjugate b (Fin.last _) from
    Finset.sum_congr rfl fun b _ => by rw [GZ_apply, mul_comm], key]
  split_ifs <;> simp

theorem om'_decomp (u v : Fin (D.R.rS + 1) → (VS D).V) :
    Gom' u v - GDl u v D.R.rS • v (Fin.last _) ∈ Xs (S := VS D) v := by
  unfold Gom'
  rw [Fin.sum_univ_castSucc, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r', add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem om_pair (u v : Fin (D.R.rS + 1) → (VS D).V) (b : Fin (D.R.rS + 1)) :
    (VS D).hT (Gom u v) (v b) = if b = Fin.last _ then GDl u v (D.R.rS + 1) else 0 := by
  have key := congrFun (congrFun (Matrix.adjugate_mul (GZ u v)) (Fin.last _)) b
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at key
  rw [GDl_top']
  unfold Gom
  rw [map_sum, LinearMap.sum_apply]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  rw [show (∑ a, (GZ u v).adjugate (Fin.last _) a * (VS D).hT (u a) (v b)) =
      ∑ a, (GZ u v).adjugate (Fin.last _) a * GZ u v a b from rfl, key]
  rcases eq_or_ne b (Fin.last _) with hb | hb
  · subst hb
    simp
  · rw [if_neg (Ne.symm hb), if_neg hb, smul_zero]

theorem om_decomp (u v : Fin (D.R.rS + 1) → (VS D).V) :
    Gom u v - star (GDl u v D.R.rS) • u (Fin.last _) ∈ Xs (S := VS D) u := by
  unfold Gom
  rw [Fin.sum_univ_castSucc, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r', add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem lemB (u v : Fin (D.R.rS + 1) → (VS D).V) (hdet : GDl u v (D.R.rS + 1) ≠ 0) {q : (VS D).V}
    (hq : q ∈ Submodule.span D.host.E (Set.range v)) (h : ∀ a, (VS D).hT (u a) q = 0) : q = 0 := by
  obtain ⟨π, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hq
  have hm : Matrix.mulVec (GZ u v) π = 0 := by
    funext a
    have := h a
    rw [map_sum] at this
    simp only [map_smul, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, GZ_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [GDl_top'] at hdet
  have hπ := Matrix.eq_zero_of_mulVec_eq_zero hdet hm
  simp [hπ]

theorem eq_zero_of_orth_of_det_ne_zero (u v : Fin (D.R.rS + 1) → (VS D).V) (hdet : GDl u v (D.R.rS + 1) ≠ 0) {q : (VS D).V}
    (hq : q ∈ Submodule.span D.host.E (Set.range u)) (h : ∀ b, (VS D).hT q (v b) = 0) : q = 0 := by
  obtain ⟨κ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hq
  have hm : Matrix.vecMul (fun a => star (κ a)) (GZ u v) = 0 := by
    funext b
    have := h b
    rw [map_sum, LinearMap.sum_apply] at this
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at this
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, GZ_apply]
    exact this
  rw [GDl_top'] at hdet
  have hκ := Matrix.eq_zero_of_vecMul_eq_zero hdet hm
  have : κ = 0 := by
    funext a
    have := congrFun hκ a
    simpa using this
  simp [this]

theorem lemC (v : Fin (D.R.rS + 1) → (VS D).V) (hv : LinearIndependent D.host.E v) {c : D.host.E}
    (h : c • v (Fin.last _) ∈ Xs (S := VS D) v) : c = 0 := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 h
  have h0 : ∑ i, (Fin.snoc (α := fun _ => D.host.E) d (-c) i) • v i = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, neg_smul]
    rw [hd, add_neg_cancel]
  have := Fintype.linearIndependent_iff.1 hv _ h0 (Fin.last _)
  simpa using this

end Cof

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open PI.ScalarPairDr.W (mem_orth hT_swap orth_orth fvec_castSucc fvec_last mem_orth_Xplus hT_smul_left)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scal

variable {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}

theorem span_left_le (F : LFlag (VS D) D.R.rS T) (F₁ : LFlag (VS D) D.R.rS T') :
    Submodule.span D.host.E (Set.range F.fl.fvec) ≤
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₁.fl.fvec)) :=
  Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩)

theorem span_right_le (F : LFlag (VS D) D.R.rS T) (F₁ : LFlag (VS D) D.R.rS T') :
    Submodule.span D.host.E (Set.range F₁.fl.fvec) ≤
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₁.fl.fvec)) :=
  Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩)

theorem Xsp_le_span (F : LFlag (VS D) D.R.rS T) :
    Xsp F ≤ Submodule.span D.host.E (Set.range F.fl.fvec) := by
  rw [Xsp, FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a.castSucc, fvec_castSucc _ _⟩

theorem Xsp_eq_Xs (F : LFlag (VS D) D.R.rS T) : Xsp F = Xs (S := VS D) F.fl.fvec := (Xs_fvec F.fl).symm

theorem z_mem_span (F : LFlag (VS D) D.R.rS T) :
    F.fl.z ∈ Submodule.span D.host.E (Set.range F.fl.fvec) :=
  Submodule.subset_span ⟨Fin.last _, fvec_last _⟩

theorem Gom'_mem (u v : Fin (D.R.rS + 1) → (VS D).V) : Gom' u v ∈ Submodule.span D.host.E (Set.range v) :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem Gom_mem (u v : Fin (D.R.rS + 1) → (VS D).V) : Gom u v ∈ Submodule.span D.host.E (Set.range u) :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem scal_dir (F : LFlag (VS D) D.R.rS T) (F₁ F₂ : LFlag (VS D) D.R.rS T')
    (hz : F.zt = F.fl.z) (hz₁ : F₁.zt = F₁.fl.z) (hz₂ : F₂.zt = F₂.fl.z) (hT0 : T ≠ 0)
    (hU2 : UUE Λ F F₂ = Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₂.fl.fvec)))
    (htr : ∀ y ∈ UUE Λ F F₂, y ∈ orth (VS D) (Xplus F) → y ∈ UUE Λ F F₁)
    (hsc : ∀ y, y ∈ Ylift Λ F F₁ → y ∈ Ylift Λ F F₂ → ∀ α α', SgRel F F₂ y 0 α α' → SgRel F F₁ y 0 α α')
    (hind : LinearIndependent D.host.E F₁.fl.fvec)
    (hD1 : GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) ≠ 0) :
    (∃ x ∈ Xsp F, GDl F.fl.fvec F₂.fl.fvec (D.R.rS + 1) • Gom' F.fl.fvec F₁.fl.fvec =
      GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) • (Gom' F.fl.fvec F₂.fl.fvec - x)) ∧
    GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) * GDl F.fl.fvec F₂.fl.fvec D.R.rS =
      GDl F.fl.fvec F₂.fl.fvec (D.R.rS + 1) * GDl F.fl.fvec F₁.fl.fvec D.R.rS := by
  set f := F.fl.fvec with hf
  set f1 := F₁.fl.fvec with hf1
  set f2 := F₂.fl.fvec with hf2
  set D1 := GDl f f1 (D.R.rS + 1) with hD1def
  set D2 := GDl f f2 (D.R.rS + 1) with hD2def
  set R1 := GDl f f1 D.R.rS with hR1def
  set R2 := GDl f f2 D.R.rS with hR2def
  set om1 := Gom' f f1 with hom1
  set om2 := Gom' f f2 with hom2
  have hfl : f (Fin.last _) = F.fl.z := fvec_last _
  have hfc : ∀ a : Fin D.R.rS, f a.castSucc = F.fl.e a := fun a => fvec_castSucc _ a
  have p1 : ∀ a, (VS D).hT (f a) om1 = if a = Fin.last _ then D1 else 0 := om'_pair f f1
  have p2 : ∀ a, (VS D).hT (f a) om2 = if a = Fin.last _ then D2 else 0 := om'_pair f f2
  have hzz : (VS D).hT F.fl.z F.fl.z = -T := F.fl.z_norm
  set u2 := om2 + (D2 / T) • F.fl.z with hu2
  have hu2U : u2 ∈ UUE Λ F F₂ := by
    rw [hU2]
    exact Submodule.add_mem _ (span_right_le F F₂ (Gom'_mem f f2))
      (Submodule.smul_mem _ _ (span_left_le F F₂ (z_mem_span F)))
  have hu2o : u2 ∈ orth (VS D) (Xplus F) := by
    rw [Xplus, mem_orth_Xplus]
    refine ⟨fun a => ?_, ?_⟩
    · have h1 := p2 a.castSucc
      rw [if_neg (Fin.castSucc_ne_last a), hfc] at h1
      rw [hu2, map_add, map_smul, h1, F.fl.z_orth a, smul_zero, add_zero]
    · have h1 := p2 (Fin.last _)
      rw [if_pos rfl, hfl] at h1
      rw [hu2, map_add, map_smul, h1, hzz, smul_eq_mul]
      field_simp
      ring
  have hu2U1 := htr u2 hu2U hu2o
  have hx2 : om2 - R2 • F₂.fl.z ∈ Xsp F₂ := by
    rw [Xsp_eq_Xs, ← fvec_last F₂.fl]
    exact om'_decomp f f2
  have hsg : SgRel F F₂ u2 0 (D2 / T) R2 :=
    ⟨0, Submodule.zero_mem _, om2 - R2 • F₂.fl.z, hx2, by rw [hz, hz₂, hu2]; abel⟩
  obtain ⟨x, hx, x1, hx1, heq⟩ := hsc u2 (Submodule.mem_inf.2 ⟨hu2U1, hu2o⟩)
    (Submodule.mem_inf.2 ⟨hu2U, hu2o⟩) _ _ hsg
  rw [hz, hz₁, hu2, sub_zero] at heq
  have hp : R2 • F₁.fl.z + x1 = om2 - x := by
    have : om2 - x = (om2 + (D2 / T) • F.fl.z) - (D2 / T) • F.fl.z - x := by abel
    rw [this, heq]
    abel
  have hpspan : om2 - x ∈ Submodule.span D.host.E (Set.range f1) := by
    rw [← hp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (z_mem_span F₁)) (Xsp_le_span F₁ hx1)
  have hxX : x ∈ F.fl.X := hx
  have hq0 : D1 • (om2 - x) - D2 • om1 = 0 := by
    refine lemB f f1 hD1 (Submodule.sub_mem _ (Submodule.smul_mem _ _ hpspan)
      (Submodule.smul_mem _ _ (Gom'_mem f f1))) fun a => ?_
    rw [map_sub, map_smul, map_smul, map_sub, p1, p2, smul_eq_mul, smul_eq_mul]
    induction a using Fin.lastCases with
    | last =>
      rw [if_pos rfl, if_pos rfl, hfl, hT_z_X F.fl hxX]
      ring
    | cast a =>
      rw [if_neg (Fin.castSucc_ne_last a), if_neg (Fin.castSucc_ne_last a), hfc,
        hT_X_X F.fl (Submodule.subset_span ⟨a, rfl⟩) hxX]
      ring
  refine ⟨⟨x, hx, (sub_eq_zero.1 hq0).symm⟩, ?_⟩
  have hy1 : om1 - R1 • f1 (Fin.last _) ∈ Xs (S := VS D) f1 := om'_decomp f f1
  have hx1' : x1 ∈ Xs (S := VS D) f1 := by rw [← Xsp_eq_Xs]; exact hx1
  have hlast1 : f1 (Fin.last _) = F₁.fl.z := fvec_last _
  have e : (D1 * R2 - D2 * R1) • f1 (Fin.last _) =
      D2 • (om1 - R1 • f1 (Fin.last _)) - D1 • x1 + (D1 • (om2 - x) - D2 • om1) := by
    rw [← hp, hlast1]
    module
  rw [hq0, add_zero] at e
  have hmem : (D1 * R2 - D2 * R1) • f1 (Fin.last _) ∈ Xs (S := VS D) f1 := by
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hy1) (Submodule.smul_mem _ _ hx1')
  have hc := lemC f1 hind hmem
  linear_combination hc

end Scal

end Formalism.L2.SG.Pf.ScalarFramePf
end
end
