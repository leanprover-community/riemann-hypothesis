import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameGenericProjectiveCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMapOfModelHasDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialPrimitiveU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFamiliesThetaSymmetricMinMemberCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInAllCompleteDVRNormalNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTwoLevelsPrimitiveAtTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListRealisedSystemUpToRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemSectionGeneratesFieldFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSymmetricFunctionValuesInGroundField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapCoordsOfSymmetricThetaIsomorphicFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHasDivOfGenericPointProjectiveCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivisorOfForallCompleteDvrPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFamiliesThetaSymmetricMinMemberCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemSectionGeneratesFieldFibresStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalisationProjectiveQuasiFinite

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.CrdMapBC

open GlobalTheory.ProjSpace GlobalTheory.Cartier GlobalTheory.QCoh.Qcqs

theorem secMaps_baseChangeIso {o k : Type} [CommRing o] [CommRing k] (β : o →+* k) (n : ℕ) (j : Fin (n + 1)) :
    SecMaps (baseChangeIso n β) (secPull (coord o n j) (baseChange n β)) (coord k n j) := by
  rintro ⟨i, l⟩
  refine (baseChangeIso_coord n β j i l).trans ?_
  congr 1

theorem pCrd_comp_baseChange {o k A : Type} [CommRing o] [CommRing k] [CommRing A] (β : o →+* k) {n : ℕ}
    (x : Sp A ⟶ PSpace k n) (v : Fin (n + 1) → A) (h : PCrd x v) : PCrd (x ≫ baseChange n β) v := by
  refine (RepBC.secCoord_pull (O1 o n) (coord o n) (baseChange n β) x v).1 ?_
  exact (FibreEmbed.secCoord_iff_of_secMaps (LB.isLB_pull (O1_isLB o n) _) (O1_isLB k n)
    (w := baseChangeIso n β) (fun j => secMaps_baseChangeIso β n j)
    (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord o n) _) (iSup_nonzeroLocus_coord k n)).2 h

theorem exists_map_of_hasDiv : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (β : o →+* k) (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace o n, h ≫ PSpace.str o n = M.s ≫ spMap β ∧ PCrd (M.pt ≫ h) c := by
  intro k Ω o _ _ _ _ β M n c hc
  obtain ⟨h₀, hs, hp⟩ := GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv k Ω M n c hc
  refine ⟨h₀ ≫ baseChange n β, ?_, ?_⟩
  · rw [Category.assoc, baseChange_str, ← Category.assoc, hs]
  · rw [← Category.assoc]
    exact pCrd_comp_baseChange β _ c hp

end GlobalTheory.SiegTh.CrdMapBC
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projSpace_map_of_tuple_hasDivisor : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (β : o →+* k) (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace o n, h ≫ PSpace.str o n = M.s ≫ spMap β ∧ PCrd (M.pt ≫ h) c := by
  atlas_forward_decl GlobalTheory.SiegTh.CrdMapBC.exists_map_of_hasDiv
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.TraitScale

theorem isUnit_natCast {o V : Type} [CommRing o] [CommRing V] [IsDomain V] (f : o →+* FractionRing V)
    (hf : ∀ a, f a ∈ Set.range (algebraMap V (FractionRing V))) {m : ℕ} (hm : IsUnit (m : o)) : IsUnit (m : V) := by
  obtain ⟨u, hu⟩ := hm.exists_right_inv
  obtain ⟨v, hv⟩ := hf u
  refine IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_)
  rw [map_mul, map_natCast, hv, map_one, ← map_natCast f, ← map_mul, hu, map_one]

theorem thList_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m N : ℕ} {K : Type} [Field K] {x₁ x₂ : Sp K ⟶ S} (e : x₁ = x₂) {T : Over S} (h₁ : Over.mk x₁ ⟶ T)
    (h₂ : Over.mk x₂ ⟶ T) (he : h₁.left = h₂.left) (θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T))
    {pt : Fin N → (Over.mk x₁ ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m x₁ (VVRank.pullS G _ h₁ θ) pt c) :
    ∃ pt' : Fin N → (Over.mk x₂ ⟶ G), ThList G L ρ m x₂ (VVRank.pullS G _ h₂ θ) pt' c := by
  subst e
  obtain rfl : h₁ = h₂ := Over.OverMorphism.ext he
  exact ⟨pt, H⟩

theorem level_odd {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    Odd (S.r * S.N) ∧ 3 ≤ S.r * S.N := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  have ho : Odd (S.r * S.N) := by
    rw [hj, ρ.N_eq]
    exact (ρ.n_odd.pow).mul (ρ.n_odd.pow.pow)
  refine ⟨ho, ?_⟩
  have h2 : 2 ≤ S.r * S.N := le_trans S.N_ge (Nat.le_mul_of_pos_left _ S.r_pos)
  obtain ⟨t, ht⟩ := ho
  omega

theorem exists_scale : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (m N : ℕ) (e : Fin N → Ω), Odd m → 3 ≤ m → IsUnit (m : o) → N = m ^ (4 * S.g) → SymE ρ m e → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (emb : Ω →+* FractionRing V), (∀ a : o, emb (algebraMap o Ω a) ∈ Set.range (algebraMap V (FractionRing V))) → ∃ (K : Type) (_ : Field K) (io : FractionRing V →+* K) (N' : ℕ) (c : Fin N → K) (c' : Fin N' → K) (a : K), a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) ∧ (∀ j, io (emb (e j)) = symTup c j) ∧ (∀ x, ∃ b, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2) := by
  intro o Ω _ _ _ _ S ρ m N e hm hm3 hmu hN hE V _ _ _ hV emb hemb
  letI := ρ.P.isAb.comm
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let i : S.R →+* K := (io.comp emb).comp S.R.val.toRingHom
  let y : Sp (FractionRing V) ⟶ Sp S.R := spMap (emb.comp S.R.val.toRingHom)
  have hmV : IsUnit (m : V) := isUnit_natCast (emb.comp (algebraMap o Ω)) hemb hmu
  have hkV : IsUnit ((S.r * S.N : ℕ) : V) := isUnit_natCast (emb.comp (algebraMap o Ω)) hemb S.unit
  have ne : ∀ {k : ℕ}, IsUnit (k : V) → (k : K) ≠ 0 := fun h => by
    have := h.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨hko, hk3⟩ := level_odd ρ
  have hfib : PolFib ρ.P.A ρ.P.L S.g (spMap i ≫ 𝟙 (Sp S.R)) :=
    ρ.g_eq ▸ GlobalTheory.UMin.FibExist.polFib_of_point _ ρ.P K _
  obtain ⟨pt, c, H⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen S.g m N K _
    (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) hm (ne hmV) hN hfib
  obtain ⟨pt', c', H'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen S.g (S.r * S.N) _ K _
    (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) hko (ne hkV) rfl hfib
  have hx : spMap i ≫ 𝟙 (Sp S.R) = spMap io ≫ y := by
    rw [Category.comp_id, ← spMap_comp]
  have H2 : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap io ≫ y) c c' :=
    hx ▸ (⟨_, pt, pt', GlobalTheory.UMin.isGenSec_real_pull o Ω S ρ K i, H, H'⟩ :
      HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap i ≫ 𝟙 (Sp S.R)) c c')
  obtain ⟨P, α, -, hα, hiso⟩ := GlobalTheory.UMin.FibExist.polFib_of_point _ ρ.P (FractionRing V) y
  have hS : (letI := P.isAb.comm; HypS P.A P.L) := by
    letI := P.isAb.comm
    exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ ρ.P.A P.A y α ρ.P.L P.L ρ.P.isLB P.isLB hα hiso ρ.hypS
  obtain ⟨a, ha, h₁, h₂⟩ := GlobalTheory.T.thetaConstants_two_levels_primitive_at_trait _ ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen V hV y P α hα hiso hS K io m (S.r * S.N)
    _ _ c c' hm hm3 hmV hko hk3 hkV H2
  obtain ⟨r₁, r₂⟩ := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o Ω S ρ K i _ pt' c' H'
  refine ⟨K, inferInstance, io, _, c, c', a, ha, h₁, h₂, ?_, r₁, r₂⟩
  have hz : spMap i ≫ 𝟙 (Sp S.R) = spMap (io.comp emb) ≫ spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R) := by
    rw [← Category.assoc, ← spMap_comp]
  obtain ⟨q, Hq⟩ := thList_transport hz _
    ((Over.homMk (spMap (io.comp emb)) rfl : Over.mk (spMap (io.comp emb) ≫ spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R)) ⟶
      Over.mk (spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R))) ≫
      (Over.homMk (spMap S.R.val.toRingHom) rfl :
        Over.mk (spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R)) ⟶ Over.mk (𝟙 (Sp S.R))))
    (spMap_comp _ _) _ H
  rw [← ThetaRuleCompare.pullS_comp] at Hq
  exact hE.2.2 K (io.comp emb) q c Hq

end GlobalTheory.SiegTh.TraitScale
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_scale_thetaConstants_at_trait : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (m N : ℕ) (e : Fin N → Ω), Odd m → 3 ≤ m → IsUnit (m : o) → N = m ^ (4 * S.g) → SymE ρ m e → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (emb : Ω →+* FractionRing V), (∀ a : o, emb (algebraMap o Ω a) ∈ Set.range (algebraMap V (FractionRing V))) → ∃ (K : Type) (_ : Field K) (io : FractionRing V →+* K) (N' : ℕ) (c : Fin N → K) (c' : Fin N' → K) (a : K), a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) ∧ (∀ j, io (emb (e j)) = symTup c j) ∧ (∀ x, ∃ b, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2) := by
  atlas_forward_decl GlobalTheory.SiegTh.TraitScale.exists_scale
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegRev

theorem isIntegralElem_of_forall {V K : Type} [CommRing V] [Field K] (i : V →+* K) {x : K}
    (h : ∀ W : ValuationSubring K, (∀ v, i v ∈ W) → x ∈ W) : i.IsIntegralElem x := by
  letI : Algebra V K := i.toAlgebra
  have hic : IsIntegrallyClosedIn (integralClosure V K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure V K) K)
  have h1 : x ∈ (integralClosure V K).toSubring := by
    by_contra hn
    obtain ⟨W, hW, hxW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn
    exact hxW (h W fun v => hW ((integralClosure V K).algebraMap_mem v))
  exact h1

theorem scale_of_prim {V K : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] [Field K]
    (io : FractionRing V →+* K) (N N' k : ℕ) {J : Type} (c : Fin N → K) (c' : Fin N' → K) (a : K)
    (e : Fin N → FractionRing V) (th : J → FractionRing V) (i : J) (ha : a ≠ 0) (hk : 1 ≤ k)
    (hP : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a))
    (hP' : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a))
    (he : ∀ j, io (e j) = symTup c j) (hth1 : ∀ x, ∃ b, c' x ^ k = io (th b) ^ k)
    (hth2 : ∀ b, ∃ x, c' x ^ k = io (th b) ^ k) (hi : th i ≠ 0)
    (hdiv : ∀ b, th b / th i ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ e' : Fin N → V, (∀ j, algebraMap V (FractionRing V) (e' j) = e j / th i ^ N.factorial) ∧
      ∃ j, IsUnit (e' j) := by
  have hk0 : k ≠ 0 := by omega
  have hti : io (th i) ≠ 0 := (map_ne_zero io).2 hi
  have hW' : ∀ W : ValuationSubring K, (∀ v, (io.comp (algebraMap V (FractionRing V))) v ∈ W) →
      io (th i) / a ∈ W ∧ a / io (th i) ∈ W := by
    intro W hW
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hth2 i
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [div_pow, ← hx, ← div_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW (hP'.1 x)) k
    · obtain ⟨x₀, hx0, hx0i⟩ := hP'.2
      obtain ⟨b₁, hb1⟩ := hth1 x₀
      have hc0 : c' x₀ ≠ 0 := fun h => hx0 (by simp [h])
      have hb10 : io (th b₁) ≠ 0 := by
        intro h0
        apply hc0
        have h2 : c' x₀ ^ k = 0 := by rw [hb1, h0, zero_pow hk0]
        exact (pow_eq_zero_iff hk0).1 h2
      have h1 : a / io (th b₁) ∈ W := by
        refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
        have e0 : (a / io (th b₁)) ^ k = ((c' x₀ / a)⁻¹) ^ k := by
          rw [inv_div, div_pow, div_pow, hb1]
        rw [e0]
        exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW hx0i) k
      have h2 : io (th b₁) / io (th i) ∈ W := by
        obtain ⟨v, hv⟩ := hdiv b₁
        have h3 := hW v
        rwa [RingHom.comp_apply, hv, map_div₀] at h3
      have e1 : a / io (th i) = a / io (th b₁) * (io (th b₁) / io (th i)) := by
        field_simp
      rw [e1]
      exact mul_mem h1 h2
  have hPt : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / io (th i)) := by
    refine ⟨fun b => isIntegralElem_of_forall _ fun W hW => ?_, ?_⟩
    · have e1 : c b / io (th i) = c b / a * (a / io (th i)) := by field_simp
      show c b / io (th i) ∈ W
      rw [e1]
      exact mul_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW (hP.1 b)) (hW' W hW).2
    · obtain ⟨b₀, hb0, hb0i⟩ := hP.2
      have hc0 : c b₀ ≠ 0 := fun h => hb0 (by simp [h])
      refine ⟨b₀, div_ne_zero hc0 hti, isIntegralElem_of_forall _ fun W hW => ?_⟩
      have e1 : (c b₀ / io (th i))⁻¹ = io (th i) / a * (c b₀ / a)⁻¹ := by field_simp
      show (c b₀ / io (th i))⁻¹ ∈ W
      rw [e1]
      exact mul_mem (hW' W hW).1 (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW hb0i)
  have hsym : ∀ j, io (e j / th i ^ N.factorial) = symTup (fun b => c b / io (th i)) j := by
    intro j
    rw [map_div₀, map_pow, he]
    have e2 : (fun b => c b / io (th i)) = fun b => (io (th i))⁻¹ * c b := by
      funext b
      rw [div_eq_inv_mul]
    rw [e2, GlobalTheory.UMin.PrimCmp.symTup_mul, inv_pow, inv_mul_eq_div]
  exact GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_primitive_unit V K io N (fun b => c b / io (th i)) (fun j => e j / th i ^ N.factorial) hPt hsym

end GlobalTheory.SiegRev

theorem GlobalTheory.SiegTh.sameScale_theta_symE : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (e : Fin (N + 1) → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv S.th → SymE ρ m e → SameScale M S.th e (N + 1).factorial := by
  intro g n hg hn hno F W hW P rig m N f hTh o Ω _ _ _ _ β S ρ u hSys M e hNorm hDiv hSym z i hi
  obtain ⟨-, -, -, hmo, hm3, hmu, hN, -, -⟩ := hTh
  obtain ⟨-, -, hSg, -, -⟩ := hSys
  haveI : IsNoetherianRing o := by
    haveI := ArithBase.ded (o := o) (Ω := Ω)
    infer_instance
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : IsNoetherianRing (M.O z) := RatModel.isNoetherianRing_O M z
  haveI : IsIntegrallyClosed (M.O z) := RatModel.isIntegrallyClosed_O hNorm z
  haveI : CharZero (M.O z) := ⟨fun a b h => by
    have := congrArg Subtype.val h
    simpa using this⟩
  have hmo' : IsUnit (m : o) := by simpa using hmu.map β
  have hNe : N + 1 = m ^ (4 * S.g) := by rw [hN, hSg]
  have hk : 1 ≤ (S.r * S.N) ^ 2 := Nat.one_le_iff_ne_zero.2
    (pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)))
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
      ∀ φ : M.O z →+* V, Function.Injective φ →
      ∃ emb : Ω →+* FractionRing V,
        (∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r)) ∧
        ∃ e' : Fin (N + 1) → V,
          (∀ j, algebraMap V (FractionRing V) (e' j) = emb (e j / S.th i ^ (N + 1).factorial)) ∧
          ∃ j, IsUnit (e' j) := by
    intro V _ _ _ hV φ hφ
    haveI : IsDiscreteValuationRing V := hV.1
    have hg : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
      (IsFractionRing.injective V (FractionRing V)).comp hφ
    let emb : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O z) hg
    have hemb : ∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r) := fun r =>
      IsFractionRing.lift_algebraMap (A := M.O z) hg r
    have hmemO : ∀ x ∈ M.O z, emb x ∈ Set.range (algebraMap V (FractionRing V)) := fun x hx =>
      ⟨φ ⟨x, hx⟩, (hemb ⟨x, hx⟩).symm⟩
    have ho : ∀ a : o, emb (algebraMap o Ω a) ∈ Set.range (algebraMap V (FractionRing V)) := fun a =>
      hmemO _ ((M.O z).algebraMap_mem a)
    obtain ⟨K, _, io, N', c, c', a, ha, hP, hP', he, h1, h2⟩ :=
      GlobalTheory.T.exists_common_scale_thetaConstants_at_trait o Ω S ρ m (N + 1) e hmo hm3 hmo' hNe hSym V hV emb ho
    have hr : ∀ b, emb (S.th b) / emb (S.th i) ∈ Set.range (algebraMap V (FractionRing V)) := fun b => by
      rw [← map_div₀]
      exact hmemO _ (hi.2 b)
    obtain ⟨e', he', j, hj⟩ := GlobalTheory.SiegRev.scale_of_prim io (N + 1) N' ((S.r * S.N) ^ 2) c c' a
      (fun j => emb (e j)) (fun b => emb (S.th b)) i ha hk hP hP' he h1 h2 ((map_ne_zero emb).2 hi.1) hr
    refine ⟨emb, hemb, e', fun j => ?_, j, hj⟩
    rw [he', map_div₀, map_pow]
  have hmem : ∀ j, e j / S.th i ^ (N + 1).factorial ∈ M.O z := by
    intro j
    obtain ⟨x, s, hs, hx⟩ := IsFractionRing.div_surjective (A := M.O z) (e j / S.th i ^ (N + 1).factorial)
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hdvd : s ∣ x := GlobalTheory.T.dvd_of_dvd_in_all_completeDVR_normal_noetherian (M.O z) x s hs0 (fun V _ _ _ hV φ hφ => by
      obtain ⟨emb, hemb, e', he', -⟩ := key V hV φ hφ
      have hv := he' j
      rw [← hx, map_div₀, hemb, hemb] at hv
      have hs' : algebraMap V (FractionRing V) (φ s) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 ((map_ne_zero_iff φ hφ).2 hs0)
      refine ⟨e' j, IsFractionRing.injective V (FractionRing V) ?_⟩
      rw [map_mul, hv, mul_div_cancel₀ _ hs'])
    obtain ⟨c, hc⟩ := hdvd
    have hs1 : algebraMap (M.O z) Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    rw [← hx, hc, map_mul, mul_div_cancel_left₀ _ hs1]
    exact c.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (M.O z)
  haveI := hloc
  obtain ⟨emb, hemb, e', he', j, hj⟩ := key V hV φ hφ
  have hj' : e' j = φ ⟨_, hmem j⟩ := IsFractionRing.injective V (FractionRing V) (by rw [he', ← hemb]; rfl)
  have hu : IsUnit (⟨e j / S.th i ^ (N + 1).factorial, hmem j⟩ : M.O z) := isUnit_of_map_unit φ _ (hj' ▸ hj)
  obtain ⟨h0, hinv⟩ := (RatModel.isUnit_O_iff _).1 hu
  have h0' : e j / S.th i ^ (N + 1).factorial ≠ 0 := h0
  have hinv' : (e j / S.th i ^ (N + 1).factorial)⁻¹ ∈ M.O z := hinv
  have hthD : S.th i ^ (N + 1).factorial ≠ 0 := pow_ne_zero _ hi.1
  have hej : e j ≠ 0 := fun h => h0' (by simp [h])
  refine ⟨j, ⟨hej, fun k => ?_⟩, ?_, hmem j⟩
  · have e3 : e k / e j = e k / S.th i ^ (N + 1).factorial * (e j / S.th i ^ (N + 1).factorial)⁻¹ := by
      field_simp
    rw [e3]
    exact mul_mem (hmem k) hinv'
  · simpa only [inv_div] using hinv'

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_pow_eq_unit_mul_symmetricFunction : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (e : Fin (N + 1) → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv S.th → SymE ρ m e → SameScale M S.th e (N + 1).factorial := by
  atlas_forward_decl GlobalTheory.SiegTh.sameScale_theta_symE
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_symE_pCrd : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∃ e : Fin (N + 1) → Ω, SymE ρ m e ∧ ∀ (h : Sp Ω ⟶ PSpace (cycAway n) N), h = spMap (algebraMap S.R Ω) ≫ u ≫ f → PCrd h e := by
  intro g n _ _ _ F W _ P rig m N f hT o Ω _ _ _ hA β S ρ u hS
  obtain ⟨hPg, hPs, hrig, hm, -, hmu, hN, -, hf, -⟩ := hT
  obtain ⟨-, -, hSg, hρs, -⟩ := hS
  haveI : CharZero Ω := hA.char
  have hSB : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  let v : S.R →+* Ω := S.R.val.toRingHom

  obtain ⟨P₀, φ, hg₀, hφ, hL₀⟩ := exists_isPolFibre polBaseChange_holds v ρ.P
  have hφ' : IsGrpPullback P₀.A ρ.P.A (spMap v ≫ 𝟙 (Sp S.R)) φ := by
    simpa using hφ
  have hL₀' : LBIso P₀.L (ρ.P.L.pull φ) := hL₀.symm
  have hfib : PolFib ρ.P.A ρ.P.L (8 * g) (spMap v ≫ 𝟙 (Sp S.R)) :=
    ⟨P₀, φ, by rw [hg₀, ρ.g_eq, hSg], hφ', hL₀'⟩

  have hth : IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := fun s =>
    (ρ.th₁_basis s).exists.elim fun r h => ⟨r 0, fun j => (h j).trans (Fin.sum_univ_one _)⟩
  let θ : SecAt ρ.P.A ρ.P.L (spMap v ≫ 𝟙 (Sp S.R)) := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ v
  have : IsAffine (Over.mk (𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap v ≫ 𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have hθ : IsGenSec ρ.P.A ρ.P.L _ θ := GlobalTheory.EmbPull.isGenSec_pullS ρ.P hSB _ hth

  obtain ⟨e, he⟩ := GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) Ω
    (spMap v ≫ 𝟙 (Sp S.R)) θ hm hN hfib
  have hmΩ : (m : Ω) ≠ 0 := by
    let κ : cycAway n →+* S.R := (Spec.preimage (u ≫ F.s)).hom
    have := (hmu.map κ).map v
    rw [map_natCast, map_natCast] at this
    exact this.ne_zero
  refine ⟨e, ⟨by rw [hSg]; exact hN, hmΩ, he⟩, fun h hh => ?_⟩

  obtain ⟨ψ, hψ, hLψ⟩ := GlobalTheory.T.sharp_polarization_unique_pullback g n F W ρ.P P u (𝟙 F.X) u (Category.comp_id u) hρs hPs
  have hα : IsGrpPullback P₀.A P.A ((spMap v ≫ u) ≫ 𝟙 F.X) (φ ≫ ψ) := by
    simpa using hφ.comp hψ
  have hLα : LBIso P₀.L (P.L.pull (φ ≫ ψ)) :=
    LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB φ) (pull_isLB P.isLB _) hL₀'
      (LBIso.trans (pull_isLB ρ.P.isLB φ) (pull_isLB (pull_isLB P.isLB ψ) φ) (pull_isLB P.isLB _)
        (RigidBundleGlue.LBIso.pull hLψ φ) (GlobalTheory.UMin.FibMove.lbIso_pull_comp P.isLB ψ φ).symm)
  have key := GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre F.X P.A P.L rig P.isLB hrig (8 * g) m N (cycAway n) F.X (𝟙 F.X) f (Sp S.R) ρ.P.A ρ.P.L ρ.rig
    Ω (spMap v ≫ u) (spMap v ≫ 𝟙 (Sp S.R)) P₀ (φ ≫ ψ) φ θ e hm hN hf ρ.P.isLB ρ.rig_gen
    (by rw [hg₀, ρ.g_eq, hSg]) hα hLα hφ' hL₀' hθ he
  rw [hh, show algebraMap S.R Ω = v from RingHom.ext fun _ => rfl]
  simpa [Category.assoc] using key

end GlobalTheory.SiegTh
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∃ e : Fin (N + 1) → Ω, SymE ρ m e ∧ ∀ (h : Sp Ω ⟶ PSpace (cycAway n) N), h = spMap (algebraMap S.R Ω) ≫ u ≫ f → PCrd h e := by
  atlas_forward_decl GlobalTheory.SiegTh.exists_symE_pCrd
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.ThInt

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

theorem thetaInt : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (h : M.Z ⟶ PSpace (cycAway n) N), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ h = spMap S.R.val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  intro g n hg hn hno F W hW P rig m N f hTh o Ω _ _ _ _ β S ρ u hSys M h hnorm hpt
  obtain ⟨e, hSym, hCrd⟩ := GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords g n hg hn hno F W hW P rig m N f hTh o Ω β S ρ u hSys
  have hCrd' : PCrd (M.pt ≫ h) e := by
    rw [hpt]; exact hCrd _ rfl
  have hDe : M.HasDiv e := GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords o Ω (cycAway n) M N h e hCrd'
  obtain ⟨-, -, -, hm, hm3, hmu, hNm, -, -⟩ := hTh
  obtain ⟨-, -, hSg, -, -⟩ := hSys
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI : CharZero Ω := ArithBase.char o
  haveI : NeZero (S.r * S.N) := ⟨by have := S.r_pos; have := S.N_ge; positivity⟩
  letI := ρ.P.isAb.comm
  obtain ⟨j, hj1, hr⟩ := ρ.r_eq
  have hnodd := ρ.n_odd
  have hnp := ρ.n_prime
  have hrNodd : Odd (S.r * S.N) := by
    rw [hr, ρ.N_eq]; exact hnodd.pow.mul hnodd.pow.pow
  have hrN3 : 3 ≤ S.r * S.N := by
    have hn3 : 3 ≤ ρ.n := by
      have := hnp.two_le
      rcases hnodd with ⟨k, hk⟩
      omega
    have h1 : ρ.n ≤ S.r := by rw [hr]; exact Nat.le_self_pow (by omega) _
    have h2 : 1 ≤ S.N := by have := S.N_ge; omega
    nlinarith
  refine GlobalTheory.T.hasDivisor_of_forall_complete_dvr_points o Ω M S.Gam (Fin (N + 1)) S.th e (N + 1).factorial (Nat.factorial_pos _) hnorm hDe ?_
  intro V _ _ _ hV ξ emb hξ j₀ hj₀ hint
  haveI : IsDiscreteValuationRing V := ((GlobalTheory.LN.cDvr_iff V).1 hV).1
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let val : S.R →+* Ω := S.R.val.toRingHom
  let i₀ : S.R →+* FractionRing V := emb.comp val
  let iK : S.R →+* K := io.comp i₀
  let i' : Ω →+* K := io.comp emb
  let σ : o →+* V := (Spec.preimage (ξ ≫ M.s)).hom
  have hmV : IsUnit (m : V) := by
    have h1 : IsUnit (m : o) := by rw [← map_natCast β]; exact hmu.map β
    rw [← map_natCast σ]; exact h1.map σ
  have hrNV : IsUnit ((S.r * S.N : ℕ) : V) := by rw [← map_natCast σ]; exact S.unit.map σ
  have hmK : (m : K) ≠ 0 := by
    have := hmV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  have hrNK : ((S.r * S.N : ℕ) : K) ≠ 0 := by
    have := hrNV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  let y : Sp (FractionRing V) ⟶ Sp S.R := spMap i₀
  obtain ⟨P', φ, gp, hL'⟩ := GlobalTheory.UPoinc.exists_pol_baseChange ρ.P y
  letI := P'.isAb.comm
  have hS' : HypS P'.A P'.L :=
    GlobalTheory.T.lineBundleSymmetry_hypothesis_base_change _ _ ρ.P.A P'.A y φ ρ.P.L P'.L ρ.P.isLB P'.isLB gp hL' ρ.hypS
  have hPF0 : PolFib ρ.P.A ρ.P.L (8 * g) (𝟙 (Sp S.R)) :=
    ⟨ρ.P, 𝟙 _, by rw [ρ.g_eq, hSg], grpPullback_self _, GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB⟩
  have hPFK : PolFib ρ.P.A ρ.P.L (8 * g) (spMap iK ≫ 𝟙 (Sp S.R)) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp S.R) ρ.P.A ρ.P.L ρ.P.A ρ.P.L (𝟙 _) (𝟙 _) ρ.P.isLB ρ.P.isLB (grpPullback_self _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB) (8 * g) S.R (𝟙 _)).2 K iK hPF0
  let θK := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ iK
  obtain ⟨pt, c, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) K
    (spMap iK ≫ 𝟙 (Sp S.R)) θK hm hmK hNm hPFK
  obtain ⟨pt', c', hc'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) (S.r * S.N)
    ((S.r * S.N) ^ (4 * (8 * g))) K (spMap iK ≫ 𝟙 (Sp S.R)) θK hrNodd hrNK rfl hPFK
  have hgen := GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres o Ω S ρ K iK
  have hxy : spMap io ≫ y = spMap iK ≫ 𝟙 (Sp S.R) := by
    rw [Category.comp_id]; exact spMap_comp_ring i₀ io
  have h2 : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap io ≫ y) c c' := by
    rw [hxy]; exact ⟨θK, pt, pt', hgen, hc, hc'⟩
  obtain ⟨a, ha, hp1, hp2⟩ := GlobalTheory.T.thetaConstants_two_levels_primitive_at_trait (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen V hV y P' φ gp hL' hS' K io
    m (S.r * S.N) (N + 1) _ c c' hm hm3 hmV hrNodd hrN3 hrNV h2
  have hreal := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o Ω S ρ K iK _ pt' c' hc'
  have hlist : ∃ pt'' : Fin (N + 1) → (Over.mk (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R))) ⟶ ρ.P.A),
      ThList ρ.P.A ρ.P.L ρ.rig m (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R)))
        (SecAt.pull ρ.P.A ρ.P.L (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ val) i') pt'' c := by
    simp only [SecAt.pull]
    rw [pullS_comp ρ.P.A ρ.P.isLB]
    refine thList_congr ρ.th₁ ?_ (Over.homMk (spMap iK) rfl) _ ?_ hc
    · rw [Category.comp_id, Category.comp_id]; exact (spMap_comp_ring val i').symm
    · simp only [Over.comp_left, Over.homMk_left]; exact (spMap_comp_ring val i').symm
  obtain ⟨pt'', hpt''⟩ := hlist
  have hsym : ∀ j, io (emb (e j)) = symTup c j := fun j => by unfold SymE SymAt at hSym; exact hSym.2.2 K i' pt'' c hpt'' j
  have hj₀' : emb (e j₀) ≠ 0 := (map_ne_zero emb).2 hj₀
  have hint' : ∀ j, emb (e j) / emb (e j₀) ∈ Set.range (algebraMap V (FractionRing V)) := fun j => by
    rw [← map_div₀]; exact hint j
  obtain ⟨H1, b, hb, H2⟩ := GlobalTheory.T.primitive_families_thetaSymmetric_min_member_compare V K io (N + 1) ((S.r * S.N) ^ (4 * (8 * g))) ((S.r * S.N) ^ 2) S.Gam c c' a
    (fun j => emb (e j)) (fun b => emb (S.th b)) ha (Nat.one_le_pow _ _ (by omega)) hp1 hp2 hsym hreal.1 hreal.2 j₀ hj₀'
    hint'
  refine ⟨fun b' => ?_, b, fun h0 => hb (by rw [h0, map_zero]), ?_⟩
  · rw [map_div₀, map_pow]; exact H1 b'
  · rw [map_div₀, map_pow]; exact H2

end GlobalTheory.SiegTh.ThInt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelThetaConstants_projectively_integral : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (h : M.Z ⟶ PSpace (cycAway n) N), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ h = spMap S.R.val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  atlas_forward_decl GlobalTheory.SiegTh.ThInt.thetaInt
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegOpen

theorem isIso_stalkMap_of_isHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M M' : RatModel o Ω}
    {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' (AlgHom.id o Ω) f) :
    IsDominant f ∧ IsIso (f.stalkMap (genericPoint M'.Z)) := by
  have hid : spMap (AlgHom.id o Ω).toRingHom ≫ M.pt = M.pt :=
    (congrArg (· ≫ M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  have : IsDominant (M'.pt ≫ f) := by
    rw [hf, hid]; infer_instance
  have hd : IsDominant f := IsDominant.of_comp M'.pt f
  refine ⟨hd, ?_⟩
  have hz : f (genericPoint M'.Z) = genericPoint M.Z := GlobalTheory.apply_genericPoint_of_isDominant f
  have key : ∀ a, M'.stalkHom (genericPoint M'.Z) (f.stalkMap (genericPoint M'.Z) a) =
      M.stalkHom (f (genericPoint M'.Z)) a := by
    intro a
    obtain ⟨U, hzU, s, rfl⟩ := M.Z.presheaf.germ_exist a
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (M'.stalkHom_germ (U := f ⁻¹ᵁ U) hzU _).trans ((hf.valF_app ⟨_, hzU⟩ s).trans (M.stalkHom_germ hzU s).symm)
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b h => M.stalkHom_injective _ ?_, fun b => ?_⟩
  · rw [← key, ← key, h]
  · have hx : M'.stalkHom (genericPoint M'.Z) b ∈ M.O (f (genericPoint M'.Z)) := by
      rw [hz, M.O_genericPoint]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := (M.stalkEquiv _).surjective ⟨_, hx⟩
    refine ⟨a, M'.stalkHom_injective _ ?_⟩
    rw [key]
    exact congrArg Subtype.val ha

end GlobalTheory.SiegOpen

namespace GlobalTheory.SiegOpen

theorem level_openImmersion : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → QFin f → ∀ (Y X : RatModel o Ω) (q : Y.Z ⟶ F.X), LevAt F β u Y q → X.IsNm S.th → Geo.Tor.IsNormalScheme X.Z → ∃ d : Y.Z ⟶ X.Z, X.IsHom Y (AlgHom.id o Ω) d ∧ IsOpenImmersion d := by
  intro g n hg hn hodd F W hW P rig m N f hTh o Ω _ _ _ _ β S ρ u hSys hQ Y X q hLev hNm hXn

  have hYdiv : Y.HasDiv S.th := GlobalTheory.T.siegelThetaConstants_projectively_integral g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys Y (q ≫ f)
    hLev.1 (by rw [← Category.assoc, hLev.2.2.2.2, Category.assoc])

  obtain ⟨d, hd⟩ := hNm.exists_isHom (M' := Y) (φ := AlgHom.id o Ω) hYdiv (RatModel.isIntegrallyClosed_O hLev.1)
  refine ⟨d, hd, ?_⟩
  have hid : spMap (AlgHom.id o Ω).toRingHom ≫ X.pt = X.pt :=
    (congrArg (· ≫ X.pt) (Spec.map_id _)).trans (Category.id_comp _)
  have hYd : Y.pt ≫ d = X.pt := hd.trans hid

  obtain ⟨e, hSymE, hPe⟩ := GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys
  have hSame := GlobalTheory.T.thetaConstant_pow_eq_unit_mul_symmetricFunction g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys X e hXn hNm.1 hSymE
  have hXe : X.HasDiv e := fun z => by
    obtain ⟨i, hi⟩ := hNm.1 z
    obtain ⟨j, hj, -⟩ := hSame z i hi
    exact ⟨j, hj⟩
  obtain ⟨hX, hXs, hXP⟩ := GlobalTheory.T.exists_projSpace_map_of_tuple_hasDivisor o Ω (cycAway n) β X N e hXe
  have hfs : f ≫ PSpace.str (cycAway n) N = F.s := hTh.2.2.2.2.2.2.2.1

  have heq : d ≫ hX = q ≫ f := by
    refine GlobalTheory.T.eq_of_same_generic_projective_coords (cycAway n) N Y.Z (Y.s ≫ spMap β) (d ≫ hX) (q ≫ f) Ω Y.pt e ?_ ?_ Y.gen ?_ ?_
    · rw [Category.assoc, hXs, ← Category.assoc, hd.inducedModelMorphism_comp_structureMap]
    · rw [Category.assoc, hfs, hLev.2.2.2.1]
    · rw [← Category.assoc, hYd]; exact hXP
    · rw [← Category.assoc, hLev.2.2.2.2]; exact hPe _ rfl

  have : LocallyOfFiniteType F.s := by
    haveI := F.smooth
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
    infer_instance
  have : LocallyOfFiniteType (f ≫ PSpace.str (cycAway n) N) := by rw [hfs]; assumption
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (PSpace.str (cycAway n) N)
  haveI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (GlobalTheory.SiegMin.finite_preimage_singleton_of_qFin f hQ)
  haveI : IsFinite q := hLev.2.1
  haveI : LocallyQuasiFinite (d ≫ hX) := by rw [heq]; infer_instance
  haveI : LocallyQuasiFinite d := LocallyQuasiFinite.of_comp d hX

  haveI := Y.sep
  haveI := Y.qc
  haveI := Y.lft
  haveI := X.sep
  haveI : IsSeparated (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : QuasiCompact (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : LocallyOfFiniteType (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : IsSeparated d := IsSeparated.of_comp d X.s
  haveI : QuasiCompact d := QuasiCompact.of_comp d X.s
  haveI : LocallyOfFiniteType d := locallyOfFiniteType_of_comp d X.s
  obtain ⟨h1, h2⟩ := isIso_stalkMap_of_isHom hd

  exact GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap d fun z => (hXn z).2

end GlobalTheory.SiegOpen
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_openImmersion_normalisedThetaClosure : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → QFin f → ∀ (Y X : RatModel o Ω) (q : Y.Z ⟶ F.X), LevAt F β u Y q → X.IsNm S.th → Geo.Tor.IsNormalScheme X.Z → ∃ d : Y.Z ⟶ X.Z, X.IsHom Y (AlgHom.id o Ω) d ∧ IsOpenImmersion d := by
  atlas_forward_decl GlobalTheory.SiegOpen.level_openImmersion
end
