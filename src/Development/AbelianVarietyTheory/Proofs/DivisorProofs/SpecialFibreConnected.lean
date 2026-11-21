import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickFibIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEqOfBasicOpenEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase

section
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_of_clopen : ∀ (X : Scheme.{0}) (U : Set X), IsClopen U → ∃ e : Γ(X, ⊤), e * e = e ∧ ((X.basicOpen e : X.Opens) : Set X) = U := by
  first | exact @GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen | exact GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen | (intros; apply GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_eq_of_basicOpen_eq' : ∀ (X : Scheme.{0}) (e e' : Γ(X, ⊤)), e * e = e → e' * e' = e' → X.basicOpen e = X.basicOpen e' → e = e' := by
  first | exact @GlobalTheory.idempotent_eq_of_basicOpen_eq | exact GlobalTheory.idempotent_eq_of_basicOpen_eq | (intros; apply GlobalTheory.idempotent_eq_of_basicOpen_eq <;> assumption)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

namespace GlobalTheory.SpecialConn

section
variable {X₁ X₂ Y : Scheme.{0}} {R₁ R₂ R : Type} [CommRing R₁] [CommRing R₂] [CommRing R]

theorem smodEq_pow_iff {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule A A)] ↔
      Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.Quotient.eq]

theorem app_rs_top (π : X₁ ⟶ Y) (W : Y.Opens) (σ : Γ(Y, ⊤)) :
    (π.app W).hom (rs Y le_top σ) = rs X₁ le_top (π.appTop.hom σ) := by
  have e := congrArg (fun q => q.hom σ) (π.naturality (homOfLE (le_top : W ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

theorem loc_map {f : Y ⟶ Spec (CommRingCat.of R)} {M : LB Y} (P : Perf f M)
    (a : X₁ ⟶ X₂) {π₁ : X₁ ⟶ Y} {π₂ : X₂ ⟶ Y} (hπ : a ≫ π₂ = π₁)
    {f₁ : X₁ ⟶ Spec (CommRingCat.of R₁)} {f₂ : X₂ ⟶ Spec (CommRingCat.of R₂)} {φ : R₂ →+* R₁}
    (w : a ≫ f₂ = f₁ ≫ Spec.map (CommRingCat.ofHom φ)) (v : Fin P.a → R₂) (i : P.I)
    (le : π₁ ⁻¹ᵁ P.W i ≤ a ⁻¹ᵁ (π₂ ⁻¹ᵁ P.W i)) :
    loc P π₁ f₁ (φ ∘ v) i = rs X₁ le ((a.app _).hom (loc P π₂ f₂ v i)) := by
  subst hπ
  refine Eq.trans ?_ (rs_self _ _).symm
  simp only [loc, map_sum, map_mul, app_cst w, Function.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

end

theorem exists_global_of_thick : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [IsProper f]
    [Flat f] (e : ∀ n, Γ(thickFib f n, ⊤)), (∀ n, (thickTr f n).appTop.hom (e (n + 1)) = e n) →
    ∃ s : Γ(Y, ⊤), ∀ n, (thickι f n).appTop.hom s = e n := by
  intro O _ _ _ _ Y f _ _ e he
  obtain ⟨P⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f (Inh.trivLB_isLB Y)
  choose E hE using fun n => P.sec (O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1)) (thickQ O n) _
    (thickι f n) (thickStr f n) (thickFib_isPullback f n)
  let v : ∀ n, Fin P.a → O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) := fun n =>
    ((E n).symm (GlobalTheory.AlgGroup.fnSec (thickι f n) (e n))).1
  have hv0 : ∀ n, (P.D₀.map (thickQ O n)).mulVec (v n) = 0 := fun n => ((E n).symm _).2
  have hvl : ∀ n i, loc P (thickι f n) (thickStr f n) (v n) i = rs _ le_top (e n) := by
    intro n i
    have h := hE n ((E n).symm (GlobalTheory.AlgGroup.fnSec (thickι f n) (e n))) i
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans (rs_rs _ _ _)
  have uniq : ∀ n (x y : {u : Fin P.a → O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) //
      (P.D₀.map (thickQ O n)).mulVec u = 0}),
      (∀ i, loc P (thickι f n) (thickStr f n) x.1 i = loc P (thickι f n) (thickStr f n) y.1 i) → x = y := by
    intro n x y h
    refine (E n).injective (sec_ext _ _ (fun i => thickι f n ⁻¹ᵁ P.W i) (fun i _ => P.ch i)
      (fun i => le_pull _ _ (P.le i)) (fun z => exists_mem P _) fun i => ?_)
    rw [hE n x i, hE n y i]
    exact h i
  have compat : ∀ n, (fun k => thickR O n (v (n + 1) k)) = v n := by
    intro n
    have hk : (P.D₀.map (thickQ O n)).mulVec (fun k => thickR O n (v (n + 1) k)) = 0 := by
      funext j
      have := RingHom.map_mulVec (thickR O n) (P.D₀.map (thickQ O (n + 1))) (v (n + 1)) j
      rw [hv0 (n + 1), Pi.zero_apply, map_zero, Matrix.map_map] at this
      exact this.symm
    refine congrArg Subtype.val (uniq n ⟨_, hk⟩ ⟨v n, hv0 n⟩ fun i => ?_)
    have hle : thickι f n ⁻¹ᵁ P.W i ≤ thickTr f n ⁻¹ᵁ (thickι f (n + 1) ⁻¹ᵁ P.W i) := by
      rw [← thickTr_ι f n]
      exact le_rfl
    have h1 := loc_map P (thickTr f n) (thickTr_ι f n) (thickTr_str f n) (v (n + 1)) i hle
    refine h1.trans ?_
    rw [hvl n i, hvl (n + 1) i, app_rs_top, rs_rs, he n]
  choose x hx using fun n k => Ideal.Quotient.mk_surjective (v n k)
  have step : ∀ n k, x (n + 1) k - x n k ∈ IsLocalRing.maximalIdeal O ^ (n + 1) := by
    intro n k
    have h := congrFun (compat n) k
    rw [← hx (n + 1) k, ← hx n k] at h
    exact Ideal.Quotient.eq.1 h
  have cauchy : ∀ k m n, m ≤ n → x n k - x m k ∈ IsLocalRing.maximalIdeal O ^ (m + 1) := by
    intro k m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rw [sub_self]; exact Ideal.zero_mem _
    | succ n hmn ih =>
      rw [← sub_add_sub_cancel (x (n + 1) k) (x n k) (x m k)]
      exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) (step n k)) ih
  choose w hw using fun k => IsPrecomplete.prec (inferInstance : IsPrecomplete (IsLocalRing.maximalIdeal O) O)
    (f := fun j => x j k) fun {m n} hmn => (smodEq_pow_iff _ _ _ _).2 (Ideal.Quotient.eq.2 (by
      rw [← neg_sub]
      exact neg_mem (Ideal.pow_le_pow_right (Nat.le_succ m) (cauchy k m n hmn))))
  have hwv : ∀ n, (fun k => thickQ O n (w k)) = v n := by
    intro n
    funext k
    have h1 := (smodEq_pow_iff _ _ _ _).1 (hw k (n + 1))
    have h2 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ (n + 1)) (x (n + 1) k) =
        Ideal.Quotient.mk _ (x n k) := Ideal.Quotient.eq.2 (step n k)
    exact h1.symm.trans (h2.trans (hx n k))
  have hw0 : P.D₀.mulVec w = 0 := by
    refine IsHausdorff.StrictMono.funext' (IsLocalRing.maximalIdeal O) (a := fun n => n + 1)
      (fun _ _ h => Nat.add_lt_add_right h 1) fun n j => ?_
    have h := RingHom.map_mulVec (thickQ O n) P.D₀ w j
    have e1 : (thickQ O n) ∘ w = v n := hwv n
    rw [e1, hv0 n] at h
    simpa using h
  obtain ⟨s, hs⟩ := FibreLift.exists_sec_of_ker P w hw0
  refine ⟨s.f PUnit.unit, fun n => ?_⟩
  refine (thickFib f n).sheaf.eq_of_locally_eq' (fun i => thickι f n ⁻¹ᵁ P.W i) ⊤
    (fun i => homOfLE le_top) (fun z _ => TopologicalSpace.Opens.mem_iSup.2 (exists_mem P _)) _ _
    fun i => ?_
  refine (app_rs_top (thickι f n) (P.W i) (s.f PUnit.unit)).symm.trans ?_
  refine Eq.trans ?_ (hvl n i)
  rw [← hwv n]
  refine Eq.trans ?_ (loc_comp P (thickFib_isPullback f n) w i).symm
  exact congrArg _ (hs i)
end GlobalTheory.SpecialConn
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.SpecialConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_flat_adic_sections_lift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [IsProper f] [Flat f] (e : ∀ n, Γ(thickFib f n, ⊤)), (∀ n, (thickTr f n).appTop.hom (e (n + 1)) = e n) → ∃ s : Γ(Y, ⊤), ∀ n, (thickι f n).appTop.hom s = e n := by
  atlas_forward_decl GlobalTheory.SpecialConn.exists_global_of_thick
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.SpecialConn
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

namespace GlobalTheory.SpecialConn

theorem eq_zero_of_thickι (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [IsProper f] [Flat f]
    (s : Γ(Y, ⊤)) (hs : ∀ n, (thickι f n).appTop.hom s = 0) : s = 0 := by
  obtain ⟨P⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f (Inh.trivLB_isLB Y)
  have hid : IsPullback (𝟙 Y) f f (Spec.map (CommRingCat.ofHom (RingHom.id O))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec O (RingHom.id O) Y (𝟙 Y) f hid
  obtain ⟨w, hw⟩ := E.surjective (GlobalTheory.AlgGroup.fnSec (𝟙 Y) s)
  have key : ∀ i, rs Y (le_top : (𝟙 Y) ⁻¹ᵁ P.W i ≤ ⊤) s = loc P (𝟙 Y) f w.1 i := fun i => by
    have e := hE w i
    rw [hw] at e
    exact (rs_rs _ _ s).symm.trans e
  have key₀ : ∀ i, loc₀ P w.1 i = rs Y (le_top : P.W i ≤ ⊤) s := fun i => by
    have := (key i).trans (loc_comp P hid w.1 i)
    exact this.symm
  have hv : ∀ n k, thickQ O n (w.1 k) = 0 := by
    intro n
    have h := thickFib_isPullback f n
    obtain ⟨En, hEn⟩ := P.sec _ (thickQ O n) _ (thickι f n) (thickStr f n) h
    have hk : (P.D₀.map (thickQ O n)).mulVec (thickQ O n ∘ w.1) = 0 := funext fun j => by
      rw [← RingHom.map_mulVec]
      have := congrFun w.2 j
      rw [show P.D₀.mulVec w.1 j = 0 from this, map_zero]
      rfl
    have hz : (P.D₀.map (thickQ O n)).mulVec (0 : Fin P.a → _) = 0 := Matrix.mulVec_zero _
    have hloc : ∀ i, loc P (thickι f n) (thickStr f n) (thickQ O n ∘ w.1) i = 0 := fun i => by
      rw [loc_comp P h, key₀ i]
      have e₃ := congrArg (fun q => q.hom s) ((thickι f n).naturality (homOfLE (le_top : P.W i ≤ ⊤)).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e₃
      refine e₃.trans ?_
      change rs _ _ ((thickι f n).appTop.hom s) = 0
      rw [hs n, map_zero]
    have hloc₀ : ∀ i, loc P (thickι f n) (thickStr f n) (0 : Fin P.a → _) i = 0 := fun i => by
      simp [loc]
    have heq := En.injective (a₁ := ⟨_, hk⟩) (a₂ := ⟨0, hz⟩) (sec_ext _ _
      (fun i => thickι f n ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull _ _ (P.le i))
      (fun y => exists_mem P (thickι f n y)) fun i => by
        rw [hEn, hEn]
        exact (hloc i).trans (hloc₀ i).symm)
    intro k
    exact congrFun (congrArg Subtype.val heq) k
  have hw0 : ∀ k, w.1 k = 0 := fun k => by
    refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal O) inferInstance (w.1 k) fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq_zero_iff_mem.1 (hv n k))
  refine Y.sheaf.eq_of_locally_eq' (fun i => P.W i) ⊤ (fun i => homOfLE le_top)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.2 (exists_mem P y)) s 0 fun i => ?_
  change rs Y (le_top : P.W i ≤ ⊤) s = rs Y (le_top : P.W i ≤ ⊤) 0
  rw [map_zero, ← key₀ i]
  simp [loc₀, hw0]

end GlobalTheory.SpecialConn
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.SpecialConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_flat_section_eq_zero_of_thickenings : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [IsProper f] [Flat f] (s : Γ(Y, ⊤)), (∀ n, (thickι f n).appTop.hom s = 0) → s = 0 := by
  atlas_forward_decl GlobalTheory.SpecialConn.eq_zero_of_thickι
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

noncomputable section

namespace GlobalTheory.SpecialConn

theorem range_spec_map_eq {O S : Type} [CommRing O] [IsLocalRing O] [CommRing S] [Nontrivial S] (φ : O →+* S)
    (hφ : ∀ Q : Ideal S, Q.IsPrime → IsLocalRing.maximalIdeal O ≤ Q.comap φ) :
    Set.range (Spec.map (CommRingCat.ofHom φ)) = {IsLocalRing.closedPoint O} := by
  have key : ∀ Q : PrimeSpectrum S, Spec.map (CommRingCat.ofHom φ) Q = IsLocalRing.closedPoint O := by
    intro Q
    refine PrimeSpectrum.ext ?_
    change Q.asIdeal.comap φ = IsLocalRing.maximalIdeal O
    exact le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap φ).ne_top) (hφ _ Q.2)
  ext x
  constructor
  · rintro ⟨Q, rfl⟩
    exact key Q
  · rintro rfl
    obtain ⟨M, hM⟩ := Ideal.exists_maximal S
    exact ⟨⟨M, hM.isPrime⟩, key _⟩

theorem range_thickQ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Set.range (Spec.map (CommRingCat.ofHom (thickQ O n))) = {IsLocalRing.closedPoint O} := by
  haveI : Nontrivial (O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal O).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  refine range_spec_map_eq _ fun Q hQ => ?_
  have h : IsLocalRing.maximalIdeal O ^ (n + 1) ≤ Q.comap (thickQ O n) := fun a ha => by
    change Ideal.Quotient.mk _ a ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact Q.zero_mem
  exact (Ideal.IsPrime.comap (thickQ O n)).le_of_pow_le h

theorem range_residue (O : Type) [CommRing O] [IsLocalRing O] :
    Set.range (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) = {IsLocalRing.closedPoint O} := by
  refine range_spec_map_eq _ fun Q hQ a ha => ?_
  change IsLocalRing.residue O a ∈ Q
  rw [(IsLocalRing.residue_eq_zero_iff a).2 ha]
  exact Q.zero_mem

theorem connectedSpace_specialFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)), IsIntegral Y → (∀ z : Y, IsIntegrallyClosed (Y.presheaf.stalk z)) → IsProper f → Flat f → ConnectedSpace (specialFibre f) := by
  intro O _ _ _ _ Y f hY _ hP hF
  have hT : Set.range (specialι f) = f ⁻¹' {IsLocalRing.closedPoint O} := by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    rw [range_residue] at h
    exact h
  have hTn : ∀ n, Set.range (thickι f n) = f ⁻¹' {IsLocalRing.closedPoint O} := fun n => by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (thickQ O n)))
    rw [range_thickQ] at h
    exact h
  have hne : ∃ y : Y, f y = IsLocalRing.closedPoint O := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    let η : Spec (.of O) := ⟨⊥, Ideal.bot_prime⟩
    have hgen : η ⤳ f y := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    obtain ⟨y', -, hy'⟩ := (Flat.generalizingMap f) hgen
    have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hsp : η ⤳ IsLocalRing.closedPoint O :=
      (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    exact hsp.mem_closed hc ⟨y', hy'⟩
  obtain ⟨y₀, hy₀⟩ := hne
  have hy₀' : y₀ ∈ Set.range (specialι f) := by rw [hT]; exact hy₀
  obtain ⟨z₀, -⟩ := hy₀'
  haveI : Nonempty (specialFibre f) := ⟨z₀⟩
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  haveI : IsClosedImmersion (specialι f) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))))
  have hcl : Topology.IsClosedEmbedding (specialι f) := (specialι f).isClosedEmbedding
  refine { toPreconnectedSpace := preconnectedSpace_iff_clopen.2 fun U hU => ?_, toNonempty := ‹_› }
  by_contra hcon
  push_neg at hcon
  obtain ⟨hU0, hU1⟩ := hcon
  obtain ⟨u, hu⟩ := hU0
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ U := by
    by_contra h
    push_neg at h
    exact hU1 (Set.eq_univ_of_forall h)
  let A := specialι f '' U
  let B := specialι f '' Uᶜ
  have hA : IsClosed A := hcl.isClosedMap _ hU.1
  have hB : IsClosed B := hcl.isClosedMap _ hU.2.isClosed_compl
  have hpt : ∀ n (z : specialFibre f), ∃ x, thickι f n x = specialι f z := fun n z => by
    have : specialι f z ∈ Set.range (thickι f n) := by rw [hTn, ← hT]; exact ⟨z, rfl⟩
    exact this
  have hAB : ∀ n, (thickι f n ⁻¹' A)ᶜ = thickι f n ⁻¹' B := by
    intro n
    ext x
    obtain ⟨z, hz⟩ : thickι f n x ∈ Set.range (specialι f) := by rw [hT, ← hTn n]; exact ⟨x, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, A, B, Set.mem_image]
    constructor
    · intro h
      exact ⟨z, fun hzU => h ⟨z, hzU, hz⟩, hz⟩
    · rintro ⟨w, hw, hw'⟩ ⟨w', hw'U, hw''⟩
      exact hw (hcl.injective (hw''.trans hw'.symm) ▸ hw'U)
  have hclo : ∀ n, IsClopen (thickι f n ⁻¹' A) := fun n =>
    ⟨hA.preimage (thickι f n).continuous,
      by rw [← isClosed_compl_iff, hAB n]; exact hB.preimage (thickι f n).continuous⟩
  choose e he hbe using fun n => GlobalTheory.T.exists_idempotent_of_clopen _ _ (hclo n)
  have hcomp : ∀ n, (thickTr f n).appTop.hom (e (n + 1)) = e n := by
    intro n
    refine GlobalTheory.T.idempotent_eq_of_basicOpen_eq' _ _ _ (by rw [← map_mul, he]) (he n) ?_
    refine TopologicalSpace.Opens.ext ?_
    rw [← Scheme.Hom.preimage_basicOpen_top, hbe n]
    change thickTr f n ⁻¹' ((Scheme.basicOpen _ (e (n + 1)) : Set _)) = _
    rw [hbe (n + 1), ← Set.preimage_comp, ← thickTr_ι f n]
    rfl
  obtain ⟨s, hs⟩ := GlobalTheory.T.proper_flat_adic_sections_lift O Y f e hcomp
  have hss : s * s = s := by
    have := GlobalTheory.T.proper_flat_section_eq_zero_of_thickenings O Y f (s * s - s) fun n => by rw [map_sub, map_mul, hs, he, sub_self]
    exact sub_eq_zero.1 this
  have h01 : s = 0 ∨ s = 1 := IsIdempotentElem.iff_eq_zero_or_one.1 hss
  obtain ⟨x, hx⟩ := hpt 0 u
  obtain ⟨x', hx'⟩ := hpt 0 u'
  rcases h01 with h0 | h1
  · have e0 : e 0 = 0 := by rw [← hs 0, h0, map_zero]
    have hxA : x ∈ thickι f 0 ⁻¹' A := ⟨u, hu, hx.symm⟩
    rw [← hbe 0, e0, Scheme.basicOpen_zero] at hxA
    exact hxA
  · have e1 : e 0 = 1 := by rw [← hs 0, h1, map_one]
    have hxA : x' ∈ ((thickFib f 0).basicOpen (e 0) : Set _) := by
      rw [e1, Scheme.basicOpen_one]
      trivial
    rw [hbe 0] at hxA
    obtain ⟨w, hw, hw'⟩ := hxA
    exact hu' (hcl.injective (hw'.trans hx') ▸ hw)

end GlobalTheory.SpecialConn
end
end
