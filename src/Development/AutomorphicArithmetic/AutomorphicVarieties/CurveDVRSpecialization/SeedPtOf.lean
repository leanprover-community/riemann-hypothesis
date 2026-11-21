import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairOverAlgebraicIntegers
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OfForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FlagRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfNear

section
set_option linter.overlappingInstances false

section SlopeTestRemainingChoices

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.W UpperTheory.V.CA UpperTheory.V.AlgebraTools.Det

namespace UpperTheory.V.Pr

private theorem tr_single {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 0 < n) (D : GDet n A G)
    (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  have h1 := ((d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 1
  rw [h, MonoidAlgebra.mapRingHom_single, map_one] at h1
  have h2 := (repApi ρ).2.2.1 hn (MonoidAlgebra.single g 1)
  rw [GDet.tr, h1] at h2
  rw [GDet.tr, h2]
  congr 1
  ext i j; simp [GDet.repAlg]

private theorem prod_smul {K : Type} [CommRing K] {M : Type} [Ring M] [Algebra K M] :
    ∀ {m : ℕ} (c : Fin m → K) (x : Fin m → M), (List.ofFn fun i => c i • x i).prod = (∏ i, c i) • (List.ofFn x).prod
  | 0, _, _ => by simp
  | m + 1, c, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Fin.prod_univ_succ,
      prod_smul (fun i => c i.succ) (fun i => x i.succ), smul_mul_smul_comm]

section Cont

variable {Γ Γ' R R' : Type} [TopologicalSpace Γ] [TopologicalSpace Γ'] [CommRing R] [CommRing R']

private theorem ac_mul {I : Ideal R} {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) :
    AdicCont I fun x => f x * g x := fun N => by
  simp only [map_mul]
  exact (hf N).mul (hg N)

private theorem ac_comp {I : Ideal R} {f : Γ → R} (hf : AdicCont I f) {u : Γ' → Γ} (hu : Continuous u) :
    AdicCont I fun x => f (u x) := fun N => (hf N).comp_continuous hu

private theorem ac_map [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ] {f : Γ → R}
    (hf : AdicCont (maximalIdeal R) f) : AdicCont (maximalIdeal R') fun x => φ (f x) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap φ :=
    le_trans (Ideal.pow_right_mono (fun y hy => map_nonunit φ y hy) N) (Ideal.le_comap_pow _ N)
  exact (hf N).comp (Ideal.quotientMap _ φ hle)

private theorem ac_desc {I : Ideal R} {f : Γ → R} {u : Γ' → Γ} (hu : Topology.IsQuotientMap u)
    (hf : AdicCont I fun x => f (u x)) : AdicCont I f := fun N s =>
  hu.isOpen_preimage.1 (hf N s)

end Cont

section Tw

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Frame l (ResidueField O)} {n : ℕ} {G : GFrame l} {r : Resid G O n} (L : TwLink F r)

private theorem κ_map {C K : Type} [CommRing C] [Algebra O C] [CommRing K] [Algebra O K] (j : C →ₐ[O] K) (g : G.G₀) :
    j ((L.κA C g : Cˣ) : C) = (L.κA K g : Kˣ) := j.commutes _

private theorem κ_map_inv {C K : Type} [CommRing C] [Algebra O C] [CommRing K] [Algebra O K] (j : C →ₐ[O] K)
    (g : G.G₀) : j (((L.κA C g)⁻¹ : Cˣ) : C) = ((L.κA K g)⁻¹ : Kˣ) := by
  rw [← map_inv, ← map_inv, κ_map]

variable {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (p : Pair r C)

private noncomputable def tt (g : G.G₀) : C := (((L.κA C g)⁻¹ : Cˣ) : C) * p.D.tr (MonoidAlgebra.single g 1)

private theorem κinv_cont : AdicCont (maximalIdeal C) fun g : G.G₀ => (((L.κA C g)⁻¹ : Cˣ) : C) := by
  have := ac_map (algebraMap O C) (ac_comp L.κ_cont continuous_inv)
  simp only [← map_inv]
  exact this

private theorem tt_cont : AdicCont (maximalIdeal C) (tt L p) := ac_mul (κinv_cont L) (p.cont 1)

private theorem tt_map (hn : 0 < n) {K : Type} [CommRing K] [Algebra O K] (j : C →ₐ[O] K)
    (r0 : G.G₀ →* Matrix (Fin n) (Fin n) K) (h : p.D.map (j : C →+* K) = GDet.ofRep r0) (g : G.G₀) :
    j (tt L p g) = (((L.κA K g)⁻¹ : Kˣ) : K) * (r0 g).trace := by
  rw [tt, map_mul, κ_map_inv, ← tr_single hn p.D _ r0 h]
  rfl

private theorem tt_res (hn : 0 < n) (g : G.G₀) :
    res O C (tt L p g) = ∑ i, ((F.Ψ (L.π g) ^ w n i : (ResidueField O)ˣ) : ResidueField O) := by
  rw [tt_map L p hn (res O C) _ p.red]
  show _ * (diagonal _).trace = _
  rw [trace_diagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [L.chib, ← Units.val_mul]
  congr 1
  show (L.κA _ g)⁻¹ * (_ * L.κA _ g) = _
  rw [mul_comm _ (L.κA _ g), inv_mul_cancel_left]

private theorem π_quot : Topology.IsQuotientMap L.π := by
  haveI : CompactSpace G.G₀ := isCompact_iff_compactSpace.1 (G.η.ker.isClosed_of_isOpen G.η_open).isCompact
  exact L.π_cont.isClosedMap.isQuotientMap L.π_cont L.π_surj

private theorem chi_ex : ∃ χ : ∀ v, Fin n → F.Gv v →* Cˣ, IsPsi O F n (fun v i g => (χ v i g : C)) ∧
    ∀ v i g, χ (L.e v) i (L.lam v g) * L.κA C (G.φ v g) = p.ψ v i g := by
  have key : ∀ v : F.V, ∃ χ : Fin n → F.Gv v →* Cˣ, (∀ i, AdicCont (maximalIdeal C) (fun g => (χ i g : C)) ∧
      ∀ g, res O C (χ i g) = ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O)) ∧
      ∀ u (h : L.e u = v) i g, χ i (h ▸ L.lam u g) * L.κA C (G.φ u g) = p.ψ u i g := fun v => by
    obtain ⟨u, rfl⟩ := L.e.surjective v
    refine ⟨fun i => (p.ψ u i * ((L.κA C).comp (G.φ u))⁻¹).comp (L.lam u).symm.toMulEquiv.toMonoidHom,
      fun i => ⟨?_, fun g => ?_⟩, fun u' h i g => ?_⟩
    · exact ac_comp (ac_mul (p.psi u i).cont (ac_comp (κinv_cont L) (G.φ_cont u))) (L.lam u).symm.continuous
    · obtain ⟨g, rfl⟩ := (L.lam u).surjective g
      have h1 : (L.lam u).symm.toMulEquiv.toMonoidHom (L.lam u g) = g := (L.lam u).symm_apply_apply g
      rw [MonoidHom.comp_apply, h1]
      show res O C ((p.ψ u i g : Cˣ) * (((L.κA C (G.φ u g))⁻¹ : Cˣ) : C)) = _
      rw [map_mul, κ_map_inv, (p.psi u i).red, L.psib, L.chib, ← Units.val_mul, ← L.lam_loc]
      congr 1
      exact mul_inv_cancel_right _ _
    · obtain rfl := L.e.injective h
      have h1 : (L.lam u').symm.toMulEquiv.toMonoidHom (L.lam u' g) = g := (L.lam u').symm_apply_apply g
      rw [MonoidHom.comp_apply, h1]
      exact inv_mul_cancel_right _ _
  choose χ h1 h2 using key
  exact ⟨χ, h1, fun v i g => h2 _ v rfl i g⟩

end Tw

private theorem irr_conj {G K : Type} [Group G] [Field K] {n : ℕ} (r : G →* GL (Fin n) K)
    (a : G → Matrix (Fin n) (Fin n) K) (h : GL (Fin n) K) (H : ∀ g, a g = h * mat r g * h⁻¹) (hr : Af.IsIrr r) :
    MatIrr ⊤ a := by
  intro W hW
  have e : ∀ g, (h : Matrix (Fin n) (Fin n) K) * (r g : Matrix (Fin n) (Fin n) K) = a g * h := fun g => by
    rw [H, Units.inv_mul_cancel_right]; rfl
  rcases hr.2.2 (W.comap (Matrix.toLin' (h : Matrix (Fin n) (Fin n) K))) le_top (fun g v hv => by
    rw [Submodule.mem_comap, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
    exact hW g (Subgroup.mem_top g) _ hv) with h0 | h0
  · refine Or.inl (eq_bot_iff.2 fun v hv => ?_)
    have h1 : ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
        W.comap (Matrix.toLin' (h : Matrix (Fin n) (Fin n) K)) := by
      rw [Submodule.mem_comap, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact hv
    rw [h0, Submodule.mem_bot] at h1
    have h2 := congrArg ((h : Matrix (Fin n) (Fin n) K) *ᵥ ·) h1
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact h2
  · refine Or.inr (eq_top_iff.2 fun v _ => ?_)
    have h1 : ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
        W.comap (Matrix.toLin' (h : Matrix (Fin n) (Fin n) K)) := h0 ▸ Submodule.mem_top
    rwa [Submodule.mem_comap, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1

private theorem main {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] [Algebra ℤ_[l] O] {F : Frame l (ResidueField O)} {n : ℕ} (T : Setup F n)
    {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (p : Pair T.r C) {K : Type} [Field K]
    [IsAlgClosed K] [Algebra O K] (j : C →ₐ[O] K) (hj : Function.Injective j)
    (r : F.G0 →* GL (Fin n) K) (Q : GL (Fin n) K) (hQ : (Q : Matrix (Fin n) (Fin n) K)ᵀ = Q)
    (hform : ∀ g, (r g : Matrix (Fin n) (Fin n) K)ᵀ * (Q : Matrix (Fin n) (Fin n) K) *
      (r (F.conj g) : Matrix (Fin n) (Fin n) K) = Q)
    (h0 : p.D.map (j : C →+* K) = GDet.ofRep (mat (Af.tw (r.comp T.K.π) (T.K.κA K))))
    (hfl : ∀ v, HasFlag ((Af.tw (r.comp T.K.π) (T.K.κA K)).comp (T.G.φ v)) fun i => pushCh (j : C →+* K) (p.ψ v i))
    (hirr : Af.IsIrr r) :
    ∃ ρ' : NRep F n K, MatIrr ⊤ ρ'.r ∧ p.D.map (j : C →+* K) = GDet.ofRep (T.K.tw ρ') := by
  have hn : 0 < n := by have := T.n23; omega
  letI : Algebra C K := (j : C →+* K).toAlgebra
  have hv : ∀ g, mat (Af.tw (r.comp T.K.π) (T.K.κA K)) g = ((T.K.κA K g : Kˣ) : K) • mat r (T.K.π g) :=
    fun g => Af.tw_val _ _ g
  obtain ⟨χ, hχ, hψ⟩ := chi_ex T.K p
  have hb : ∀ g, j (tt T.K p g) = (mat r (T.K.π g)).trace := fun g => by
    rw [tt_map T.K p hn j _ h0, hv, trace_smul, smul_eq_mul, Units.inv_mul_cancel_left]
  let t : F.G0 → C := fun x => tt T.K p (Function.surjInv T.K.π_surj x)
  have ht0 : ∀ x, j (t x) = (mat r x).trace := fun x => by
    have := hb (Function.surjInv T.K.π_surj x)
    rwa [Function.surjInv_eq T.K.π_surj] at this
  have ht : ∀ g, t (T.K.π g) = tt T.K p g := fun g => hj (by rw [ht0, hb])
  have hψ' : ∀ v i g, j (p.ψ v i g : Cˣ) =
      (T.K.κA K (T.G.φ v g) : Kˣ) * j (χ (T.K.e v) i (T.K.lam v g) : Cˣ) := fun v i g => by
    rw [← hψ, Units.val_mul, map_mul, mul_comm, ← κ_map T.K j]
  refine Exists.elim (of_form T.ok T.n23 C K hj (mat r) Q t χ Q.isUnit hQ hform ⟨?_, fun x => ?_⟩ ht0 hχ
    (fun v g => ?_)) fun ρ H => ?_
  · refine ac_desc (π_quot T.K) ?_
    simp only [ht]
    exact tt_cont T.K p
  · obtain ⟨g, rfl⟩ := T.K.π_surj x
    rw [ht, tt_res T.K p hn]
  · obtain ⟨u, rfl⟩ := T.K.e.surjective v
    obtain ⟨g, rfl⟩ : ∃ g' : Fin n → T.G.Gv u, g = fun i => T.K.lam u (g' i) :=
      ⟨fun i => (T.K.lam u).symm (g i), funext fun i => ((T.K.lam u).apply_symm_apply _).symm⟩
    have h1 := (flagRel _ _ (hfl u)).2 g
    have h2 := prod_smul (fun i => ((T.K.κA K (T.G.φ u (g i)) : Kˣ) : K))
      (fun i => mat r (F.loc0 _ (T.K.lam u (g i))) -
        j (χ (T.K.e u) i (T.K.lam u (g i)) : Cˣ) • (1 : Matrix (Fin n) (Fin n) K))
    have h3 := h2.symm.trans (Eq.trans (congrArg (fun f => (List.ofFn f).prod) (funext fun i => by
      rw [smul_sub, T.K.lam_loc, ← hv, smul_smul, ← hψ']
      rfl)) h1)
    exact (IsUnit.smul_eq_zero (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _))).1 h3
  · obtain ⟨h, H1, -, -⟩ := H
    refine ⟨ρ, irr_conj r _ h H1 hirr, h0.trans ((repApi _).2.2.2.2.2.2.2 _ h fun g => ?_)⟩
    show _ = (((T.K.κA K g : Kˣ) : K) • ρ.r (T.K.π g)) * _
    rw [hv, H1, mul_smul_comm, smul_mul_assoc, Units.inv_mul_cancel_right]

end UpperTheory.V.Pr

end SlopeTestRemainingChoices

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix

theorem UpperTheory.universalMaps_point_of_polarized_flagged_rep :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fr.IsCoef l O] [Algebra ℤ_[l] O] {F : Fr.Frame l (ResidueField O)} {n : ℕ} (T : Setup F n) (K' : Type) [Field K'] [IsAlgClosed K'] [Algebra O K'] (x : T.B.B →ₐ[O] K') (r : F.G0 →* GL (Fin n) K') (ρ : T.G.G₀ →* GL (Fin n) K') (Q : GL (Fin n) K') (ψ : ∀ v, Fin n → T.G.Gv v →* K'ˣ), (Q : Matrix (Fin n) (Fin n) K')ᵀ = Q → (∀ g, (r g : Matrix (Fin n) (Fin n) K')ᵀ * (Q : Matrix (Fin n) (Fin n) K') * (r (F.conj g) : Matrix (Fin n) (Fin n) K') = Q) → ρ = tw (r.comp T.K.π) (T.K.κA K') → T.B.u.Maps (x : T.B.B →+* K') (W.GDet.ofRep (W.mat ρ)) ψ → (∀ v, W.HasFlag (ρ.comp (T.G.φ v)) (ψ v)) → IsIrr r → ∃ ρ' : Fr.NRep F n K', MatIrr ⊤ ρ'.r ∧ T.B.u.D.map (x : T.B.B →+* K') = W.GDet.ofRep (T.K.tw ρ') := by
  intro l _ O _ _ _ _ _ F n T K' _ _ _ x r ρ Q ψ hQ hform hρ hx hfl hirr
  subst hρ
  haveI : Alg.IsCO O x.range := Alg.co_quot O _ _ x.rangeRestrict x.rangeRestrict_surjective
  obtain ⟨p, hp⟩ := W.exists_determinantPair_map_of_algHom l T.G O n T.r T.B.B x.range x.rangeRestrict T.B.u
  have hD : p.D.map (x.range.val : x.range →+* K') = T.B.u.D.map (x : T.B.B →+* K') := by
    rw [← hp.1, (CA.d_gmap _).2.1]; rfl
  rw [← hD]
  refine main T p x.range.val Subtype.val_injective r Q hQ hform (hD.trans hx.1) (fun v => ?_) hirr
  have : (fun i => W.pushCh (x.range.val : x.range →+* K') (p.ψ v i)) = ψ v := funext fun i => by
    rw [← hp.2 v i, ← hx.2 v i]; rfl
  rw [this]
  exact hfl v
end

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix
set_option linter.overlappingInstances false

private theorem fac_conj {Ω : Type} [Field Ω] [CharZero Ω] (l : ℕ) (A : ValuationSubring Ω) (g x : G ℚ Ω)
    (hl : ¬ A.valuation (l : Ω) < 1) (hx : x ∈ Ine (F := ℚ) A) :
    ∃ A' : ValuationSubring Ω, ¬ A'.valuation (l : Ω) < 1 ∧ g * x * g⁻¹ ∈ Ine (F := ℚ) A' := by
  have h : IsLift (RingEquiv.refl ℚ) ((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω) := fun q => g.symm.commutes q
  let σ : Ω ≃+* Ω := ((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω)
  have hA : ∀ y : Ω, σ y ∈ A ↔ y ∈ A.comap (σ : Ω →+* Ω) := fun y => by
    rw [ValuationSubring.mem_comap]
    rfl
  refine ⟨A.comap (σ : Ω →+* Ω), ?_, ?_⟩
  · rw [← val_lt_one hA (l : Ω), map_natCast]
    exact hl
  · have hc := conjGal_mem_Ine h hA hx
    convert hc using 1
    ext z
    rfl

theorem UpperTheory.exists_frame_factorization_of_trivial_on_inertia :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} {L : Type} [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) {n : ℕ} (r : G L Ω →* GL (Fin n) (Qbar l)), Continuous r → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A, Ψ (galEmb ℚ L Ω s) = 1 → r s = 1) → ∃ r' : Φ.G0 →* GL (Fin n) (Qbar l), Continuous r' ∧ (∀ s, r' (k.p0 s) = r s) ∧ ∀ P : GL (Fin n) (Qbar l), Sd.IsPair σ r 1 P → ∀ g, (r' g).valᵀ * P.val * (r' (Φ.conj g)).val = P.val := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ Φ k n r hr hine
  have hgal : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L ⊓ η.ker := fun s => by
    have h := galEmb_mem ℚ L Ω s
    rwa [k.gal] at h
  have hmem : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L := fun s => (hgal s).1
  have hq : ∀ s, (k.p0 s : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩ := fun s => rfl
  let q : G L Ω →* Φ.G0 :=
    { toFun := k.p0
      map_one' := by
        apply Subtype.ext
        rw [hq]
        rw [show (⟨galEmb ℚ L Ω 1, hmem 1⟩ : upl Ω L) = 1 from Subtype.ext (map_one _), map_one]
        rfl
      map_mul' := fun s t => by
        apply Subtype.ext
        rw [Subgroup.coe_mul, hq, hq, hq, ← map_mul]
        exact congrArg k.p (Subtype.ext (map_mul _ _ _)) }
  have hqv : ∀ s, ((q s : Φ.G0) : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩ := fun s => rfl
  have hqs : Function.Surjective q := by
    intro x
    obtain ⟨u, hu⟩ := k.p_surj x.val
    have hu1 : (u : G ℚ Ω) ∈ galOf ℚ L Ω := by
      rw [k.gal]
      refine ⟨u.2, MonoidHom.mem_ker.mpr ?_⟩
      rw [← k.del u, hu]
      exact MonoidHom.mem_ker.mp x.2
    rw [← range_galEmb ℚ L Ω] at hu1
    obtain ⟨s, hs⟩ := hu1
    refine ⟨s, Subtype.ext ?_⟩
    rw [hqv, ← hu]
    exact congrArg k.p (Subtype.ext hs)
  have hgc : Continuous (galEmb ℚ L Ω) := (galEmbTop ℚ L Ω).1.continuous
  have hqc : Continuous q := by
    refine continuous_induced_rng.2 ?_
    exact k.p_cont.comp (hgc.subtype_mk hmem)
  have hinj : Function.Injective (galEmb ℚ L Ω) := (galEmbTop ℚ L Ω).1.injective
  have hker : ∀ s, q s = 1 → r s = 1 := by
    intro s hs
    have h1 : (⟨galEmb ℚ L Ω s, hmem s⟩ : upl Ω L) ∈ k.p.ker := by
      rw [MonoidHom.mem_ker, ← hqv, hs]
      rfl
    rw [k.p_ker] at h1
    let H' : Subgroup (upl Ω L) := (r.ker.map (galEmb ℚ L Ω)).comap (upl Ω L).subtype
    have hcl : IsClosed (H' : Set (upl Ω L)) := by
      have hk : IsClosed (r.ker : Set (G L Ω)) := by
        haveI : T2Space (Qbar l) := inferInstance
        haveI : T2Space (Matrix (Fin n) (Fin n) (Qbar l)) :=
          (inferInstance : T2Space (Fin n → Fin n → Qbar l))
        haveI h2 : T2Space (GL (Fin n) (Qbar l)) := inferInstance
        haveI : T1Space (GL (Fin n) (Qbar l)) := @T2Space.t1Space _ _ h2
        exact isClosed_singleton.preimage hr
      have hi : IsClosed ((galEmb ℚ L Ω) '' (r.ker : Set (G L Ω))) :=
        (hk.isCompact.image hgc).isClosed
      exact hi.preimage continuous_subtype_val
    have hX : Subgroup.normalClosure
        {s : upl Ω L | ∃ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 ∧ (s : G ℚ Ω) ∈ Ine B' ∧
          η s = 1 ∧ barChar O Ψ s = 1} ≤ H' := by
      unfold Subgroup.normalClosure
      refine (Subgroup.closure_le _).2 ?_
      intro c hc
      rw [Group.mem_conjugatesOfSet_iff] at hc
      obtain ⟨x, ⟨B', hB'l, hxI, hxη, hxbar⟩, hconj⟩ := hc
      obtain ⟨u, hu⟩ := isConj_iff.mp hconj
      have hcv : (c : G ℚ Ω) = u * x * (u : G ℚ Ω)⁻¹ := by
        rw [← hu, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      obtain ⟨A', hA'l, hcI⟩ := fac_conj l B' u x hB'l hxI
      rw [← hcv] at hcI
      have hcη : η c = 1 := by
        rw [hcv, map_mul, map_mul, hxη, mul_one, ← map_mul, mul_inv_cancel, map_one]
      have hcbar : barChar O Ψ c = 1 := by
        rw [hcv, map_mul, map_mul, hxbar, mul_one, ← map_mul, mul_inv_cancel, map_one]
      have hcgal : (c : G ℚ Ω) ∈ galOf ℚ L Ω := by
        rw [k.gal]
        exact ⟨c.2, hcη⟩
      rw [← range_galEmb ℚ L Ω] at hcgal
      obtain ⟨t, ht⟩ := hcgal
      have hΨ : Ψ c = 1 := k.teich A' hA'l c ⟨hcI, c.2⟩ hcbar
      show (c : G ℚ Ω) ∈ r.ker.map (galEmb ℚ L Ω)
      refine ⟨t, ?_, ht⟩
      show r t = 1
      refine hine A' hA'l t ?_ ?_
      · show galEmb ℚ L Ω t ∈ Ine (F := ℚ) A'
        rw [ht]
        exact hcI
      · rw [ht]
        exact hΨ
    have h2 := (Subgroup.topologicalClosure_minimal _ hX hcl) h1
    obtain ⟨t, ht, hts⟩ := h2
    rw [hinj hts] at ht
    exact ht
  have hle : q.ker ≤ r.ker := fun s hs => hker s hs
  let e := QuotientGroup.quotientKerEquivOfSurjective q hqs
  let r' : Φ.G0 →* GL (Fin n) (Qbar l) := (QuotientGroup.lift q.ker r hle).comp e.symm.toMonoidHom
  have hr'q : ∀ s, r' (q s) = r s := by
    intro s
    have he : e.symm (q s) = (s : G L Ω ⧸ q.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift q.ker r hle (e.symm (q s)) = r s
    rw [he]
    rfl
  have hqq : Topology.IsQuotientMap q := Topology.IsQuotientMap.of_surjective_continuous hqs hqc
  have hr'c : Continuous r' := by
    rw [hqq.continuous_iff]
    convert hr using 1
    funext s
    exact hr'q s
  refine ⟨r', hr'c, fun s => hr'q s, ?_⟩
  intro P hP g
  obtain ⟨s, rfl⟩ := hqs g
  obtain ⟨hσ, hσc⟩ := k.c
  have hs'gal : σ * galEmb ℚ L Ω s * σ⁻¹ ∈ galOf ℚ L Ω := by
    rw [k.gal]
    refine ⟨(upl Ω L).mul_mem ((upl Ω L).mul_mem hσ (hmem s)) ((upl Ω L).inv_mem hσ),
      MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_mul, MonoidHom.mem_ker.mp (hgal s).2, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rw [← range_galEmb ℚ L Ω] at hs'gal
  obtain ⟨s', hs'⟩ := hs'gal
  have hconj : Φ.conj (q s) = q s' := by
    apply Subtype.ext
    rw [show ((Φ.conj (q s) : Φ.G0) : Φ.Γ) = Φ.c * (q s : Φ.Γ) * Φ.c⁻¹ from
      MulAut.conjNormal_apply _ _]
    rw [hqv, hqv, ← hσc, ← map_inv, ← map_mul, ← map_mul]
    apply congrArg k.p
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hs'.symm
  rw [hconj, hr'q, hr'q]
  have h := hP s s' hs'
  rw [MonoidHom.one_apply, Units.val_one, one_smul] at h
  exact h
end

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix

private theorem cyc_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {v : W.Plc F} {A : ValuationSubring Ω} (hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (hA : IsPlaceOver A v) {n : ℤ} (hn : n ≠ 0) : ∃ g ∈ Ine (F := F) A, cycBar F Ω l g ^ n ≠ 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hval : A.valuation (l : Ω) < 1 := by
    have h1 := (hA (l : 𝓞 F)).2 hl
    simpa using h1
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσI, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval u
  let f : ℕ → (F →ₐ[ℚ] Ω) := fun k =>
    ((σ ^ k : Ω ≃ₐ[ℚ] Ω) : Ω →ₐ[ℚ] Ω).comp (IsScalarTower.toAlgHom ℚ F Ω)
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, a < b → f a = f b →
      ∃ k : ℕ, 0 < k ∧ ∀ x : F, (σ ^ k) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro a b hlt he
    refine ⟨b - a, by omega, fun x => ?_⟩
    have hx : (σ ^ a) (algebraMap F Ω x) = (σ ^ b) (algebraMap F Ω x) :=
      congrArg (fun φ : F →ₐ[ℚ] Ω => φ x) he
    have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hb, AlgEquiv.mul_apply] at hx
    exact ((σ ^ a).injective hx).symm
  obtain ⟨k, hk0, hk⟩ : ∃ k : ℕ, 0 < k ∧ ∀ x : F, (σ ^ k) (algebraMap F Ω x) = algebraMap F Ω x := by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact key a b h hfab
    · exact key b a h hfab.symm
  let g : G F Ω := { (σ ^ k : Ω ≃ₐ[ℚ] Ω) with commutes' := hk }
  have hgI : g ∈ Ine (F := F) A := pow_mem hσI k
  refine ⟨g, hgI, fun heq => ?_⟩
  have hr : MulSemiringAction.toRingAut (G F Ω) Ω g =
      MulSemiringAction.toRingAut (G ℚ Ω) Ω (σ ^ k) := RingEquiv.ext fun x => rfl
  have hz : cycZ F Ω l g = u ^ k := by
    show cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω g) = u ^ k
    rw [hr, ← hσu, ← map_pow]
    rfl
  have hinj : Function.Injective
      (Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom : ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l)) :=
    Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
  have h1 : (u ^ k) ^ n = 1 := by
    apply hinj
    rw [map_zpow, map_one]
    have : cycBar F Ω l g = Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom : ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l) (cycZ F Ω l g) := rfl
    rw [← hz, ← this]
    exact heq
  rw [← zpow_natCast, ← zpow_mul] at h1
  exact hu _ (mul_ne_zero (by exact_mod_cast hk0.ne') hn) h1

private theorem w_anti (n : ℕ) : StrictAnti (Fr.w n) := by
  intro i j hij
  have : (i : ℕ) < j := hij
  unfold Fr.w
  split_ifs <;> omega

theorem UpperTheory.diagonal_characters_regular_algebraic_of_inertia_weights :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : W.Plc L} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ (ka : G L Ω →* (Qbar l)ˣ), Sd.IsAlgChar ι ka → ∀ (n m : ℕ), 2 ≤ m → ∀ κ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ, (∀ i (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A → κ i s = cycBar L Ω l s ^ ((m : ℤ) * Fr.w n i)) → (∃ wt : Fin n → W.Emb l w → ℤ, (∀ τ, StrictMono fun j => wt j τ) ∧ ∀ j, W.IsLocAlg h (κ j * ka.comp (Dec (F := L) A).subtype) (wt j)) ∧ ∀ i j, κ i * ka.comp (Dec (F := L) A).subtype ≠ κ j * ka.comp (Dec (F := L) A).subtype * (cycBar L Ω l).comp (Dec (F := L) A).subtype := by
  intro hGAR L Ω _ _ _ _ _ l _ ι A w h hl ka hka n m hm κ hκ
  let cyc : ↥(Dec (F := L) A) →* (Qbar l)ˣ := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  let kaD : ↥(Dec (F := L) A) →* (Qbar l)ˣ := ka.comp (Dec (F := L) A).subtype
  obtain ⟨_, art, χ, a, hart, _, hlad⟩ := hka
  let wk : W.Emb l w → ℤ := fun τ =>
    -a ((ι.toRingHom.comp ↑τ).comp (algebraMap L (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w)))
  have hone : IsOpen (((1 : ↥(Ine (F := L) A) →* (Qbar l)ˣ).ker : Set ↥(Ine (F := L) A))) := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  have hkaW : W.IsLocAlg h kaD wk := by
    by_cases hex : ∃ a, GlobalTheory.LocLanglands.IsLocalArtin h a
    · exact Loc.laHecke h art hart ι χ a ka hlad hex
    · exact ⟨1, hone, fun a' ha' => absurd ⟨a', ha'⟩ hex⟩
  obtain ⟨phk, hphk⟩ := hkaW
  have hc := Loc.laCyc hGAR h hl
  obtain ⟨hmul, hpow, hzero⟩ := Loc.laMul (l := l) h
  have hm0 : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
  have hwt : ∀ j, W.IsLocAlg h (κ j * kaD) (fun τ => -((m : ℤ) * Fr.w n j) + wk τ) := by
    intro j
    let x : ℤ := (m : ℤ) * Fr.w n j
    have h0 : W.IsWtPart h (κ j * cyc ^ (-x)) 0 1 := by
      refine hzero _ _ hone fun σ => ?_
      have hs := hκ j (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ)) σ.2
      rw [MonoidHom.one_apply, mul_one, MonoidHom.mul_apply, MonoidHom.zpow_apply, hs]
      show cycBar L Ω l σ ^ x * cycBar L Ω l σ ^ (-x) = 1
      rw [← zpow_add, add_neg_cancel, zpow_zero]
    have h1 := (hmul _ _ _ _ _ _ h0 (hpow _ _ _ x hc)).1
    have h2 := (hmul _ _ _ _ _ _ h1 hphk).1
    have he : κ j * cyc ^ (-x) * cyc ^ x * kaD = κ j * kaD := by
      rw [mul_assoc (κ j), ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    rw [he] at h2
    refine ⟨1 * 1 ^ x * phk, ?_⟩
    convert h2 using 2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, x]
    ring
  refine ⟨⟨fun j τ => -((m : ℤ) * Fr.w n j) + wk τ, fun τ i j hij => ?_, hwt⟩, ?_⟩
  · have := w_anti n hij
    simp only
    nlinarith
  · intro i j heq
    have hcomm : κ j * kaD * cyc = κ j * cyc * kaD := by
      rw [mul_assoc, mul_comm kaD, ← mul_assoc]
    rw [hcomm] at heq
    have heq' : κ i = κ j * cyc := mul_right_cancel heq
    have hN : (m : ℤ) * Fr.w n i - (m : ℤ) * Fr.w n j - 1 ≠ 0 := by
      intro h0
      have h1 : (m : ℤ) * (Fr.w n i - Fr.w n j) = 1 := by linarith
      have := Int.eq_one_of_mul_eq_one_right hm0.le h1
      omega
    obtain ⟨g, hg, hne⟩ := cyc_ine hl h hN
    apply hne
    let s := Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h ⟨g, hg⟩)
    have hi := hκ i s hg
    have hj := hκ j s hg
    have hs := congrArg (fun f => f s) heq'
    simp only [MonoidHom.mul_apply] at hs
    rw [hi, hj] at hs
    have hs' : cycBar L Ω l g ^ ((m : ℤ) * Fr.w n i) = cycBar L Ω l g ^ ((m : ℤ) * Fr.w n j) * cycBar L Ω l g := hs
    rw [zpow_sub, zpow_sub, hs', zpow_one]
    group
end

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open Polynomial
open scoped Matrix

set_option linter.overlappingInstances false

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime]















variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {n : ℕ} {ka : G L Ω →* (Qbar l)ˣ}

private def prT (R : CReal k c₁ f n ka) : G L Ω →* R.T.G.G₀ := R.V.pr



end SlopeTestRemainingChoices
end
