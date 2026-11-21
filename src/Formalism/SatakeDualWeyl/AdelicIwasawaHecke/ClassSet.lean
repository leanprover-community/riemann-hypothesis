import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEasy
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEquiv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
import Formalism.HermitianLattices.HermitianLatticesProofs.ShortVectors
import Formalism.HermitianLattices.HermitianLatticesProofs.FinIntermediate
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomOfTrace

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG Formalism.UG.CS

theorem csAsm_hform_smul_right {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    (J : Matrix n n E) (c : E) (y x : n → E) :
    hform σ J y (c • x) = c * hform σ J y x := by
  unfold Formalism.UG.hform
  simp [Matrix.mulVec_smul, dotProduct_smul, Finset.mul_sum, smul_eq_mul, mul_left_comm]

theorem csAsm_gmap_mul {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (a b : V ≃ₗ[K] V)
    (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  first
  | rfl
  | (congr 1; ext x; simp [LinearEquiv.mul_apply])

theorem csAsm_gmap_one {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  unfold Formalism.HermitianLatticesTheory.gmap
  simp

theorem csAsm_gmap_inv {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (a : V ≃ₗ[K] V)
    (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a L) = L := by
  rw [← csAsm_gmap_mul, inv_mul_cancel, csAsm_gmap_one]

theorem classSetFiniteL_of (hSigmaInvol : Formalism.UG.CS.SigmaInvol) (hTracePos : Formalism.UG.CS.TracePos)
    (hFormSymm : Formalism.UG.CS.FormSymm) (hIsomUJ : Formalism.UG.CS.IsomUJ)
    (hGlobLatLattice : Formalism.UG.CS.GlobLatLattice) (hClassInj : Formalism.UG.CS.ClassInj)
    (hScaleBound : Formalism.UG.CS.ScaleBound) (hDualBound : Formalism.UG.CS.DualBound)
    (hClassSetFiniteBdd : Formalism.UG.CS.ClassSetFiniteBdd) (hStdLatFull : Formalism.UG.CS.StdLatFull) :
    Formalism.UG.ClassSetFiniteL := by
  intro F E _ _ _ _ _ n _ _ σ J hσ hJ hdet hdef Λ hfin hspan
  have hinv : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e := fun e => hSigmaInvol F E σ hσ e
  obtain ⟨c, hc0, hcpos⟩ := hTracePos F E n σ J hdef
  set cE : E := algebraMap F E (c : F) with hcE
  have hσc : (σ : E →+* E) cE = cE := by
    rw [hcE]
    exact σ.commutes _
  have hcF : ((c : 𝓞 F) : F) ≠ 0 := by
    intro h
    apply hc0
    first
    | exact_mod_cast h
    | exact RingOfIntegers.ext h
  have hcE0 : cE ≠ 0 := by
    rw [hcE]
    exact (map_ne_zero _).mpr hcF
  set cO : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) c with hcO
  have hcOE : algebraMap (𝓞 E) E cO = cE := by
    rw [hcO, hcE, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
  have hcO0 : cO ≠ 0 := by
    intro h
    apply hcE0
    rw [← hcOE, h, map_zero]
  letI : StarRing E := starOfInv (σ : E →+* E) hinv
  obtain ⟨hsymm, hfe⟩ := hFormSymm E (σ : E →+* E) hinv n J cE hσc hJ
  obtain ⟨d, hd0, hd⟩ := hScaleBound F E n σ J Λ hfin hspan
  obtain ⟨e, he0, he⟩ := hDualBound F E n σ J Λ hdet hfin hspan
  have hpos : ∀ x : n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (formJ (σ : E →+* E) hinv J cE x x) := by
    intro x hx
    rw [hfe]
    exact hcpos x hx
  obtain ⟨s, hs⟩ := hClassSetFiniteBdd E (n → E) (formJ (σ : E →+* E) hinv J cE) hsymm hpos d (e * cO) hd0
    (mul_ne_zero he0 hcO0)
  have key : ∀ g : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ N ∈ s, ∃ φ ∈ Formalism.HermitianLatticesTheory.isom (formJ (σ : E →+* E) hinv J cE),
      Formalism.HermitianLatticesTheory.gmap φ N = globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ := by
    intro g
    apply hs
    · exact hGlobLatLattice F E n Λ hfin hspan g
    · intro x hx y hy
      rw [hfe, Submodule.mem_one]
      obtain ⟨o, ho⟩ := hd g g.2 x hx y hy
      refine ⟨o * cO, ?_⟩
      rw [map_mul, ho, hcOE]
      show algebraMap (𝓞 E) E d * hform (σ : E →+* E) J x y * cE = algebraMap (𝓞 E) E d * (cE * hform (σ : E →+* E) J x y)
      ring
    · intro x hx
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply, Submodule.mem_one] at hx
      have hx' : ∀ y ∈ globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ,
          hform (σ : E →+* E) J y (cE • x) ∈ (algebraMap (𝓞 E) E).range := by
        intro y hy
        obtain ⟨o, ho⟩ := hx y hy
        rw [hfe] at ho
        refine ⟨o, ?_⟩
        rw [csAsm_hform_smul_right]
        exact ho
      have h2 := he g g.2 (cE • x) hx'
      convert h2 using 1
      show algebraMap (𝓞 E) E (e * cO) • x = algebraMap (𝓞 E) E e • cE • x
      rw [map_mul, hcOE, smul_smul]
  classical
  choose N hN φ hφ hφN using key
  let f : ClassSet ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) → s :=
    fun q => ⟨N (Quotient.out q), hN (Quotient.out q)⟩
  have hf : Function.Injective f := by
    intro q1 q2 h12
    have hNN : N (Quotient.out q1) = N (Quotient.out q2) := congrArg Subtype.val h12
    obtain ⟨γ, hγ⟩ : ∃ γ : GL n E, glEquiv γ = φ (Quotient.out q1) * (φ (Quotient.out q2))⁻¹ :=
      ⟨Matrix.GeneralLinearGroup.toLin.symm ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (n → E)).symm
        (φ (Quotient.out q1) * (φ (Quotient.out q2))⁻¹)), by simp [glEquiv]⟩
    have hUJ : γ ∈ UJ (σ : E →+* E) J :=
      (hIsomUJ E (σ : E →+* E) hinv n J cE hcE0 hσc γ).mpr (by
        rw [hγ]
        exact mul_mem (hφ _) (inv_mem (hφ _)))
    have hlat : globLat ((Quotient.out q1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ =
        Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat ((Quotient.out q2 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
          GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) := by
      rw [hγ, csAsm_gmap_mul, ← hφN (Quotient.out q2), csAsm_gmap_inv, ← hNN, hφN]
    have h3 := hClassInj F E n σ J Λ hfin hspan (Quotient.out q1) (Quotient.out q2) γ hUJ hlat
    rwa [DoubleCoset.out_eq', DoubleCoset.out_eq'] at h3
  exact Finite.of_injective f hf

theorem classSetFinite_of (hSigmaInvol : Formalism.UG.CS.SigmaInvol) (hTracePos : Formalism.UG.CS.TracePos)
    (hFormSymm : Formalism.UG.CS.FormSymm) (hIsomUJ : Formalism.UG.CS.IsomUJ)
    (hGlobLatLattice : Formalism.UG.CS.GlobLatLattice) (hClassInj : Formalism.UG.CS.ClassInj)
    (hScaleBound : Formalism.UG.CS.ScaleBound) (hDualBound : Formalism.UG.CS.DualBound)
    (hClassSetFiniteBdd : Formalism.UG.CS.ClassSetFiniteBdd) (hStdLatFull : Formalism.UG.CS.StdLatFull) :
    Formalism.UG.ClassSetFinite := by
  intro F E _ _ _ _ _ n _ _ σ J hσ hJ hdet hdef
  have h := classSetFiniteL_of hSigmaInvol hTracePos hFormSymm hIsomUJ hGlobLatLattice hClassInj hScaleBound
    hDualBound hClassSetFiniteBdd hStdLatFull F E n σ J hσ hJ hdet hdef (stdLat (n := n) (A := E) (𝓞 E))
    (hStdLatFull E n).1 (hStdLatFull E n).2
  have heq : levelAfL σ J (stdLat (n := n) (A := E) (𝓞 E)) = levelAf σ J := by
    unfold Formalism.UG.levelAfL Formalism.UG.levelAf
    congr 1
    apply le_antisymm
    · unfold Formalism.UG.latS
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range] at hx ⊢
      intro i
      obtain ⟨a, ha⟩ := hx i
      exact ⟨⟨inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i),
        Subring.subset_closure (Or.inl ⟨⟨x i, a, ha⟩, rfl⟩)⟩, rfl⟩
    · intro v hv
      simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range] at hv
      unfold Formalism.UG.latS
      rw [pi_eq_sum_univ v]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      obtain ⟨y, hy⟩ := hv i
      have hy' : (y : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = v i := hy
      have hsm : (v i • fun j => if i = j then (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) else 0) =
          y • (fun j => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (if i = j then (1 : E) else 0)) := by
        ext j
        simp only [Pi.smul_apply, smul_eq_mul, Subring.smul_def]
        rw [← hy']
        split_ifs <;> simp
      rw [hsm]
      refine Submodule.smul_mem _ y (Submodule.subset_span ⟨fun j => if i = j then (1 : E) else 0, ?_, rfl⟩)
      simp only [SetLike.mem_coe, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range]
      intro j
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
  rw [heq] at h
  exact h

end Formalism.UG.P
end
end

section
noncomputable section

open NumberField

namespace Formalism.UG.P

theorem csTrace_trace_pos {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F)
    (hb : ∀ ι : F →+* ℝ, 0 < ι b) : 0 < Algebra.trace ℚ F b := by
  have key : algebraMap ℚ ℂ (Algebra.trace ℚ F b) = ∑ σ : F →ₐ[ℚ] ℂ, σ b :=
    trace_eq_sum_embeddings ℂ
  have hre : ∀ σ : F →ₐ[ℚ] ℂ, 0 < (σ b).re := by
    intro σ
    have hr : NumberField.ComplexEmbedding.IsReal (σ : F →+* ℂ) :=
      NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
    have e := hr.coe_embedding_apply b
    have e' : (σ : F →+* ℂ) b = σ b := rfl
    rw [← e', ← e, Complex.ofReal_re]
    exact hb _
  have hne : Nonempty (F →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have h2 := congrArg Complex.re key
  rw [Complex.re_sum] at h2
  have h3 : 0 < ∑ σ : F →ₐ[ℚ] ℂ, (σ b).re :=
    Finset.sum_pos (fun σ _ => hre σ) Finset.univ_nonempty
  rw [← h2] at h3
  simpa using h3

theorem csTrace_trace_algebraMap_pos {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsTotallyReal F] (b : F) (hb : ∀ ι : F →+* ℝ, 0 < ι b) :
    0 < Algebra.trace ℚ E (algebraMap F E b) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [← Algebra.trace_trace (S := F), Algebra.trace_algebraMap, map_nsmul]
  exact nsmul_pos (csTrace_trace_pos b hb) Module.finrank_pos.ne'

theorem trace_form_positive : Formalism.UG.CS.TracePos := by
  intro F E _ _ _ _ _ n _ _ σ J hJ
  obtain ⟨hF, hdef⟩ := hJ
  haveI : IsTotallyReal F := hF

  let φ0 : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  let ι0 : F →+* ℝ :=
    (NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (NumberField.InfinitePlace.mk φ0))).embedding
  have hval : ∀ x : n → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x := by
    intro x hx
    rcases hdef ι0 with h | h
    · obtain ⟨a, ha, -⟩ := h x hx; exact ⟨a, ha⟩
    · obtain ⟨a, ha, -⟩ := h x hx; exact ⟨a, ha⟩

  have same : ∀ x y : n → E, x ≠ 0 → y ≠ 0 → ∀ a b : F,
      algebraMap F E a = hform (σ : E →+* E) J x x →
      algebraMap F E b = hform (σ : E →+* E) J y y → ∀ ι : F →+* ℝ, 0 < ι a * ι b := by
    intro x y hx hy a b ha hb ι
    rcases hdef ι with h | h
    · obtain ⟨a', ha', hap⟩ := h x hx
      obtain ⟨b', hb', hbp⟩ := h y hy
      have e1 : a' = a := (algebraMap F E).injective (ha'.trans ha.symm)
      have e2 : b' = b := (algebraMap F E).injective (hb'.trans hb.symm)
      subst e1 e2
      exact mul_pos hap hbp
    · obtain ⟨a', ha', hap⟩ := h x hx
      obtain ⟨b', hb', hbp⟩ := h y hy
      have e1 : a' = a := (algebraMap F E).injective (ha'.trans ha.symm)
      have e2 : b' = b := (algebraMap F E).injective (hb'.trans hb.symm)
      subst e1 e2
      exact mul_pos_of_neg_of_neg hap hbp
  by_cases hx : ∃ x0 : n → E, x0 ≠ 0
  · obtain ⟨x0, hx0⟩ := hx
    obtain ⟨a0, ha0⟩ := hval x0 hx0
    have ha0ne : a0 ≠ 0 := by
      intro h0
      have := same x0 x0 hx0 hx0 a0 a0 ha0 ha0 ι0
      rw [h0, map_zero, zero_mul] at this
      exact lt_irrefl _ this
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a0
    have hqF : algebraMap (𝓞 F) F q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (nonZeroDivisors.ne_zero hq)
    have hp : algebraMap (𝓞 F) F p = a0 * algebraMap (𝓞 F) F q := by
      rw [← hpq, div_mul_cancel₀ _ hqF]
    have hc : ((p * q : 𝓞 F) : F) = a0 * algebraMap (𝓞 F) F q * algebraMap (𝓞 F) F q := by
      have : ((p * q : 𝓞 F) : F) = algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F q := by
        rw [← map_mul]
      rw [this, hp]
    refine ⟨p * q, ?_, ?_⟩
    · intro h0
      have : ((p * q : 𝓞 F) : F) = 0 := by simp [h0]
      rw [hc] at this
      exact mul_ne_zero (mul_ne_zero ha0ne hqF) hqF this
    · intro x hx
      obtain ⟨a, ha⟩ := hval x hx
      rw [← ha, ← map_mul]
      apply csTrace_trace_algebraMap_pos
      intro ι
      have hs := same x0 x hx0 hx a0 a ha0 ha ι
      have hq2 : 0 < ι (algebraMap (𝓞 F) F q) * ι (algebraMap (𝓞 F) F q) :=
        mul_self_pos.mpr ((map_ne_zero_iff _ ι.injective).mpr hqF)
      rw [hc, map_mul, map_mul, map_mul]
      nlinarith [mul_pos hs hq2]
  · push_neg at hx
    refine ⟨1, one_ne_zero, fun x hx' => absurd (hx x) hx'⟩

end Formalism.UG.P
end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG Formalism.UG.CS

theorem class_injective_of_span_recovery (hSpanRecover : Formalism.UG.CS.SpanRecover)
    (hGlobLatEquiv : Formalism.UG.CS.GlobLatEquiv) : Formalism.UG.CS.ClassInj := by
  intro F E _ _ _ _ _ n _ _ σ J Λ hfin hspan g g' γ hγ hlat
  set A := FiniteAdeleRing (𝓞 F) F with hA
  set L := latS (F := F) A (tensInt (F := F) A (intOE E) (intAd F)) Λ with hL
  set γA : GL n (E ⊗[F] A) := bc (inclE (F := F) A) γ with hγA

  have hsig : ∀ e : E, sigR σ A (inclE (F := F) A e) = inclE (F := F) A (σ e) := by
    intro e
    simp [sigR, inclE]
  have hγm : (γA : Matrix n n (E ⊗[F] A)) = (γ : Matrix n n E).map (inclE (F := F) A) := rfl
  have hγU : γA ∈ UPts σ J A := by
    change cT (sigR σ A) (γA : Matrix n n (E ⊗[F] A)) * J.map (inclE (F := F) A)
      * (γA : Matrix n n (E ⊗[F] A)) = J.map (inclE (F := F) A)
    have h0 : cT (σ : E →+* E) (γ : Matrix n n E) * J * (γ : Matrix n n E) = J := hγ
    have hc : cT (sigR σ A) (γA : Matrix n n (E ⊗[F] A))
        = (cT (σ : E →+* E) (γ : Matrix n n E)).map (inclE (F := F) A) := by
      ext i j
      simp [cT, hγm, hsig]
    rw [hc, hγm, ← Matrix.map_mul, ← Matrix.map_mul, h0]

  have heq : globLat (γA * (g' : GL n (E ⊗[F] A))) Λ = globLat (g : GL n (E ⊗[F] A)) Λ := by
    have h1 := hGlobLatEquiv F E n Λ γ (g' : GL n (E ⊗[F] A)) 1 (one_mem _)
    rw [mul_one] at h1
    rw [h1, hlat]
  have hR : ∀ u : n → E ⊗[F] A,
      (((g : GL n (E ⊗[F] A))⁻¹ : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ u ∈ L ↔
        (((γA * (g' : GL n (E ⊗[F] A)))⁻¹ : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ u ∈ L := by
    intro u
    have h1 := hSpanRecover F E n Λ hfin hspan (g : GL n (E ⊗[F] A)) u
    have h2 := hSpanRecover F E n Λ hfin hspan (γA * (g' : GL n (E ⊗[F] A))) u
    rw [heq] at h2
    exact h1.symm.trans h2
  set k : GL n (E ⊗[F] A) := (g : GL n (E ⊗[F] A))⁻¹ * (γA * (g' : GL n (E ⊗[F] A))) with hk
  have hkS : k ∈ stabGL L := by
    intro x
    have h := hR (((γA * (g' : GL n (E ⊗[F] A)) : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    exact h.symm
  have hkU : k ∈ UPts σ J A :=
    mul_mem (inv_mem g.2) (mul_mem hγU g'.2)
  rw [DoubleCoset.eq]
  refine ⟨⟨γA⁻¹, inv_mem hγU⟩, ?_, ⟨k, hkU⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨γ⁻¹, inv_mem hγ, map_inv _ _⟩
  · rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨hkU, hkS⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hk]
    group

end Formalism.UG.P
end
end

section
noncomputable section
open Module NumberField Matrix

namespace Formalism.UG.P

theorem csCovol_sq_eq_det_gram {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis (Fin N) ℤ L) :
    ZLattice.covolume L ^ 2 =
      (Matrix.of fun i j : Fin N => inner ℝ ((b i : EuclideanSpace ℝ (Fin N))) (b j)).det := by
  classical
  let b₀ := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
  have hc := ZLattice.covolume_eq_det_mul_measureReal L MeasureTheory.volume b b₀
  have hvol : MeasureTheory.volume.real (ZSpan.fundamentalDomain b₀) = 1 := by
    rw [MeasureTheory.measureReal_def,
      MeasureTheory.measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀ MeasureTheory.volume)]
    rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped]
    simp
  rw [hc, hvol, mul_one, sq_abs, Module.Basis.det_apply]
  have hG : (Matrix.of fun i j : Fin N => inner ℝ ((b i : EuclideanSpace ℝ (Fin N))) (b j)) =
      (b₀.toMatrix (Subtype.val ∘ b))ᵀ * b₀.toMatrix (Subtype.val ∘ b) := by
    ext i j
    simp [b₀, Matrix.mul_apply, Module.Basis.toMatrix_apply, PiLp.inner_apply, mul_comm]
  rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]

theorem csCovol_det_le {N : ℕ} (G : Matrix (Fin N) (Fin N) ℚ) (hG : 0 < G.det) (D : ℤ) (hD0 : D ≠ 0)
    (P : Matrix (Fin N) (Fin N) ℤ) (hP : G * P.map (Int.cast : ℤ → ℚ) = (D : ℚ) • 1) :
    G.det ≤ (|D| : ℚ) ^ N := by
  have hdet := congrArg Matrix.det hP
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hPd : ((P.det : ℤ) : ℚ) = (P.map (Int.cast : ℤ → ℚ)).det := (Int.castRingHom ℚ).map_det P
  rw [← hPd] at hdet
  have hP0 : P.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, mul_zero] at hdet
    exact pow_ne_zero N (Int.cast_ne_zero.mpr hD0) hdet.symm
  have h1 : (1 : ℚ) ≤ |(P.det : ℚ)| := by
    have : (1 : ℤ) ≤ |P.det| := Int.one_le_abs hP0
    exact_mod_cast this
  have habs := congrArg abs hdet
  rw [abs_mul, abs_of_pos hG, abs_pow] at habs
  have key : G.det ≤ |(D : ℚ)| ^ N :=
    calc G.det = G.det * 1 := (mul_one _).symm
      _ ≤ G.det * |(P.det : ℚ)| := mul_le_mul_of_nonneg_left h1 hG.le
      _ = |(D : ℚ)| ^ N := habs
  simpa using key

theorem csCovol_int_mult {K : Type} [Field K] [NumberField K] (e : 𝓞 K) (he : e ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ c : 𝓞 K, (algebraMap ℤ (𝓞 K) n) = c * e := by
  obtain ⟨c, hc⟩ := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 K) e
  refine ⟨Algebra.intNorm ℤ (𝓞 K) e, ?_, c, by rw [hc, mul_comm]⟩
  first
  | exact Algebra.intNorm_ne_zero.mpr he
  | exact (Algebra.intNorm_eq_zero.not).mpr he
  | simpa using he

theorem csCovol_discr_mul {K : Type} [Field K] [NumberField K] (z : K)
    (hz : ∀ a : 𝓞 K, Algebra.trace ℚ K ((a : K) * z) ∈ Set.range (algebraMap ℤ ℚ)) :
    ((discr K : ℚ) : K) * z ∈ Set.range (algebraMap (𝓞 K) K) := by
  have hmem : z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.mp ha
    rw [Algebra.traceForm_apply, mul_comm]
    obtain ⟨n, hn⟩ := hz a'
    exact ⟨n, hn⟩
  have hone : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)
    (1 : Submodule (𝓞 K) K) (b := NumberField.integralBasis K)
    (fun i => by
      rw [NumberField.integralBasis_apply]
      exact NumberField.RingOfIntegers.isIntegral_coe _) hone hmem
  rw [← NumberField.coe_discr, Algebra.smul_def, mul_one] at hint
  refine ⟨⟨_, hint⟩, ?_⟩
  simp

section Main

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {N : ℕ}
  (ι : V →+ EuclideanSpace ℝ (Fin N))

theorem csCovol_mem_zmap (M : Submodule (𝓞 K) V) (v : EuclideanSpace ℝ (Fin N)) :
    v ∈ Formalism.HermitianLatticesTheory.zmap ι M ↔ ∃ y ∈ M, ι y = v := by
  first
  | exact Iff.rfl
  | simp [Formalism.HermitianLatticesTheory.zmap, AddSubgroup.mem_map]
  | (unfold Formalism.HermitianLatticesTheory.zmap; rw [AddSubgroup.mem_toIntSubmodule, AddSubgroup.mem_map]; rfl)

theorem csCovol_expand
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) (b : Basis (Fin N) ℤ (Formalism.HermitianLatticesTheory.zmap ι M)) (m : Fin N → V)
    (hm : ∀ i, ι (m i) = b i) (z : V) (hz : z ∈ M) :
    ∃ a : Fin N → ℤ, (∀ w : V, Algebra.trace ℚ K (h w z) =
        ∑ j, (a j : ℚ) * Algebra.trace ℚ K (h w (m j))) ∧
      (∀ w : V, Algebra.trace ℚ K (h z w) = ∑ j, (a j : ℚ) * Algebra.trace ℚ K (h (m j) w)) := by
  have hz' : ι z ∈ Formalism.HermitianLatticesTheory.zmap ι M := (csCovol_mem_zmap ι M (ι z)).mpr ⟨z, hz, rfl⟩
  have h1 : (⟨ι z, hz'⟩ : Formalism.HermitianLatticesTheory.zmap ι M) = ∑ j, b.repr ⟨ι z, hz'⟩ j • b j := (b.sum_repr _).symm
  have h2 := congrArg Subtype.val h1
  simp only [Submodule.coe_sum, SetLike.val_smul, ← hm] at h2
  refine ⟨fun j => b.repr ⟨ι z, hz'⟩ j, fun w => ?_, fun w => ?_⟩
  · have e1 := hι w z
    rw [h2, inner_sum] at e1
    simp only [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hι] at e1
    have e2 : ((Algebra.trace ℚ K (h w z) : ℚ) : ℝ) =
        ((∑ j, ((b.repr ⟨ι z, hz'⟩ j : ℤ) : ℚ) * Algebra.trace ℚ K (h w (m j)) : ℚ) : ℝ) := by
      push_cast
      first | exact e1 | exact e1.symm
    exact_mod_cast e2
  · have e1 := hι z w
    rw [h2, sum_inner] at e1
    simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hι] at e1
    have e2 : ((Algebra.trace ℚ K (h z w) : ℚ) : ℝ) =
        ((∑ j, ((b.repr ⟨ι z, hz'⟩ j : ℤ) : ℚ) * Algebra.trace ℚ K (h (m j) w) : ℚ) : ℝ) := by
      push_cast
      first | exact e1 | exact e1.symm
    exact_mod_cast e2

theorem csCovol_column
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) (b : Basis (Fin N) ℤ (Formalism.HermitianLatticesTheory.zmap ι M)) (m : Fin N → V)
    (hm : ∀ i, ι (m i) = b i) (e : 𝓞 K)
    (hdual : ∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M) (n : ℤ) (c : 𝓞 K)
    (hc : algebraMap ℤ (𝓞 K) n = c * e)
    (hG : (Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k))).det ≠ 0) (j : Fin N) :
    ∃ a : Fin N → ℤ,
      (Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k))) *ᵥ (fun k => (a k : ℚ)) =
        ((n * discr K : ℤ) : ℚ) • Pi.single j (1 : ℚ) := by
  classical
  set G : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k)) with hGdef
  have htr : ∀ (q : ℚ) (y : K), Algebra.trace ℚ K ((q : K) * y) = q * Algebra.trace ℚ K y := by
    intro q y
    rw [← Rat.smul_def, map_smul, smul_eq_mul]
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  set cc : Fin N → ℚ := G⁻¹ *ᵥ Pi.single j (1 : ℚ) with hcc
  have hGc : G *ᵥ cc = Pi.single j (1 : ℚ) := by
    rw [hcc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hunit, Matrix.one_mulVec]
  set x : V := ∑ k, ((cc k : ℚ) : K) • m k with hx
  have hmx : ∀ i, Algebra.trace ℚ K (h (m i) x) = (Pi.single j (1 : ℚ) : Fin N → ℚ) i := by
    intro i
    rw [← hGc, hx, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, htr]
    simp only [Matrix.mulVec, dotProduct, hGdef, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have hloc : ∀ w ∈ M, ((discr K : ℚ) : K) * h w x ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro w hw
    apply csCovol_discr_mul
    intro a
    have hai : IsIntegral ℤ (star (a : K)) :=
      (NumberField.RingOfIntegers.isIntegral_coe a).map (starRingEnd K).toIntAlgHom
    set a' : 𝓞 K := ⟨star (a : K), hai⟩ with ha'
    have hw' : a' • w ∈ M := M.smul_mem a' hw
    obtain ⟨aa, -, haa⟩ := csCovol_expand h ι hι M b m hm (a' • w) hw'
    have e1 := haa x
    simp only [hmx] at e1
    have hsmul : a' • w = (star (a : K)) • w := by
      rw [← algebraMap_smul K a' w]
      rfl
    rw [hsmul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul] at e1
    refine ⟨aa j, ?_⟩
    rw [e1]
    simp [Pi.single_apply]
  have hdx : ((discr K : ℚ) : K) • x ∈ Formalism.HermitianLatticesTheory.dual h M := by
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    intro w hw
    rw [map_smul, smul_eq_mul]
    obtain ⟨r, hr⟩ := hloc w hw
    exact Submodule.mem_one.mpr ⟨r, hr⟩
  have hy : (((n * discr K : ℤ) : ℚ) : K) • x ∈ M := by
    have h1 := hdual _ hdx
    have h2 := M.smul_mem c h1
    have hcK : ((n : ℤ) : K) = (c : K) * (e : K) := by
      have := congrArg (fun t : 𝓞 K => (t : K)) hc
      simpa using this
    convert h2 using 1
    rw [← algebraMap_smul K c, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [hcK]
    try simp only [algebraMap_smul, RingOfIntegers.coe_eq_algebraMap]
    try ring
  obtain ⟨aa, haa, -⟩ := csCovol_expand h ι hι M b m hm _ hy
  refine ⟨aa, ?_⟩
  funext i
  have e1 := haa (m i)
  rw [map_smul, smul_eq_mul, htr, hmx] at e1
  simp only [Matrix.mulVec, dotProduct, hGdef, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [e1]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

end Main

theorem covolume_of_dual_holds : Formalism.UG.CS.CovolOfDual := by
  intro K V _ _ _ _ _ _ _ _ h _ _ N ι hι e he
  obtain ⟨n, hn0, c, hc⟩ := csCovol_int_mult e he
  set D : ℤ := n * discr K with hD
  have hD0 : D ≠ 0 := mul_ne_zero hn0 (NumberField.discr_ne_zero K)
  refine ⟨|(D : ℝ)| ^ N, ?_⟩
  intro M _ hdual _ _
  classical
  have hrank : Module.finrank ℤ (Formalism.HermitianLatticesTheory.zmap ι M) = N := by
    rw [ZLattice.rank ℝ, finrank_euclideanSpace_fin]
  let b := Module.finBasisOfFinrankEq ℤ (Formalism.HermitianLatticesTheory.zmap ι M) hrank
  have hm' : ∀ i, ∃ y ∈ M, ι y = b i := fun i => (csCovol_mem_zmap ι M _).mp (b i).2
  choose m _ hm using hm'
  set G : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k)) with hGdef
  have hsq := csCovol_sq_eq_det_gram _ b
  have hGR : (Matrix.of fun i j : Fin N => inner ℝ ((b i : EuclideanSpace ℝ (Fin N))) (b j)) =
      (Rat.castHom ℝ).mapMatrix G := by
    ext i k
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hGdef]
    rw [← hm, ← hm, hι]
    rfl
  have hsq' : ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) ^ 2 = (G.det : ℝ) := by
    rw [hsq, hGR, ← RingHom.map_det]
    rfl
  clear hsq
  have hsq := hsq'
  have hcov : 0 < ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) := ZLattice.covolume_pos _ _
  have hGpos : 0 < G.det := by
    have : (0 : ℝ) < (G.det : ℝ) := by rw [← hsq]; positivity
    exact_mod_cast this
  have hcol := fun j => csCovol_column h ι hι M b m hm e hdual n c hc hGpos.ne' j
  choose aa haa using hcol
  let P : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun k j => aa j k
  have hP : G * P.map (Int.cast : ℤ → ℚ) = (D : ℚ) • 1 := by
    ext i j
    have := congrFun (haa j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, P, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [this, hD]
    simp [Pi.single_apply, eq_comm]
  have hle := csCovol_det_le G hGpos D hD0 P hP
  have hleR : ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) ^ 2 ≤ |(D : ℝ)| ^ N := by
    rw [hsq]
    have : ((G.det : ℚ) : ℝ) ≤ (((|D| : ℚ) ^ N : ℚ) : ℝ) := by exact_mod_cast hle
    simpa using this
  have hD1 : (1 : ℝ) ≤ |(D : ℝ)| ^ N := by
    apply one_le_pow₀
    have : (1 : ℤ) ≤ |D| := Int.one_le_abs hD0
    exact_mod_cast this
  nlinarith

end Formalism.UG.P
end
end

section
noncomputable section

open NumberField

namespace Formalism.UG.P

theorem csBdd_nat_mul {K : Type} [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ t : 𝓞 K, (m : 𝓞 K) = d * t := by
  classical
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, ?_⟩
  · refine Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
    exact ⟨t, by rw [← ht, mul_comm]⟩

theorem class_set_finite_bounded_holds (hCovolOfDual : Formalism.UG.CS.CovolOfDual) :
    Formalism.UG.CS.ClassSetFiniteBdd := by
  intro K V _ _ _ _ _ _ _ _ h hsymm hpos d e hd he
  obtain ⟨N, ι, hι, hmul, hlat⟩ := Formalism.HermitianLatticesTheory.traceReal_main h hsymm hpos
  obtain ⟨C, hC⟩ := hCovolOfDual K V h hsymm hpos N ι hι e he
  obtain ⟨m, hm, t, ht⟩ := csBdd_nat_mul d hd
  let S : Set (Submodule (𝓞 K) V) := {M | Submodule.IsLattice K M ∧
    (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ (1 : Submodule (𝓞 K) K)) ∧
    (∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M)}
  have hSd : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M, (m : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro M hM x hx y hy
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hM.2.1 x hx y hy)
    refine Submodule.mem_one.mpr ⟨t * a, ?_⟩
    have hmK : (m : K) = (d : K) * (t : K) := by
      have := congrArg (algebraMap (𝓞 K) K) ht
      simpa using this
    rw [map_mul, ha, hmK]
    have htc : algebraMap (𝓞 K) K t = (t : K) := rfl
    rw [htc]
    ring
  obtain ⟨s, -, hs⟩ := Formalism.HermitianLatticesTheory.classSetFinite_core Formalism.HermitianLatticesTheory.shortVectors
    Formalism.HermitianLatticesTheory.finIntermediate Formalism.HermitianLatticesTheory.isomOfTrace h hpos N ι hι hmul m hm C S hSd
    (fun M hM => hlat M hM.1) (fun M hM _ _ => hC M hM.1 hM.2.2)
  exact ⟨s, fun M hM hdM heM => hs M ⟨hM, hdM, heM⟩⟩

end Formalism.UG.P
end
end

section
namespace Formalism.UG.P

theorem lattice_class_set_finite_local_holds : Formalism.UG.ClassSetFiniteL :=
  have hs := span_recovery_of_integral_adelic_approx integral_adele_approximation_holds
  classSetFiniteL_of sigma_involution_holds trace_form_positive hermitian_form_symmetry_holds unitary_isometry_lattice_holds
    global_lattice_isLattice_holds (class_injective_of_span_recovery hs global_lattice_equiv_holds) scale_bound_holds
    (dual_lattice_bound_holds hs) (class_set_finite_bounded_holds covolume_of_dual_holds) standard_lattice_full_holds

theorem lattice_class_set_finite_holds : Formalism.UG.ClassSetFinite :=
  have hs := span_recovery_of_integral_adelic_approx integral_adele_approximation_holds
  classSetFinite_of sigma_involution_holds trace_form_positive hermitian_form_symmetry_holds unitary_isometry_lattice_holds
    global_lattice_isLattice_holds (class_injective_of_span_recovery hs global_lattice_equiv_holds) scale_bound_holds
    (dual_lattice_bound_holds hs) (class_set_finite_bounded_holds covolume_of_dual_holds) standard_lattice_full_holds

end Formalism.UG.P
end
