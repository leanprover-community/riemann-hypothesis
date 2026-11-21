import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingletonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsolutelyIntegrallyCloseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstAndFinite
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionOfMonicPolynomialsHaveRootsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIsNilpotentMulFiniteInfFgIdealsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

private theorem ringKrullDim_le_quotient_of_algebraMap_eq_zero (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (s : R) (hs : algebraMap R S s = 0) :
    ringKrullDim S ≤ ringKrullDim (R ⧸ Ideal.span {s}) := by
  rw [ringKrullDim_quotient]
  have hmem : ∀ P : PrimeSpectrum S, (⟨P.asIdeal.comap (algebraMap R S), inferInstance⟩ : PrimeSpectrum R) ∈
      PrimeSpectrum.zeroLocus (R := R) (Ideal.span {s}) := fun P => by
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hs, Ideal.zero_mem]
  exact Order.krullDim_le_of_strictMono (fun P => ⟨_, hmem P⟩)
    (fun P Q h => Subtype.mk_lt_mk.mpr (Ideal.IsIntegral.comap_lt_comap (R := R) h))

private theorem hInv_adjoin_of_dim_quotient_lt (q : ℕ) [NeZero q] (d : ℕ)
    (hlow : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R)
    (D : Type) [CommRing D] [Algebra.FiniteType ℤ D] (hqD : IsUnit (q : D)) (E : Type) [CommRing E]
    [Algebra D E] [Algebra.IsIntegral D E] (s : D) (hsE : algebraMap D E s = 0)
    (hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d) (F : Finset E) :
    HInv q ((Algebra.adjoin D (F : Set E)).restrictScalars ℤ) := by
  set T := Algebra.adjoin D (F : Set E)
  have : Algebra.IsIntegral D T := ⟨fun x =>
    (isIntegral_algHom_iff T.val Subtype.val_injective).mp (Algebra.IsIntegral.isIntegral (x : E))⟩
  have : Algebra.FiniteType D T := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset F)
  have : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans (R := ℤ) (S := D) inferInstance inferInstance
  have hsT : algebraMap D T s = 0 := Subtype.ext (by simpa using hsE)
  have h1 : ringKrullDim T < d := (ringKrullDim_le_quotient_of_algebraMap_eq_zero D T s hsT).trans_lt hlt
  have h2 : IsUnit (q : T) := by simpa using hqD.map (algebraMap D T)
  exact hlow T h2 h1

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.hInv_of_integral_killed_of_lower : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ (E : Type) [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (s : D), s ≠ 0 → algebraMap D E s = 0 → HInv q E := by
  intro q _ d hlow D _ _ _ hqD hdD E _ _ _ s hs0 hsE
  have hquot := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hs0)
  have hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d := by
    have h := hquot.trans hdD
    generalize ringKrullDim (D ⧸ Ideal.span {s}) = a at h ⊢
    cases a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe a =>
      have h' : a + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
      have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h')
      exact_mod_cast (ENat.add_one_le_iff ha).mp h'
  exact GlobalTheory.T.hInv_of_directed_union_subalgebras q E (Finset E) (fun F => (Algebra.adjoin D (F : Set E)).restrictScalars ℤ)
    (fun F G h x hx => Algebra.adjoin_mono (Finset.coe_subset.mpr h) hx)
    (fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩)
    (fun F => by
      have h := hqD.map (algebraMap D (Algebra.adjoin D (F : Set E)))
      rw [map_natCast] at h
      exact h)
    (fun F => hInv_adjoin_of_dim_quotient_lt q d hlow D hqD E s hsE hlt F)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariant_integral_killed_of_lowerDim : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ (E : Type) [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (s : D), s ≠ 0 → algebraMap D E s = 0 → HInv q E := by
  first | (exact @GlobalTheory.hInv_of_integral_killed_of_lower) | (exact GlobalTheory.hInv_of_integral_killed_of_lower) | (intros; apply GlobalTheory.hInv_of_integral_killed_of_lower  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem finite_retractions_of_adjoin_finset_integral
    (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
    [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E)
    (hF : Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤) :
    {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite := by
  classical
  choose p hpm hp0 using fun x : E => (Algebra.IsIntegral.isIntegral (R := D) x)
  have hfin : (Set.pi Set.univ fun f : F =>
      ((((p f.1).map (algebraMap D T)).roots.toFinset : Finset T) : Set T)).Finite :=
    Set.Finite.pi (fun f => Finset.finite_toSet _)
  refine Set.Finite.of_finite_image (f := fun χ : E →ₐ[D] T => fun f : F => χ f.1)
    (hfin.subset ?_) ?_
  · rintro _ ⟨χ, _, rfl⟩
    refine Set.mem_univ_pi.2 fun f => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots ((hpm f.1).map (algebraMap D T)).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply,
      Polynomial.aeval_def, hp0, map_zero]
  · intro χ₁ h₁ χ₂ h₂ he
    apply AlgHom.ext_of_adjoin_eq_top hF
    rintro x (⟨t, rfl⟩ | hx)
    · have e₁ := AlgHom.congr_fun (show χ₁.comp ι = AlgHom.id D T from h₁) t
      have e₂ := AlgHom.congr_fun (show χ₂.comp ι = AlgHom.id D T from h₂) t
      simp only [AlgHom.comp_apply, AlgHom.id_apply] at e₁ e₂
      rw [e₁, e₂]
    · exact congrFun he ⟨x, hx⟩

theorem finite_retractions_of_adjoin_finset_integral' :
    ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
      [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E),
      Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ →
        {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite :=
  fun D T E _ _ _ _ _ _ _ _ ι F hF => finite_retractions_of_adjoin_finset_integral D T E ι F hF

end GlobalTheory
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_retractions_of_adjoin_finset_integral_domain : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite := by
  first | (exact @GlobalTheory.finite_retractions_of_adjoin_finset_integral') | (exact GlobalTheory.finite_retractions_of_adjoin_finset_integral') | (intros; apply GlobalTheory.finite_retractions_of_adjoin_finset_integral'  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem ker_retraction_fg : ∀ (D T E : Type) [CommRing D] [CommRing T] [Algebra D T] [CommRing E] [Algebra D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → ∀ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T → (RingHom.ker χ).FG := by
  intro D T E _ _ _ _ _ ι F hF χ hχ
  have hχι : ∀ t, χ (ι t) = t := fun t => by simpa using DFunLike.congr_fun hχ t
  set J : Ideal E := Ideal.span ((fun f => f - ι (χ f)) '' (F : Set E)) with hJ
  have key : ∀ x, x - ι (χ x) ∈ J := by
    intro x
    have hx : x ∈ Algebra.adjoin D (Set.range ι ∪ (F : Set E)) := by rw [hF]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨t, rfl⟩ | hx
      · simp [hχι]
      · exact Ideal.subset_span ⟨x, hx, rfl⟩
    | algebraMap r => simp [AlgHom.commutes]
    | add x y _ _ hx hy =>
      have e : x + y - ι (χ (x + y)) = (x - ι (χ x)) + (y - ι (χ y)) := by
        simp only [map_add]; ring
      rw [e]; exact J.add_mem hx hy
    | mul x y _ _ hx hy =>
      have e : x * y - ι (χ (x * y)) = (x - ι (χ x)) * y + ι (χ x) * (y - ι (χ y)) := by
        simp only [map_mul]; ring
      rw [e]; exact J.add_mem (J.mul_mem_right _ hx) (J.mul_mem_left _ hy)
  have hker : RingHom.ker χ = J := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      simpa [hx] using key x
    · rw [hJ, Ideal.span_le]
      rintro _ ⟨f, _, rfl⟩
      simp [RingHom.mem_ker, hχι]
  rw [hker]
  classical
  exact ⟨F.image (fun f => f - ι (χ f)), by rw [Finset.coe_image]⟩

end GlobalTheory
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_retraction_fg_of_adjoin_finset : ∀ (D T E : Type) [CommRing D] [CommRing T] [Algebra D T] [CommRing E] [Algebra D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → ∀ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T → (RingHom.ker χ).FG := by
  first | (exact @GlobalTheory.ker_retraction_fg) | (exact GlobalTheory.ker_retraction_fg) | (intros; apply GlobalTheory.ker_retraction_fg  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem homotopyInv_quot_iInf_ker_retractions : ∀ (q : ℕ) [NeZero q] (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], IsUnit (q : D) → HInv q T → (∀ (E' : Type) [CommRing E'] [Algebra D E'] [Algebra.IsIntegral D E'] (s : D), s ≠ 0 → algebraMap D E' s = 0 → HInv q E') → ∀ (ι : T →ₐ[D] E) (X : Finset (E →ₐ[D] T)), (∀ χ ∈ X, χ.comp ι = AlgHom.id D T) → HInv q (E ⧸ ⨅ χ ∈ X, RingHom.ker χ) := by
  intro q _ D T E _ _ _ _ _ _ _ _ _ hq hT hlow ι X
  classical
  induction X using Finset.induction_on with
  | empty =>
    intro _
    apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton
    rw [Ideal.Quotient.subsingleton_iff]
    simp
  | @insert χ Y hχY ih =>
    intro hX
    have hχ : χ.comp ι = AlgHom.id D T := hX χ (Finset.mem_insert_self _ _)
    have ih' := ih (fun ψ hψ => hX ψ (Finset.mem_insert_of_mem hψ))
    have hχι : ∀ t, χ (ι t) = t := fun t => by
      simpa using DFunLike.congr_fun hχ t
    have hins : (⨅ ψ ∈ insert χ Y, RingHom.ker ψ) = RingHom.ker χ ⊓ ⨅ ψ ∈ Y, RingHom.ker ψ := by
      rw [Finset.iInf_insert]
    rw [hins]
    set P : Ideal E := RingHom.ker χ with hPdef
    set I : Ideal E := ⨅ ψ ∈ Y, RingHom.ker ψ with hIdef
    by_cases hIP : I ≤ P
    · rw [inf_eq_right.mpr hIP]; exact ih'
    · obtain ⟨y, hyI, hyP⟩ := Set.not_subset.mp hIP
      have hy0 : χ y ≠ 0 := fun h => hyP (RingHom.mem_ker.mpr h)
      have hint : IsIntegral D (χ y) := Algebra.IsIntegral.isIntegral _
      have hne := Ideal.comap_ne_bot_of_integral_mem hy0 (Ideal.mem_span_singleton_self (χ y)) hint
      obtain ⟨s, hsmem, hs0⟩ := Submodule.ne_bot_iff _ |>.mp hne
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hsmem
      obtain ⟨u, hu⟩ := hsmem
      have hsPI : algebraMap D E s ∈ P ⊔ I := by
        have h1 : algebraMap D E s - ι u * y ∈ P := by
          rw [hPdef, RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, hχι, hu, sub_self]
        have h2 : ι u * y ∈ I := Ideal.mul_mem_left _ _ hyI
        have : algebraMap D E s = (algebraMap D E s - ι u * y) + ι u * y := by ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
      set J : Ideal E := P ⊓ I with hJ
      have hJP : J ≤ P := inf_le_left
      have hJI : J ≤ I := inf_le_right
      apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (E ⧸ J) (P.map (Ideal.Quotient.mk J)) (I.map (Ideal.Quotient.mk J))
      · intro x hx
        obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective x
        have h1 := (Ideal.mem_quotient_iff_mem hJP).mp hx.1
        have h2 := (Ideal.mem_quotient_iff_mem hJI).mp hx.2
        have : Ideal.Quotient.mk J e = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ⟨h1, h2⟩
        rw [this]; exact zero_mem _
      · have := hq.map (algebraMap D (E ⧸ J))
        simpa using this
      · have hsurj : Function.Surjective χ := fun t => ⟨ι t, hχι t⟩
        have e1 := DoubleQuot.quotQuotEquivQuotOfLE hJP
        have e2 := (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv
        exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q T _ (e1.trans e2).symm hT
      · exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm ih'
      · apply hlow _ s hs0
        change Ideal.Quotient.mk _ (Ideal.Quotient.mk J (algebraMap D E s)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_sup]
        exact Ideal.mem_map_of_mem _ hsPI

end GlobalTheory
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hInv_quot_iInf_ker_retractions : ∀ (q : ℕ) [NeZero q] (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], IsUnit (q : D) → HInv q T → (∀ (E' : Type) [CommRing E'] [Algebra D E'] [Algebra.IsIntegral D E'] (s : D), s ≠ 0 → algebraMap D E' s = 0 → HInv q E') → ∀ (ι : T →ₐ[D] E) (X : Finset (E →ₐ[D] T)), (∀ χ ∈ X, χ.comp ι = AlgHom.id D T) → HInv q (E ⧸ ⨅ χ ∈ X, RingHom.ker χ) := by
  first | (exact @GlobalTheory.homotopyInv_quot_iInf_ker_retractions) | (exact GlobalTheory.homotopyInv_quot_iInf_ker_retractions) | (intros; apply GlobalTheory.homotopyInv_quot_iInf_ker_retractions  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure : ∀ (D : Type) [CommRing D] [IsDomain D], AIC (integralClosure D (AlgebraicClosure (FractionRing D))) := by
  first | (exact @GlobalTheory.aic_integralClosure_algebraicClosure) | (exact GlobalTheory.aic_integralClosure_algebraicClosure) | (intros; apply GlobalTheory.aic_integralClosure_algebraicClosure  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_mono (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    {F G : Finset A} (h : F ⊆ G) : firstAndFinite R A k F ≤ firstAndFinite R A k G := by
  unfold firstAndFinite
  apply Algebra.adjoin_mono
  apply Set.union_subset_union_right
  apply Set.iUnion_mono
  intro i
  exact Set.image_mono (by exact_mod_cast h)

theorem tprod_eq_prod_singleAlgHom (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (f : Fin (k + 1) → A) :
    PiTensorProduct.tprod R f = ∏ i, PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) i (f i) := by
  classical
  simp only [PiTensorProduct.singleAlgHom_apply]
  have := map_prod (PiTensorProduct.tprodMonoidHom R (A := fun _ : Fin (k + 1) => A))
    (fun u => MonoidHom.mulSingle (fun _ : Fin (k + 1) => A) u (f u)) Finset.univ
  refine Eq.trans ?_ this
  simp only [MonoidHom.mulSingle_apply]
  rw [Finset.univ_prod_mulSingle]
  rfl

theorem exists_finset_mem_firstAndFinite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (x : PiTensorProduct R (fun _ : Fin (k + 1) => A)) : ∃ F : Finset A, x ∈ firstAndFinite R A k F := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine ⟨Finset.univ.image f, ?_⟩
    refine Subalgebra.smul_mem _ ?_ r
    rw [tprod_eq_prod_singleAlgHom]
    refine Subalgebra.prod_mem _ fun i _ => ?_
    apply Algebra.subset_adjoin
    refine Or.inr (Set.mem_iUnion.2 ⟨i, f i, by simp, rfl⟩)
  | add x y hx hy =>
    obtain ⟨F, hF⟩ := hx
    obtain ⟨G, hG⟩ := hy
    exact ⟨F ∪ G, Subalgebra.add_mem _ (firstAndFinite_mono R A k Finset.subset_union_left hF)
      (firstAndFinite_mono R A k Finset.subset_union_right hG)⟩

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_mem_tensorPowerFirstFactorAdjoinFinset : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (x : PiTensorProduct R (fun _ : Fin (k + 1) => A)), ∃ F : Finset A, x ∈ firstAndFinite R A k F := by
  first | (exact @GlobalTheory.EtC.exists_finset_mem_firstAndFinite) | (exact GlobalTheory.EtC.exists_finset_mem_firstAndFinite) | (intros; apply GlobalTheory.EtC.exists_finset_mem_firstAndFinite  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_isIntegral (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A) :
    Algebra.IsIntegral R (firstAndFinite R A k F) := by
  unfold firstAndFinite
  apply Algebra.IsIntegral.adjoin
  rintro x (⟨a, rfl⟩ | hx)
  · exact (Algebra.IsIntegral.isIntegral a).map _
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, -, rfl⟩ := hi
    exact (Algebra.IsIntegral.isIntegral a).map _

end GlobalTheory.EtC

example : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A), Algebra.IsIntegral R (firstAndFinite R A k F) := GlobalTheory.EtC.firstAndFinite_isIntegral
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_isIntegral : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A), Algebra.IsIntegral R (firstAndFinite R A k F) := by
  first | (exact @GlobalTheory.EtC.firstAndFinite_isIntegral) | (exact GlobalTheory.EtC.firstAndFinite_isIntegral) | (intros; apply GlobalTheory.EtC.firstAndFinite_isIntegral  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_fg_over_first : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A), ∃ F' : Finset (firstAndFinite R A k F), Algebra.adjoin R (Set.range (firstIncl R A k F) ∪ (F' : Set (firstAndFinite R A k F))) = ⊤ := by
  intro R A _ _ _ k F
  classical
  set S := firstAndFinite R A k F with hS
  let g : Fin (k + 1) × F → S := fun p =>
    ⟨PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) p.1 p.2.1,
      Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.2 ⟨p.1, p.2.1, p.2.2, rfl⟩))⟩
  refine ⟨Finset.univ.image g, ?_⟩
  apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  conv_rhs => rw [hS, firstAndFinite]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  · ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image, Set.mem_range,
      Set.mem_iUnion, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨⟨i, a, ha⟩, rfl⟩, rfl⟩
      exact ⟨i, a, ha, rfl⟩
    · rintro ⟨i, a, ha, rfl⟩
      exact ⟨g (i, ⟨a, ha⟩), ⟨(i, ⟨a, ha⟩), rfl⟩, rfl⟩

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_fg_over_first : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A), ∃ F' : Finset (firstAndFinite R A k F), Algebra.adjoin R (Set.range (firstIncl R A k F) ∪ (F' : Set (firstAndFinite R A k F))) = ⊤ := by
  first | (exact @GlobalTheory.EtC.firstAndFinite_fg_over_first) | (exact GlobalTheory.EtC.firstAndFinite_fg_over_first) | (intros; apply GlobalTheory.EtC.firstAndFinite_fg_over_first  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem hInv_of_finite_over_aic (q : ℕ) [NeZero q] (d : ℕ) (hH : (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R))
    (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D] (hq : IsUnit (q : D))
    (hd : ringKrullDim D ≤ d) (T : Type) [CommRing T] [IsDomain T] [Algebra D T]
    [Algebra.IsIntegral D T] (hT : AIC T) (hTq : HInv q T) (E : Type) [CommRing E] [Algebra D E]
    [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E)
    (hF : Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤) : HInv q E := by
  have hlow := GlobalTheory.T.etaleHomotopyInvariant_integral_killed_of_lowerDim q d hH D hq hd
  have hqE : IsUnit (q : E) := by simpa using hq.map (algebraMap D E)
  set X : Finset (E →ₐ[D] T) := (GlobalTheory.T.finite_retractions_of_adjoin_finset_integral_domain D T E ι F hF).toFinset with hX
  have hXid : ∀ χ ∈ X, χ.comp ι = AlgHom.id D T := fun χ hχ => by simpa [hX] using hχ
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.exists_ne_zero_isNilpotent_mul_finite_inf_fg_ideals D E (E →ₐ[D] T) X (fun χ => RingHom.ker χ)
    (fun χ hχ => GlobalTheory.T.ker_retraction_fg_of_adjoin_finset D T E ι F hF χ (hXid χ hχ))
    (fun Q hQ hQc => by
      obtain ⟨χ, hχι, hχQ⟩ := GlobalTheory.T.exists_retraction_of_monicPolynomialsHaveRoots D T E hT ι Q hQ hQc
      have hmem : χ ∈ X := by simpa [hX] using hχι
      rw [← hχQ]
      exact iInf₂_le χ hmem)
  set I : Ideal E := ⨅ χ ∈ X, RingHom.ker χ with hI
  set J : Ideal E := Ideal.span {algebraMap D E s} with hJ
  have hIJ : I ⊓ J ≤ nilradical E := by
    intro y hy
    obtain ⟨hyI, hyJ⟩ := Ideal.mem_inf.mp hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hyJ
    obtain ⟨m, hm⟩ := hs _ hyI
    refine ⟨2 * m, ?_⟩
    calc (a * algebraMap D E s) ^ (2 * m)
        = a ^ m * (algebraMap D E s * (a * algebraMap D E s)) ^ m := by ring
      _ = 0 := by rw [hm, mul_zero]
  have hJs : ∀ K : Ideal E, J ≤ K → algebraMap D (E ⧸ K) s = 0 := by
    intro K hK
    rw [IsScalarTower.algebraMap_apply D E (E ⧸ K), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hK (Ideal.mem_span_singleton_self _)
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q E I J hIJ hqE (GlobalTheory.T.hInv_quot_iInf_ker_retractions q D T E hq hTq hlow ι X hXid)
    (hlow (E ⧸ J) s hs0 (hJs J le_rfl)) (hlow (E ⧸ (I ⊔ J)) s hs0 (hJs _ le_sup_right))

def subalgebraOfSubringEquiv {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) :
    S ≃+* subalgebraOfSubring S.toSubring where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem hInv_tensorPower_integralClosure : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ k : ℕ, HInv q (PiTensorProduct D (fun _ : Fin (k + 1) => integralClosure D (AlgebraicClosure (FractionRing D)))) := by
  intro q _ d hH D _ _ _ hq hd k
  have hqDp : IsUnit (q : integralClosure D (AlgebraicClosure (FractionRing D))) := by
    simpa using hq.map (algebraMap D (integralClosure D (AlgebraicClosure (FractionRing D))))
  have hTq := GlobalTheory.T.etaleHomotopyInvariance_absolutelyIntegrallyClosed q _ (GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure D) hqDp
  have hqS : ∀ F, IsUnit (q : firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F) :=
    fun F => by simpa using hq.map (algebraMap D (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F))
  refine GlobalTheory.T.hInv_of_directed_union_subalgebras q _ (Finset (integralClosure D (AlgebraicClosure (FractionRing D))))
    (fun F => subalgebraOfSubring (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F).toSubring)
    ?_ ?_ ?_ ?_
  · intro F G hFG x hx
    rw [mem_subalgebraOfSubring] at hx ⊢
    exact Algebra.adjoin_mono (Set.union_subset_union_right _
      (Set.iUnion_mono fun i => Set.image_mono (Finset.coe_subset.mpr hFG))) hx
  · intro x
    obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_mem_tensorPowerFirstFactorAdjoinFinset D _ k x
    exact ⟨F, (mem_subalgebraOfSubring).mpr hF⟩
  · intro F
    simpa using (hqS F).map (subalgebraOfSubringEquiv (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F))
  · intro F
    haveI := GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_isIntegral D (integralClosure D (AlgebraicClosure (FractionRing D))) k F
    obtain ⟨F', hF'⟩ := GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_fg_over_first D (integralClosure D (AlgebraicClosure (FractionRing D))) k F
    exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ (subalgebraOfSubringEquiv _)
      (hInv_of_finite_over_aic q d hH D hq hd _ (GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure D) hTq _ (firstIncl D _ k F) F' hF')

end GlobalTheory.EtC
end
