import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
import BuildAid.ForwardExisting

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ClosedPt

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CxPts TopologicalSpace

theorem exists_residue_eval : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ),
    LocallyOfFiniteType p → ∀ (B : LB Y), B.IsLB → ∀ z : Y, IsClosed ({z} : Set Y) →
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (e : B.Sec →+ K),
      (∀ (a : F) (s : B.Sec), e (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ a • s) = algebraMap F K a * e s) ∧
      (∀ s : B.Sec, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s → e s ≠ 0) ∧
      ∀ τ : K →+* ℂ, τ.comp (algebraMap F K) = σ → ∃ (y : GlobalTheory.CxPts p σ) (i : B.ι),
        y.1 (IsLocalRing.closedPoint ℂ) = z ∧ ∀ s : B.Sec, GlobalTheory.CxPts.secVal p σ s i y = τ (e s) := by
  intro F _ Y p σ hp B hB z hz
  obtain ⟨i, hzi⟩ : ∃ i, z ∈ B.U i := Opens.mem_iSup.1 (by rw [hB.cover]; trivial)
  obtain ⟨U, hU, hzU, hUi⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hzi
  replace hU : IsAffineOpen U := hU
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have hftA : Algebra.FiniteType F Γ(Y, U) := hft
  set x0 := hU.primeIdealOf ⟨z, hzU⟩ with hx0
  have hfx : hU.fromSpec x0 = z := hU.fromSpec_primeIdealOf ⟨z, hzU⟩
  have hcl : IsClosed ({x0} : Set (PrimeSpectrum Γ(Y, U))) := by
    have h1 : IsClosed (hU.fromSpec.base ⁻¹' {z}) := hz.preimage hU.fromSpec.base.hom.continuous
    have h2 : hU.fromSpec.base ⁻¹' {z} = {x0} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hq
        exact hU.fromSpec.isOpenEmbedding.injective (hq.trans hfx.symm)
      · rintro rfl; exact hfx
    rw [h2] at h1
    exact h1
  have hmax : x0.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hcl
  let P := x0.asIdeal
  letI : Field (Γ(Y, U) ⧸ P) := Ideal.Quotient.field P
  have : Algebra.FiniteType F (Γ(Y, U) ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) Ideal.Quotient.mk_surjective
  have hfin : Module.Finite F (Γ(Y, U) ⧸ P) := finite_of_finite_type_of_isJacobsonRing F _
  have hmem : ∀ f : Γ(Y, U), z ∈ Y.basicOpen f ↔ f ∉ P := by
    intro f
    have h1 : x0 ∈ hU.fromSpec ⁻¹ᵁ Y.basicOpen f ↔ hU.fromSpec x0 ∈ Y.basicOpen f := Iff.rfl
    rw [hfx, hU.fromSpec_preimage_basicOpen] at h1
    exact h1.symm.trans (PrimeSpectrum.mem_basicOpen _ _)
  let e : B.Sec →+ Γ(Y, U) ⧸ P :=
    { toFun := fun s => Ideal.Quotient.mk P (resG Y hUi (s.f i))
      map_zero' := by simp
      map_add' := fun s t => by simp only [GlobalTheory.LB.add_f, map_add] }
  refine ⟨Γ(Y, U) ⧸ P, inferInstance, inferInstance, hfin, e, ?_, ?_, ?_⟩
  · intro a s
    change Ideal.Quotient.mk P (resG Y hUi ((algX p ⊤ a • s).f i)) = _ * Ideal.Quotient.mk P _
    have hres : resG Y (hUi.trans le_top) (algX p ⊤ a) = algX p U a :=
      RingHom.congr_fun (GlobalTheory.TopForm.resG_comp_algX p (hUi.trans le_top)) a
    rw [GlobalTheory.LB.smul_f, map_mul, map_mul, GlobalTheory.LB.resG_resG, hres]
    rfl
  · intro s hs
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hs
    have hki : z ∈ B.U i ⊓ B.U k := ⟨hzi, Y.basicOpen_le _ hk⟩
    have hrel := GlobalTheory.LB.sec_rel s i k (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) inf_le_right le_rfl
    have h1 : z ∈ Y.basicOpen (resG Y (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) (s.f i)) := by
      rw [hrel, Scheme.basicOpen_mul, Y.basicOpen_of_isUnit
        ((B.g i k).isUnit.map (resG Y le_rfl))]
      refine ⟨hki, ?_⟩
      have : resG Y (inf_le_right : B.U i ⊓ B.U k ≤ B.U k) (s.f k) =
          Y.presheaf.map (homOfLE (inf_le_right : B.U i ⊓ B.U k ≤ B.U k)).op (s.f k) := rfl
      rw [this, Scheme.basicOpen_res]
      exact ⟨hki, hk⟩
    have h2 : z ∈ Y.basicOpen (s.f i) := by
      have : resG Y (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) (s.f i) =
          Y.presheaf.map (homOfLE (inf_le_left : B.U i ⊓ B.U k ≤ B.U i)).op (s.f i) := rfl
      rw [this, Scheme.basicOpen_res] at h1
      exact h1.2
    have h3 : z ∈ Y.basicOpen (resG Y hUi (s.f i)) := by
      have : resG Y hUi (s.f i) = Y.presheaf.map (homOfLE hUi).op (s.f i) := rfl
      rw [this, Scheme.basicOpen_res]
      exact ⟨hzU, h2⟩
    change Ideal.Quotient.mk P _ ≠ 0
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact (hmem _).1 h3
  · intro τ hτ
    let φ : Γ(Y, U) →+* ℂ := τ.comp (Ideal.Quotient.mk P)
    have hφ : ∀ a, φ (algX p U a) = σ a := fun a => by
      rw [← hτ]; rfl
    refine ⟨ofHom hU φ hφ, i, ?_, fun s => ?_⟩
    · have hker : RingHom.ker φ = P := by
        rw [RingHom.ker_comp_of_injective _ τ.injective]
        exact Ideal.mk_ker
      have hpt : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ) = x0 := by
        apply PrimeSpectrum.ext
        change Ideal.comap φ (IsLocalRing.maximalIdeal ℂ) = P
        rw [IsLocalRing.maximalIdeal_eq_bot]
        exact hker
      change hU.fromSpec ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ)) = z
      rw [hpt, hfx]
    · rw [secVal_apply, ← ev_res hUi (ofHom_mem hU φ hφ), ev_ofHom]
      rfl

end GlobalTheory.CompanionTheory.Ar.ClosedPt
end
end

section
open Matrix

namespace GlobalTheory.CompanionTheory.Arith.DedekindDescent

theorem single_ext (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (σ : F →+* ℂ) {κ : Type} [Fintype κ] (b : κ → ℂ)
    (hb : ∀ c : κ → F, ∑ k, σ (c k) * b k = 0 → c = 0) (x : κ → K)
    (h : ∀ τ : K →+* ℂ, τ.comp (algebraMap F K) = σ → ∑ k, b k * τ (x k) = 0) : x = 0 := by
  let _ : Algebra F ℂ := σ.toAlgebra
  have : CharZero F := ⟨fun a b hab => Nat.cast_injective (R := ℂ) (by
    have := congrArg σ hab
    simpa only [map_natCast] using this)⟩
  have key : ∀ y : K, ∑ k, σ (Algebra.trace F K (x k * y)) * b k = 0 := by
    intro y
    have htr : ∀ k, σ (Algebra.trace F K (x k * y)) = ∑ φ : K →ₐ[F] ℂ, φ (x k * y) :=
      fun k => trace_eq_sum_embeddings ℂ (x := x k * y)
    simp only [htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun φ _ => ?_
    have hφ := h (φ : K →+* ℂ) φ.comp_algebraMap
    have hsplit : ∑ k, φ (x k * y) * b k = φ y * ∑ k, b k * (φ : K →+* ℂ) (x k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, AlgHom.coe_toRingHom]
      ring
    rw [hsplit, hφ, mul_zero]
  funext k0
  by_contra hne
  have h0 := congrFun (hb _ (key (x k0)⁻¹)) k0
  simp only [Pi.zero_apply] at h0 hne
  rw [mul_inv_cancel₀ hne, ← map_one (algebraMap F K), Algebra.trace_algebraMap, nsmul_eq_mul,
    mul_one, Nat.cast_eq_zero] at h0
  exact (Module.finrank_pos (R := F) (M := K)).ne' h0

theorem linIndep_descent : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (J : Type) (K : J → Type) [∀ j, Field (K j)] [∀ j, Algebra F (K j)] [∀ j, FiniteDimensional F (K j)] (ι : Type) [Fintype ι] (v : ι → ∀ j, K j), (∀ a : ι → F, (∀ j, ∑ l, algebraMap F (K j) (a l) * v l j = 0) → a = 0) → ∀ d : ι → ℂ, (∀ j (τ : K j →+* ℂ), τ.comp (algebraMap F (K j)) = σ → ∑ l, d l * τ (v l j) = 0) → d = 0 := by
  intro F _ σ J K _ _ _ ι _ v hv d hd
  let _ : Algebra F ℂ := σ.toAlgebra
  let S := Submodule.span F (Set.range d)
  have : FiniteDimensional F S := FiniteDimensional.span_of_finite F (Set.finite_range d)
  let B := Module.finBasis F S
  have hmem : ∀ l, d l ∈ S := fun l => Submodule.subset_span ⟨l, rfl⟩
  have hval : ∀ e : Fin (Module.finrank F S) → F,
      ((∑ k, e k • B k : S) : ℂ) = ∑ k, σ (e k) * (B k : ℂ) := by
    intro e
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra]
  have hdc : ∀ l, d l = ∑ k, σ (B.repr ⟨d l, hmem l⟩ k) * (B k : ℂ) := by
    intro l
    rw [← hval]
    exact (congrArg Subtype.val (B.sum_repr ⟨d l, hmem l⟩)).symm
  have hbind : ∀ e : Fin (Module.finrank F S) → F, ∑ k, σ (e k) * (B k : ℂ) = 0 → e = 0 := by
    intro e he
    have h1 : ∑ k, e k • B k = 0 := by
      apply Subtype.ext
      rw [hval, he]
      rfl
    funext k
    exact Fintype.linearIndependent_iff.1 B.linearIndependent e h1 k
  have hx : ∀ j k, ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j = 0 := by
    intro j
    have hτ' : ∀ τ : K j →+* ℂ, τ.comp (algebraMap F (K j)) = σ →
        ∀ a, τ (algebraMap F (K j) a) = σ a := fun τ hτ a => by rw [← hτ]; rfl
    have := single_ext F (K j) σ (fun k => (B k : ℂ)) hbind
      (fun k => ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j) (fun τ hτ => by
        refine Eq.trans ?_ (hd j τ hτ)
        simp only [map_sum, map_mul, hτ' τ hτ]
        rw [Finset.sum_congr rfl fun l _ => congrArg (· * τ (v l j)) (hdc l)]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
    intro k
    exact congrFun this k
  have hc0 : ∀ k, (fun l => B.repr ⟨d l, hmem l⟩ k) = 0 := fun k => hv _ fun j => hx j k
  funext l
  rw [hdc l, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := congrFun (hc0 k) l
  simp only [Pi.zero_apply] at this
  rw [this, map_zero, zero_mul]

end GlobalTheory.CompanionTheory.Arith.DedekindDescent
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.VanDescent

theorem exists_closed_mem_notMem : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F), LocallyOfFiniteType p → ∀ (U O : Y.Opens), ¬ U ≤ O → ∃ z : Y, IsClosed ({z} : Set Y) ∧ z ∈ U ∧ z ∉ O := by
  intro F _ Y p hp U O hUO
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, hzU, hzO⟩ := Set.not_subset.1 hUO
  obtain ⟨y, ⟨hy, hy'⟩, hc⟩ := nonempty_inter_closedPoints (Z := (U : Set Y) ∩ (O : Set Y)ᶜ)
    ⟨z, hzU, hzO⟩ (U.isOpen.isLocallyClosed.inter O.isOpen.isClosed_compl.isLocallyClosed)
  exact ⟨y, hc, hy, hy'⟩

theorem secVal_eq_zero_of_le {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ}
    {B : LB Y} {O : Y.Opens} (s : B.Sec) (hs : nonzeroLocus s ≤ O) (i : B.ι) (y : CxPts p σ)
    (hy : y ∉ ptsIn p σ O) : secVal p σ s i y = 0 := by
  by_contra h
  by_cases hi : y ∈ ptsIn p σ (B.U i)
  · exact hy (ptsIn_mono hs ((secVal_ne_zero_iff s hi).1 h))
  · exact h (by rw [secVal_apply]; exact ev_of_notMem hi _)

theorem vanish_descent : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ), LocallyOfFiniteType p → ∀ (B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y), B.IsLB → ∀ (O : Y.Opens) (x : GlobalTheory.SecC p σ B), (∀ i y, y ∉ GlobalTheory.CxPts.ptsIn p σ O → GlobalTheory.SecC.val x i y = 0) → ∃ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → B.Sec), (∀ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (ss j) ≤ O) ∧ GlobalTheory.SecC.val x = ∑ j, as j • GlobalTheory.CxPts.secVal p σ (ss j) := by
  intro F _ Y p σ hp B hB O x hx
  let J := {z : Y // IsClosed ({z} : Set Y) ∧ z ∉ O}
  have hpt := fun j : J => GlobalTheory.CompanionTheory.Ar.ClosedPt.exists_residue_eval F Y p σ hp B hB j.1 j.2.1
  choose K instF instA instFD e he_smul he_ne he_pt using hpt
  let G : Submodule ℂ (B.ι → CxPts p σ → ℂ) :=
    Submodule.span ℂ {f | ∃ s : B.Sec, nonzeroLocus s ≤ O ∧ secVal p σ s = f}
  let Z : Submodule ℂ (B.ι → CxPts p σ → ℂ) :=
    { carrier := {v | ∀ i y, y ∉ ptsIn p σ O → v i y = 0}
      add_mem' := fun {u v} hu hv i y hy => by simp [hu i y hy, hv i y hy]
      zero_mem' := fun i y _ => rfl
      smul_mem' := fun c v hv i y hy => by simp [hv i y hy] }
  have hGZ : G ≤ Z := Submodule.span_le.2 (by
    rintro _ ⟨s, hs, rfl⟩ i y hy
    exact secVal_eq_zero_of_le s hs i y hy)
  have key : ∀ (n : ℕ) (b : Fin n → B.Sec) (d : Fin n → ℂ) (g : B.ι → CxPts p σ → ℂ), g ∈ G →
      (∑ l, d l • secVal p σ (b l) + g) ∈ Z → (∑ l, d l • secVal p σ (b l) + g) ∈ G := by
    intro n
    induction n with
    | zero => intro b d g hg _; simpa using hg
    | succ m ih =>
      intro b d g hg hv
      by_cases H : ∀ a : Fin (m + 1) → F,
          (∀ j, ∑ l, algebraMap F (K j) (a l) * e j (b l) = 0) → a = 0
      · have hz : ∀ j (τ : K j →+* ℂ), τ.comp (algebraMap F (K j)) = σ →
            ∑ l, d l * τ (e j (b l)) = 0 := by
          intro j τ hτ
          obtain ⟨y, i, hyz, hy⟩ := he_pt j τ hτ
          have hyO : y ∉ ptsIn p σ O := fun h => j.2.2 (hyz ▸ mem_ptsIn.1 h)
          have h1 := hv i y hyO
          have h2 := hGZ hg i y hyO
          simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h2, add_zero,
            hy] at h1
          exact h1
        have hd : d = 0 := GlobalTheory.CompanionTheory.Arith.DedekindDescent.linIndep_descent F σ J K (Fin (m + 1)) (fun l j => e j (b l)) H d hz
        subst hd
        simpa using hg
      · push Not at H
        obtain ⟨a, ha0, ha⟩ := H
        have hes : ∀ j, e j (∑ l, algX p ⊤ (a l) • b l) = 0 := fun j => by
          simp only [map_sum, he_smul]
          exact ha0 j
        have hsO : nonzeroLocus (∑ l, algX p ⊤ (a l) • b l) ≤ O := by
          by_contra h
          obtain ⟨z, hzc, hzs, hzO⟩ := exists_closed_mem_notMem F Y p hp _ O h
          exact he_ne ⟨z, hzc, hzO⟩ _ hzs (hes _)
        have hsG : secVal p σ (∑ l, algX p ⊤ (a l) • b l) ∈ G :=
          Submodule.subset_span ⟨_, hsO, rfl⟩
        have hsv : secVal p σ (∑ l, algX p ⊤ (a l) • b l) = ∑ l, σ (a l) • secVal p σ (b l) := by
          simp only [map_sum, secVal_smul]
        rw [hsv] at hsG
        obtain ⟨l₀, hl₀⟩ := Function.ne_iff.1 ha
        have hσ : σ (a l₀) ≠ 0 := (map_ne_zero σ).2 hl₀
        obtain ⟨c, hc⟩ : ∃ c, c = d l₀ * (σ (a l₀))⁻¹ := ⟨_, rfl⟩
        have hdc : d l₀ = c * σ (a l₀) := by rw [hc, inv_mul_cancel_right₀ hσ]
        have heq : ∑ l, d l • secVal p σ (b l) + g =
            ∑ i, (d (l₀.succAbove i) - c * σ (a (l₀.succAbove i))) •
              secVal p σ (b (l₀.succAbove i)) + (g + c • ∑ l, σ (a l) • secVal p σ (b l)) := by
          rw [Fin.sum_univ_succAbove _ l₀, Fin.sum_univ_succAbove (fun l => σ (a l) • _) l₀]
          simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hdc]
          module
        rw [heq] at hv ⊢
        exact ih _ _ _ (G.add_mem hg (G.smul_mem c hsG)) hv
  have hxspan : x ∈ Submodule.span ℂ (Set.range (SecC.of p σ : B.Sec → SecC p σ B)) :=
    by rw [SecC.span_range_of (p := p) (σ := σ) (B := B)]; exact Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hxspan
  choose b hb using fun i => (g i).2
  have hval : SecC.val x = ∑ l, f l • secVal p σ (b l) + 0 := by
    rw [← hfg, add_zero, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← hb l, SecC.val_of]
  have hxZ : SecC.val x ∈ Z := hx
  rw [hval] at hxZ
  have hmem := key n b f 0 G.zero_mem hxZ
  rw [← hval] at hmem
  obtain ⟨m, as, ss, hss⟩ := Submodule.mem_span_set'.1 hmem
  choose t ht1 ht2 using fun j => (ss j).2
  exact ⟨m, as, t, ht1, by rw [← hss]; exact Finset.sum_congr rfl fun j _ => by rw [ht2]⟩

end GlobalTheory.CompanionTheory.VanDescent
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_section_finite_combination : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ), LocallyOfFiniteType p → ∀ (B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y), B.IsLB → ∀ (O : Y.Opens) (x : GlobalTheory.SecC p σ B), (∀ i y, y ∉ GlobalTheory.CxPts.ptsIn p σ O → GlobalTheory.SecC.val x i y = 0) → ∃ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → B.Sec), (∀ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (ss j) ≤ O) ∧ GlobalTheory.SecC.val x = ∑ j, as j • GlobalTheory.CxPts.secVal p σ (ss j) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.VanDescent.vanish_descent
end
