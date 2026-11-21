import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Mathlib

section
noncomputable section

namespace Formalism.L2.Pj.CompSplitPfC

open TensorProduct

variable {P S : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [CommRing S] [Algebra P S]
  [Algebra.Etale P S]

theorem cspC_alg (s : S) : algebraMap S (S ⊗[P] FractionRing P) s = s ⊗ₜ (1 : FractionRing P) := rfl

theorem cspC_inj : Function.Injective (algebraMap S (S ⊗[P] FractionRing P)) := by
  have hf : Function.Injective (Algebra.linearMap P (FractionRing P)) :=
    IsFractionRing.injective P (FractionRing P)
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (Algebra.linearMap P (FractionRing P)) hf
  have key : ∀ s : S, algebraMap S (S ⊗[P] FractionRing P) s =
      (LinearMap.lTensor S (Algebra.linearMap P (FractionRing P))) ((TensorProduct.rid P S).symm s) := by
    intro s
    rw [cspC_alg, TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]
  intro a b h
  rw [key, key] at h
  exact (TensorProduct.rid P S).symm.injective (h2 h)

theorem cspC_artinian : IsArtinianRing (S ⊗[P] FractionRing P) := by
  haveI : Algebra.Etale (FractionRing P) (FractionRing P ⊗[P] S) := inferInstance
  haveI : Module.Finite (FractionRing P) (FractionRing P ⊗[P] S) :=
    Algebra.FormallyUnramified.finite_of_free (FractionRing P) _
  haveI : IsArtinianRing (FractionRing P ⊗[P] S) := IsArtinianRing.of_finite (FractionRing P) _
  exact Function.Surjective.isArtinianRing (f := (Algebra.TensorProduct.comm P (FractionRing P) S))
    (Algebra.TensorProduct.comm P (FractionRing P) S).surjective

theorem cspC_range (y : S ⊗[P] integralClosure P (FractionRing P)) :
    ∃ s : S, algebraMap S (S ⊗[P] FractionRing P) s =
      Algebra.TensorProduct.map (AlgHom.id P S) (integralClosure P (FractionRing P)).val y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s z =>
    obtain ⟨p, hp⟩ := (IsIntegrallyClosed.isIntegral_iff (R := P) (K := FractionRing P)).mp z.2
    refine ⟨p • s, ?_⟩
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, cspC_alg, ← hp,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨s', hs'⟩ := hb
    exact ⟨s + s', by rw [map_add, map_add, hs, hs']⟩

theorem cspC_idem_of {r : S ⊗[P] FractionRing P} (hr : IsIdempotentElem r) :
    ∃ s : S, algebraMap S (S ⊗[P] FractionRing P) s = r := by
  have hint : IsIntegral S r := by
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1), Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    simp [mul_sub, hr.eq]
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := P) (S := S)
    (B := FractionRing P)).2 ⟨r, hint⟩
  obtain ⟨s, hs⟩ := cspC_range y
  refine ⟨s, hs.trans ?_⟩
  exact congrArg Subtype.val hy

variable (P) in
include P in
theorem cspC_minimal_unique {q P1 P2 : Ideal S} [hq : q.IsPrime] (h1 : P1 ∈ minimalPrimes S)
    (h2 : P2 ∈ minimalPrimes S) (hq1 : P1 ≤ q) (hq2 : P2 ≤ q) : P1 = P2 := by
  by_contra hne
  let M := Algebra.algebraMapSubmonoid S (nonZeroDivisors P)
  have hP1 : P1.IsPrime := Ideal.minimalPrimes_isPrime h1
  have hP2 : P2.IsPrime := Ideal.minimalPrimes_isPrime h2
  have hM : ∀ I ∈ minimalPrimes S, Disjoint (M : Set S) I := by
    intro I hI
    refine Set.disjoint_left.2 fun m hm hmI => ?_
    have hnzd : m ∈ nonZeroDivisors S := by
      refine mem_nonZeroDivisors_iff_right.2 fun x hx => cspC_inj (P := P) ?_
      have hu := IsLocalization.map_units (S ⊗[P] FractionRing P) (⟨m, hm⟩ : M)
      have h0 : algebraMap S (S ⊗[P] FractionRing P) x * algebraMap S (S ⊗[P] FractionRing P) m = 0 := by
        rw [← map_mul, hx, map_zero]
      rw [map_zero]
      exact (hu.mul_left_eq_zero).1 h0
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hI) hmI hnzd
  let Q1 := Ideal.map (algebraMap S (S ⊗[P] FractionRing P)) P1
  let Q2 := Ideal.map (algebraMap S (S ⊗[P] FractionRing P)) P2
  have hQ1 : Q1.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P1 hP1 (hM P1 h1)
  have hQ2 : Q2.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P2 hP2 (hM P2 h2)
  have hc1 : Q1.comap (algebraMap S (S ⊗[P] FractionRing P)) = P1 :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP1 (hM P1 h1)
  have hc2 : Q2.comap (algebraMap S (S ⊗[P] FractionRing P)) = P2 :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP2 (hM P2 h2)
  have hQne : Q1 ≠ Q2 := fun e => hne (by rw [← hc1, ← hc2, e])
  have := cspC_artinian (P := P) (S := S)
  obtain ⟨r, hr2, hrid, hrall⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne Q2
  have hr1 : r ∈ Q1 := hrall Q1 hQ1 hQne
  obtain ⟨s, hs⟩ := cspC_idem_of (P := P) hrid
  have hs1 : s ∈ P1 := by rw [← hc1, Ideal.mem_comap, hs]; exact hr1
  have hs2 : s ∉ P2 := by rw [← hc2, Ideal.mem_comap, hs]; exact hr2
  have hsid : s * s = s := cspC_inj (P := P) (by rw [map_mul, hs, hrid.eq])
  have h0 : (1 - s) * s ∈ P2 := by
    rw [sub_mul, one_mul, hsid, sub_self]
    exact P2.zero_mem
  have h1s : 1 - s ∈ P2 := (hP2.mem_or_mem h0).resolve_right hs2
  have : (1 : S) ∈ q := by
    have := q.add_mem (hq2 h1s) (hq1 hs1)
    rwa [sub_add_cancel] at this
  exact hq.ne_top ((Ideal.eq_top_iff_one _).2 this)

end Formalism.L2.Pj.CompSplitPfC
end
end

section
noncomputable section

namespace Formalism.L2.Pj.CompSplitPfD

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Topology

theorem cspD_gen {X : Type} [TopologicalSpace X] [QuasiSober X] {W : Set X} (hW : W ∈ irreducibleComponents X) :
    IsGenericPoint hW.1.genericPoint W := by
  have h1 := hW.1.isGenericPoint_genericPoint_closure
  rwa [(isClosed_of_mem_irreducibleComponents W hW).closure_eq] at h1

theorem cspD_max {X : Type} [TopologicalSpace X] [T0Space X] {W : Set X}
    (hW : W ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η W) (z : X) (hz : z ⤳ η) : z = η := by
  have hWc : closure ({η} : Set X) = W := hη
  have h1 : closure ({η} : Set X) ⊆ closure {z} := specializes_iff_closure_subset.mp hz
  have hirr : IsIrreducible (closure ({z} : Set X)) := isIrreducible_singleton.closure
  have h2 : closure ({z} : Set X) ⊆ W := hW.2 hirr (hWc ▸ h1)
  have h3 : closure ({z} : Set X) = closure {η} := le_antisymm (hWc ▸ h2) h1
  exact (inseparable_iff_closure_eq.mpr h3).eq

theorem cspD_disj {X : Type} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    (hloc : ∀ x : X, ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → X), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b)
    (Z Z' : Set X) (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) (hne : Z ≠ Z') :
    Disjoint Z Z' := by
  rw [Set.disjoint_left]
  intro x hxZ hxZ'
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η Z := ⟨_, cspD_gen hZ⟩
  obtain ⟨η', hη'⟩ : ∃ η', IsGenericPoint η' Z' := ⟨_, cspD_gen hZ'⟩
  have s1 : η ⤳ x := by rw [specializes_iff_mem_closure, hη.def]; exact hxZ
  have s2 : η' ⤳ x := by rw [specializes_iff_mem_closure, hη'.def]; exact hxZ'
  obtain ⟨Y, tY, g, hg, ⟨y, rfl⟩, hY⟩ := hloc x
  have hU : IsOpen (Set.range g) := hg.isOpen_range
  obtain ⟨a, ha⟩ : η ∈ Set.range g := s1.mem_open hU ⟨y, rfl⟩
  obtain ⟨b, hb⟩ : η' ∈ Set.range g := s2.mem_open hU ⟨y, rfl⟩
  have hind := hg.toIsEmbedding.toIsInducing
  have maxa : ∀ a', a' ⤳ a → a' = a := fun a' h => hg.injective (by
    have h' : g a' ⤳ g a := h.map hg.continuous
    rw [ha] at h' ⊢; exact cspD_max hZ hη _ h')
  have maxb : ∀ b', b' ⤳ b → b' = b := fun b' h => hg.injective (by
    have h' : g b' ⤳ g b := h.map hg.continuous
    rw [hb] at h' ⊢; exact cspD_max hZ' hη' _ h')
  have ya : a ⤳ y := hind.specializes_iff.mp (by rw [ha]; exact s1)
  have yb : b ⤳ y := hind.specializes_iff.mp (by rw [hb]; exact s2)
  have hab := hY a b y maxa maxb ya yb
  apply hne
  calc Z = closure {η} := hη.def.symm
    _ = closure {η'} := by rw [← ha, ← hb, hab]
    _ = Z' := hη'.def

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem cspD_smooth (Xo : Moduli Dw l) (c : Coeff l) :
    Smooth (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
  first
    | (haveI := Xo.smooth; exact MorphismProperty.pullback_snd _ _ inferInstance)
    | (haveI := Xo.smooth; infer_instance)
    | (haveI := Xo.smooth; haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s; infer_instance)

theorem cspD_local (Xo : Moduli Dw l) (c : Coeff l) (x : Xo.XF c) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → Xo.XF c), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (Xo.XF c).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have hsm := cspD_smooth Xo c
  have h1 := HasRingHomProperty.appLE (P := @Smooth)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp; trivial)
  let ψ : c.F →+* Γ(Xo.XF c, V) :=
    ((pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)).appLE ⊤ V (fun p _ => by simp; trivial)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom
  have hψ : ψ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.bijective) h1
  let _ : Algebra c.F Γ(Xo.XF c, V) := ψ.toAlgebra
  have : Algebra.Smooth c.F Γ(Xo.XF c, V) := hψ
  obtain ⟨r, hr, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := c.F)
    (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)
  refine ⟨PrimeSpectrum (Localization.Away r), inferInstance,
    hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)), ?_, ?_, ?_⟩
  · exact (hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)
  · obtain ⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine ⟨z, ?_⟩
    show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)) z) = x
    rw [hz]
    exact hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro a b y ha hb hay hby
    have : IsIntegrallyClosed (MvPolynomial (Fin n) c.F) := UniqueFactorizationMonoid.instIsIntegrallyClosed
    have hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) →
        a.asIdeal ∈ minimalPrimes (Localization.Away r) := by
      intro a ha
      refine ⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩
      have := ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)
      exact (congrArg PrimeSpectrum.asIdeal this).ge
    exact PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) c.F) (q := y.asIdeal)
      (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay)
      ((PrimeSpectrum.le_iff_specializes _ _).2 hby))

theorem cspD_comp_disj (Xo : Moduli Dw l) (c : Coeff l) (Z Z' : Comp Xo c) (hne : Z ≠ Z') :
    Disjoint (Z : Set (Xo.XF c)) Z' := cspD_disj (cspD_local Xo c) Z Z' Z.2 Z'.2 (fun h => hne (Subtype.ext h))

end Formalism.L2.Pj.CompSplitPfD
end
end
