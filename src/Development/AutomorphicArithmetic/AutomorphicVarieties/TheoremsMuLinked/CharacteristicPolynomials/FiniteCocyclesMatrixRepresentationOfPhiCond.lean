import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.LocallyConstantCocyclesFiniteOfPhi
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.CocField
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IntModel

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem mem_pow_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A) (N : ℕ) (x : M) :
    x ∈ (Ideal.span {t} ^ N • (⊤ : Submodule A M)) ↔ ∃ y, t ^ N • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Submodule.mem_top, hy⟩

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n _ i
      simpa using J.mul_mem_right (n i) hr
    · intro a b ha hb i
      simpa using J.add_mem (ha i) (hb i)
  · intro hx
    have hsum : x = ∑ i, x i • (Pi.single i (1 : R) : Fin r → R) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem lc_iff {R G : Type} [CommRing R] [TopologicalSpace G] (J : Ideal R) {r : ℕ} (f : G → Fin r → R) :
    (IsLocallyConstant fun g => (J • (⊤ : Submodule R (Fin r → R))).mkQ (f g)) ↔
      ∀ i, IsLocallyConstant fun g => Ideal.Quotient.mk J (f g i) := by
  have key : ∀ a b : Fin r → R, (J • (⊤ : Submodule R (Fin r → R))).mkQ a = (J • (⊤ : Submodule R (Fin r → R))).mkQ b ↔
      ∀ i, Ideal.Quotient.mk J (a i) = Ideal.Quotient.mk J (b i) := by
    intro a b
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_pi]
    rfl
  simp only [IsLocallyConstant.iff_eventually_eq, key]
  constructor
  · intro h i x
    exact (h x).mono fun y hy => hy i
  · intro h x
    exact Filter.eventually_all.mpr fun i => h i x

private theorem cocycles_finitely_generated (l : ℕ) [Fact l.Prime] {R G M : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (t : R) (I : Ideal R) (hI : I = Ideal.span {t}) (ht0 : t ≠ 0) (hIne : I ≠ ⊤) [IsPrecomplete I R]
    (hfq : Finite (R ⧸ I)) (hlI : (l : R) ∈ I)
    (ρ : G →* Module.End R M) (Z : Submodule R (G → M)) (hΦ : PhiCond G l)
    (hρ : ∀ (N : ℕ) m, IsLocallyConstant fun g => (I ^ N • (⊤ : Submodule R M)).mkQ (ρ g m))
    (hZ : ∀ z ∈ Z, (∀ N : ℕ, IsLocallyConstant fun g => (I ^ N • (⊤ : Submodule R M)).mkQ (z g)) ∧
      ∀ g h, z (g * h) = z g + ρ g (z h)) : Z.FG := by
  subst hI
  have htinj : ∀ x : M, t • x = 0 → x = 0 := by
    intro x hx
    let b := Module.Free.chooseBasis R M
    apply b.repr.injective
    ext i
    have h := congrArg (fun y => b.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    simpa using (mul_eq_zero.mp h).resolve_left ht0
  have hcancel : ∀ a b : M, t • a = t • b → a = b := fun a b h =>
    sub_eq_zero.mp (htinj _ (by rw [smul_sub, h, sub_self]))
  have hMh : ∀ x : M, (∀ n : ℕ, ∃ y, t ^ n • y = x) → x = 0 := by
    intro x hx
    have hle : Ideal.span {t} ≤ (⊥ : Ideal R).jacobson := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hIne
    have h := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) _ hle
    have hx' : x ∈ ⨅ i, Ideal.span {t} ^ i • (⊤ : Submodule R M) :=
      (Submodule.mem_iInf _).mpr fun n => (mem_pow_smul t n x).mpr (hx n)
    rw [h] at hx'
    simpa using hx'
  let C : Submodule R (G → M) :=
    { carrier := {z | (∀ N : ℕ, IsLocallyConstant fun g => (Ideal.span {t} ^ N • (⊤ : Submodule R M)).mkQ (z g)) ∧
        ∀ g h, z (g * h) = z g + ρ g (z h)}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · simp only [Pi.add_apply, map_add]
          exact (ha1 N).add (hb1 N)
        · simp only [Pi.add_apply, ha2, hb2, map_add]
          abel
      zero_mem' := ⟨fun N => by
          simp only [Pi.zero_apply, map_zero]
          exact IsLocallyConstant.const 0,
        fun g h => by simp⟩
      smul_mem' := by
        rintro r a ⟨ha1, ha2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · simp only [Pi.smul_apply, map_smul]
          exact (ha1 N).comp (fun q => r • q)
        · simp only [Pi.smul_apply, ha2, smul_add, map_smul] }
  have hZC : Z ≤ C := fun z hz => hZ z hz
  haveI : Finite (R ⧸ Ideal.span {t}) := hfq
  haveI hM'fin : Finite (M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) := Module.finite_of_finite (R ⧸ Ideal.span {t})
  let ρ' : G →* AddMonoid.End (M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) :=
    { toFun := fun g => ((Ideal.span {t} • (⊤ : Submodule R M)).mapQ _ (ρ g)
        (Submodule.smul_top_le_comap_smul_top _ _)).toAddMonoidHom
      map_one' := by
        refine AddMonoidHom.ext fun x => ?_
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          simp
          rfl
      map_mul' := by
        intro g h
        refine AddMonoidHom.ext fun x => ?_
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          simp [Module.End.mul_apply]
          rfl }
  have hρ' : ∀ g x, ρ' g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) := fun g x => rfl
  have hS := UpperTheory.V.Pa.Det.locallyConstant_cocycles_finite_of_phi l ρ' hΦ
    (by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul R]
        exact Submodule.smul_mem_smul hlI Submodule.mem_top)
    (by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        have h1 := hρ 1 x
        rw [pow_one] at h1
        exact h1)
  let Ψ : C →ₗ[R] (G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) :=
    LinearMap.pi fun g => (Ideal.span {t} • (⊤ : Submodule R M)).mkQ ∘ₗ (LinearMap.proj g ∘ₗ C.subtype)
  have hΨ : ∀ z g, Ψ z g = Submodule.Quotient.mk (z.1 g) := fun z g => rfl
  have hrange : ∀ z, Ψ z ∈ {z : G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M) | IsLocallyConstant z ∧
      ∀ g h, z (g * h) = z g + ρ' g (z h)} := by
    intro z
    obtain ⟨hz1, hz2⟩ := z.2
    refine ⟨?_, fun g h => ?_⟩
    · have h1 := hz1 1
      rw [pow_one] at h1
      exact h1
    · rw [hΨ, hΨ, hΨ, hz2, hρ', Submodule.Quotient.mk_add]
  have hker : LinearMap.ker Ψ = Ideal.span {t} • (⊤ : Submodule R C) := by
    apply le_antisymm
    · intro z hz
      have hz' : ∀ g, ∃ y, t • y = z.1 g := by
        intro g
        have h0 : Ψ z g = 0 := congrFun (LinearMap.mem_ker.mp hz) g
        rw [hΨ, Submodule.Quotient.mk_eq_zero, ← pow_one (Ideal.span {t})] at h0
        obtain ⟨y, hy⟩ := (mem_pow_smul t 1 _).mp h0
        exact ⟨y, by simpa using hy⟩
      choose y hy using hz'
      obtain ⟨hz1, hz2⟩ := z.2
      have hyC : y ∈ C := by
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · rw [IsLocallyConstant.iff_eventually_eq]
          intro x
          filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp (hz1 (N + 1)) x] with g hg
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hg ⊢
          obtain ⟨w, hw⟩ := (mem_pow_smul t (N + 1) _).mp hg
          refine (mem_pow_smul t N _).mpr ⟨w, hcancel _ _ ?_⟩
          rw [smul_sub, hy, hy, ← hw, ← mul_smul, ← pow_succ']
        · apply hcancel
          rw [hy (g * h), smul_add, ← map_smul, hy g, hy h]
          exact hz2 g h
      have hzt : z = t • (⟨y, hyC⟩ : C) := Subtype.ext (funext fun g => (hy g).symm)
      rw [hzt]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top
    · intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr n _
        rw [LinearMap.mem_ker, map_smul]
        funext g
        rw [Pi.smul_apply, hΨ, ← Submodule.Quotient.mk_smul, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · intro a b ha hb
        exact add_mem ha hb
  have hfin : Finite (C ⧸ LinearMap.ker Ψ) := by
    have hsub : (LinearMap.range Ψ : Set _) ⊆ {z : G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M) | IsLocallyConstant z ∧
        ∀ g h, z (g * h) = z g + ρ' g (z h)} := by
      rintro _ ⟨z, rfl⟩
      exact hrange z
    haveI : Finite (LinearMap.range Ψ) := (hS.subset hsub).to_subtype
    exact Finite.of_equiv _ Ψ.quotKerEquivRange.symm.toEquiv
  rw [hker] at hfin
  haveI : IsHausdorff (Ideal.span {t}) C := by
    refine ⟨fun x hx => ?_⟩
    apply Subtype.ext
    funext g
    show x.1 g = 0
    apply hMh
    intro n
    have h1 := hx n
    rw [SModEq.sub_mem, sub_zero] at h1
    obtain ⟨y, hy⟩ := (mem_pow_smul t n x).mp h1
    exact ⟨y.1 g, by rw [← hy]; rfl⟩
  haveI : Module.Finite R (C ⧸ Ideal.span {t} • (⊤ : Submodule R C)) := Module.Finite.of_finite
  have hCfin : Module.Finite R C := (UpperTheory.V.abelian₂.nakayama R (Ideal.span {t}) C).2 this
  have hCfg : C.FG := Module.Finite.iff_fg.mp hCfin
  haveI := isNoetherian_of_fg_of_noetherian C hCfg
  have hZ'fg : (Z.comap C.subtype).FG := IsNoetherian.noetherian _
  have hZeq : Submodule.map C.subtype (Z.comap C.subtype) = Z :=
    Submodule.map_comap_eq_of_le (by rwa [Submodule.range_subtype])
  rw [← hZeq]
  exact hZ'fg.map _

theorem UpperTheory.V.Th.Det.continuousCocycles_fg_integral_of_phiCond :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {m : ℕ} (σ : G →* GL (Fin m) c.O) (Z : Submodule c.O (G → Fin m → c.O)), PhiCond G l → (∀ i j, AdicCont (maximalIdeal c.O) fun g => W.mat σ g i j) → (∀ z ∈ Z, (∀ i, AdicCont (maximalIdeal c.O) fun g => z g i) ∧ ∀ g h, z (g * h) = z g + W.mat σ g *ᵥ z h) → Z.FG := by
  intro l _ c G _ _ _ _ _ m σ Z hΦ hσ hZ
  obtain ⟨hc, hf, hl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  haveI : IsPrecomplete (maximalIdeal c.O) c.O := hc.toIsPrecomplete
  let ρ : G →* Module.End c.O (Fin m → c.O) :=
    (Matrix.toLinAlgEquiv' (R := c.O) (n := Fin m)).toAlgHom.toRingHom.toMonoidHom.comp (W.mat σ)
  have hρ : ∀ g x, ρ g x = W.mat σ g *ᵥ x := fun g x => rfl
  refine cocycles_finitely_generated l t (maximalIdeal c.O) ht.maximalIdeal_eq ht.ne_zero (maximalIdeal.isMaximal c.O).ne_top
    hf hl ρ Z hΦ (fun N x => ?_) (fun z hz => ⟨fun N => ?_, fun g h => ?_⟩)
  · rw [lc_iff]
    intro i
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    filter_upwards [Filter.eventually_all.2 fun j => (hσ i j N).eventually_eq g] with g' hg'
    simp only [hρ, Matrix.mulVec, dotProduct, map_sum, map_mul, hg']
  · rw [lc_iff]
    exact fun i => (hZ z hz).1 i N
  · rw [hρ]; exact (hZ z hz).2 g h
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem zc_norm {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] (x : PadicAlgCl l) := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val
  have h0 : ‖(x : PadicAlgCl l)‖ = spectralValue (minpoly ℚ_[l] (x : PadicAlgCl l)) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral _))]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem zc_dvd {l : ℕ} [Fact l.Prime] (c : Coef l) (x y : c.O)
    (h : ‖(x : PadicAlgCl l)‖ < ‖(y : PadicAlgCl l)‖) : y ∣ x := by
  rcases ValuationRing.dvd_total y x with h1 | ⟨u, rfl⟩
  · exact h1
  · exfalso
    rw [Subalgebra.coe_mul, norm_mul] at h
    exact absurd (mul_le_of_le_one_right (norm_nonneg _) (zc_norm c u)) (not_le.2 h)

private theorem zc_ev {l : ℕ} [hl : Fact l.Prime] {G : Type} [TopologicalSpace G] (c : Coef l)
    (f : G → c.O) (hf : Continuous fun g => (f g : PadicAlgCl l)) (N : ℕ) (x : G) :
    ∀ᶠ y in nhds x, (l : c.O) ^ N ∣ f y - f x := by
  have hl0 : (l : PadicAlgCl l) ^ N ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  have h1 : ∀ᶠ y in nhds x, ‖(f y : PadicAlgCl l) - f x‖ < ‖(l : PadicAlgCl l) ^ N‖ :=
    ((hf.sub continuous_const).norm.tendsto x).eventually_lt_const (by simpa using norm_pos_iff.2 hl0)
  filter_upwards [h1] with y hy
  exact zc_dvd c _ _ (by push_cast; exact hy)

private theorem zc_split {l : ℕ} [hl : Fact l.Prime] (c c' : Coef l) (hcc : c.O ≤ c'.O) {G : Type} [Group G]
    [TopologicalSpace G] {m : ℕ} (σ : G →* GL (Fin m) c.O) (z : G → Fin m → PadicAlgCl l) (hz : Continuous z)
    (hm : ∀ g i, z g i ∈ c'.O)
    (hc : ∀ g h, z (g * h) = z g + W.mat (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ) g *ᵥ z h) :
    ∃ (n : ℕ) (b : Fin n → PadicAlgCl l) (w : Fin n → G → Fin m → c.O),
      (∀ k, (∀ i, AdicCont (maximalIdeal c.O) fun g => w k g i) ∧
        ∀ g h, w k (g * h) = w k g + W.mat σ g *ᵥ w k h) ∧
      ∀ g i, z g i = ∑ k, b k * (w k g i : PadicAlgCl l) := by
  obtain ⟨-, -, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  letI : Algebra c.O c'.O := (Subalgebra.inclusion hcc).toRingHom.toAlgebra
  have ha : ∀ (a : c.O) (x : c'.O), ((a • x : c'.O) : PadicAlgCl l) = a * x := fun _ _ => rfl
  haveI : IsScalarTower ℤ_[l] c.O c'.O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite c.O c'.O := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI : FaithfulSMul c.O c'.O := (faithfulSMul_iff_algebraMap_injective _ _).2 (Subalgebra.inclusion_injective hcc)
  haveI : Module.Free c.O c'.O := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis c.O c'.O
  let f : G → Fin m → c'.O := fun g i => ⟨z g i, hm g i⟩
  refine ⟨_, fun k => b k, fun k g i => b.coord k (f g i), fun k => ⟨fun i N => ?_, fun g h => ?_⟩, fun g i => ?_⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    filter_upwards [zc_ev c' (fun g => f g i) ((continuous_apply i).comp hz) N x] with y ⟨u, hu⟩
    have e : (l : c'.O) ^ N * u = ((l : c.O) ^ N) • u := by rw [Algebra.smul_def, map_pow, map_natCast]
    rw [Ideal.Quotient.eq, ← map_sub, hu, e, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm N)
  · funext i
    have e : f (g * h) i = f g i + ∑ j, W.mat σ g i j • f h j := Subtype.ext (by
      rw [Subalgebra.coe_add, AddSubmonoidClass.coe_finset_sum]
      exact congrFun (hc g h) i)
    simp only [e, map_add, map_sum, map_smul, Pi.add_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
  · have e := congrArg Subtype.val (b.sum_repr (f g i))
    rw [AddSubmonoidClass.coe_finset_sum] at e
    refine e.symm.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [ha, mul_comm]
    rfl

theorem UpperTheory.V.Th.Det.finite_cocycles_colRep_of_phiCond :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {m : ℕ} (σ : G →* GL (Fin m) (Qbar l)), PhiCond G l → Continuous σ → Module.Finite (Qbar l) (Z1 (Loc.colRep σ)) := by
  intro l _ G _ _ _ _ _ m σ hΦ hσ
  classical
  obtain ⟨c₀, -⟩ := UpperTheory.V.X.So.coefOf l ⊥
  obtain ⟨c, Q, σ₀, -, hQ, hσ₀⟩ := UpperTheory.V.Ws.Eb.intModel c₀ σ hσ
  have hQ' : ∀ g, W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀ g = Q⁻¹ * σ g * Q := fun g => by
    rw [mul_assoc, hQ, inv_mul_cancel_left]
  let Z : Submodule c.O (G → Fin m → c.O) :=
    { carrier := {z | (∀ i, AdicCont (maximalIdeal c.O) fun g => z g i) ∧
          ∀ g h, z (g * h) = z g + W.mat σ₀ g *ᵥ z h}
      add_mem' := fun {a b} ha hb => ⟨fun i N => by
          simp only [Pi.add_apply, map_add]; exact (ha.1 i N).add (hb.1 i N),
        fun g h => by simp only [Pi.add_apply, Matrix.mulVec_add, ha.2 g h, hb.2 g h]; abel⟩
      zero_mem' := ⟨fun i N => by
          simp only [Pi.zero_apply, map_zero]; exact IsLocallyConstant.const _, fun g h => by simp⟩
      smul_mem' := fun r a ha => ⟨fun i N => by
          simp only [Pi.smul_apply, smul_eq_mul, map_mul]
          exact (ha.1 i N).comp (fun x => Ideal.Quotient.mk _ r * x),
        fun g h => by simp only [Pi.smul_apply, Matrix.mulVec_smul, ha.2 g h, smul_add]⟩ }
  obtain ⟨s, hs⟩ := UpperTheory.V.Th.Det.continuousCocycles_fg_integral_of_phiCond c σ₀ Z hΦ hσ₀ fun z hz => hz
  let ι : (G → Fin m → c.O) → G → Fin m → PadicAlgCl l := fun w g i => (w g i : PadicAlgCl l)
  let S : Submodule (PadicAlgCl l) (G → Fin m → PadicAlgCl l) := Submodule.span _ (ι '' s)
  have hS : ∀ w ∈ Z, ι w ∈ S := by
    intro w hw
    rw [← hs] at hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => exact S.zero_mem
    | add y z _ _ hy hz => exact S.add_mem hy hz
    | smul a y _ hy => exact S.smul_mem (a : PadicAlgCl l) hy
  let T : (G → Fin m → PadicAlgCl l) →ₗ[PadicAlgCl l] (G → Fin m → PadicAlgCl l) :=
    (Matrix.toLin' (Q : Matrix (Fin m) (Fin m) (PadicAlgCl l))).compLeft G
  have hfg : (S.map T).FG := (Submodule.fg_span (s.finite_toSet.image ι)).map T
  refine Module.Finite.iff_fg.2 (Submodule.FG.of_le hfg fun z hz => ?_)
  let z' : G → Fin m → PadicAlgCl l := fun g => ((Q⁻¹ : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) *ᵥ z g
  have hT : ∀ g, (Q : Matrix (Fin m) (Fin m) (PadicAlgCl l)) *ᵥ z' g = z g := fun g => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hz' : Continuous z' := continuous_const.matrix_mulVec hz.1
  have hc' : ∀ g h, z' (g * h) = z' g + W.mat (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀) g *ᵥ z' h := by
    intro g h
    have e : W.mat (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀) g =
        ((Q⁻¹ * σ g * Q : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) := by
      rw [← hQ']; rfl
    rw [e, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
    exact congrArg (fun v => ((Q⁻¹ : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) *ᵥ v) (hz.2 g h)
  have hσ₁ : Continuous (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀) := by
    rw [show (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀ : G → _) = fun g => Q⁻¹ * σ g * Q from funext hQ']
    exact (continuous_const.mul hσ).mul continuous_const
  obtain ⟨c', a, hcc, ha, hm⟩ := UpperTheory.V.Th.Det.cocField c _ z' hσ₁ hz' hc'
  obtain ⟨n, b, w, hw, e⟩ := zc_split c c' hcc σ₀ (a • z') (hz'.const_smul a) hm fun g h => by
    simp only [Pi.smul_apply, hc', smul_add, Matrix.mulVec_smul]
  refine ⟨z', ?_, funext hT⟩
  have e' : a • z' = ∑ k, b k • ι (w k) := by
    funext g i
    rw [e, Finset.sum_apply, Finset.sum_apply]
    rfl
  rw [SetLike.mem_coe, ← S.smul_mem_iff ha, e']
  exact S.sum_mem fun k _ => S.smul_mem _ (hS _ (hw k))
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private def matrixFlattenLinearEquiv (K : Type) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) K ≃ₗ[K] (Fin (n * n) → K) where
  toFun X i := X (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  invFun v a b := v (finProdFinEquiv (a, b))
  map_add' X Y := rfl
  map_smul' c X := rfl
  left_inv X := by
    funext a b
    simp
  right_inv v := by
    funext i
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

private theorem continuous_matrix_flatten (K : Type) [Field K] [TopologicalSpace K] (n : ℕ) :
    Continuous (matrixFlattenLinearEquiv K n) := by
  show Continuous fun (X : Matrix (Fin n) (Fin n) K) (i : Fin (n * n)) => X (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  exact continuous_pi fun i => (continuous_apply _).comp (continuous_apply _)

private noncomputable def flattenedMatrixRepresentation {K : Type} [Field K] {G : Type} [Group G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) :
    G →* Matrix (Fin (n * n)) (Fin (n * n)) K where
  toFun g := LinearMap.toMatrix'
    ((matrixFlattenLinearEquiv K n).toLinearMap ∘ₗ R g ∘ₗ (matrixFlattenLinearEquiv K n).symm.toLinearMap)
  map_one' := by
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' g h := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp

private theorem matrix_rep_flatten_apply {K : Type} [Field K] {G : Type} [Group G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) (g : G) (X : Matrix (Fin n) (Fin n) K) :
    Matrix.toLin' (flattenedMatrixRepresentation R g) (matrixFlattenLinearEquiv K n X) = matrixFlattenLinearEquiv K n (R g X) := by
  show Matrix.toLin' (LinearMap.toMatrix' _) _ = _
  rw [Matrix.toLin'_toMatrix']
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply]

private theorem continuous_matrix_rep_flatten {K : Type} [Field K] [TopologicalSpace K] {G : Type} [Group G]
    [TopologicalSpace G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) (hR : ∀ X, Continuous fun g => R g X) :
    Continuous (flattenedMatrixRepresentation R) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun g => LinearMap.toMatrix' ((matrixFlattenLinearEquiv K n).toLinearMap ∘ₗ R g ∘ₗ (matrixFlattenLinearEquiv K n).symm.toLinearMap) i j
  simp only [LinearMap.toMatrix'_apply]
  exact (continuous_matrix_flatten K n).comp (hR _) |>.comp continuous_id |> fun h => (continuous_apply i).comp h

theorem UpperTheory.V.Th.Det.finite_cocycles_matrixRepresentation_of_phiCond :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {n : ℕ} (R : Representation (Qbar l) G (Matrix (Fin n) (Fin n) (Qbar l))), PhiCond G l → (∀ X, Continuous fun g => R g X) → Module.Finite (Qbar l) (Z1 R) := by
  intro l _ G _ _ _ _ _ n R hΦ hR
  let σ : G →* GL (Fin (n * n)) (Qbar l) := (flattenedMatrixRepresentation R).toHomUnits
  have hσ : Continuous σ := by
    rw [Units.continuous_iff]
    refine ⟨continuous_matrix_rep_flatten R hR, ?_⟩
    have h : (fun g => (((σ g)⁻¹ : GL (Fin (n * n)) (Qbar l)) : Matrix (Fin (n * n)) (Fin (n * n)) (Qbar l))) = fun g => flattenedMatrixRepresentation R g⁻¹ := by
      funext g
      rw [← map_inv]
      rfl
    rw [h]
    exact (continuous_matrix_rep_flatten R hR).comp continuous_inv
  have hfin := UpperTheory.V.Th.Det.finite_cocycles_colRep_of_phiCond σ hΦ hσ
  let Φ : (G → Matrix (Fin n) (Fin n) (Qbar l)) →ₗ[Qbar l] (G → Fin (n * n) → Qbar l) :=
    LinearMap.compLeft (matrixFlattenLinearEquiv (Qbar l) n).toLinearMap G
  have hmem : ∀ f ∈ Z1 R, Φ f ∈ Z1 (UpperTheory.V.Loc.colRep σ) := by
    rintro f ⟨hc, hco⟩
    refine ⟨(continuous_matrix_flatten (Qbar l) n).comp hc, fun g h => ?_⟩
    show matrixFlattenLinearEquiv (Qbar l) n (f (g * h)) = matrixFlattenLinearEquiv (Qbar l) n (f g) + Matrix.toLin' (flattenedMatrixRepresentation R g) (matrixFlattenLinearEquiv (Qbar l) n (f h))
    rw [hco g h, map_add, matrix_rep_flatten_apply]
  have hinj : Function.Injective (Φ.restrict hmem) := by
    intro x y hxy
    apply Subtype.ext
    funext g
    have e := congrFun (congrArg Subtype.val hxy) g
    exact (matrixFlattenLinearEquiv (Qbar l) n).injective e
  exact Module.Finite.of_injective (Φ.restrict hmem) hinj
end
