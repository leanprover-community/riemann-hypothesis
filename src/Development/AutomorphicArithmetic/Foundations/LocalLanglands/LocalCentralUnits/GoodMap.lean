import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NameLaws
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PairCheckThreeTwo
import Development.DiscreteGroups.GlobalIrreducibility.DzKSchur
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ResBase
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.DiscreteGroups.GlobalIrreducibility.DzGalTR
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameRecAll
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsSemisimpleInducedParam
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsoUniq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameUniq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ParUniq
import Development.DiscreteGroups.GlobalIrreducibility.LTw
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TwTame
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameArt
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.IsTateEpsUnramTwist
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.TameLpOfCharIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLawsOfLawsLit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCharacterTwist

section
open CategoryTheory Polynomial Matrix GlobalTheory.GLq

namespace UpperTheory.Zero.LLC

private theorem scalar_comm {g n : ℕ} [Fact g.Prime] (c : (ZMod g)ˣ) (x : Gn g n) :
    GeneralLinearGroup.scalar (Fin n) c * x = x * GeneralLinearGroup.scalar (Fin n) c := by
  ext i j
  simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, mul_comm]

private theorem schur_scalar {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) [Simple τ] (s : G)
    (hs : ∀ x : G, s * x = x * s) : ∃ l : ℂ, ∀ v : τ, τ.ρ s v = l • v := by
  let F : τ ⟶ τ := ⟨FGModuleCat.ofHom (τ.ρ s), fun x => by
    ext v
    change τ.ρ s (τ.ρ x v) = τ.ρ x (τ.ρ s v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hs]⟩
  obtain ⟨l, hl⟩ := endomorphism_simple_eq_smul_id ℂ F
  refine ⟨l, fun v => ?_⟩
  have : F.hom.hom.hom v = l • v := by rw [← hl]; rfl
  exact this

private theorem charpoly_lmul {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] {n : ℕ}
    (b : Module.Basis (Fin n) F K) (x : K) (hd : (minpoly F x).natDegree = n) :
    (Algebra.leftMulMatrix b x).charpoly = minpoly F x := by
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h0 : aeval x (Algebra.leftMulMatrix b x).charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx) (Matrix.charpoly_monic _)
    (minpoly.dvd F x h0) (by rw [Matrix.charpoly_natDegree_eq_dim, hd, Fintype.card_fin])

private theorem natDegree_smul {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (c : Fˣ) (x : K) : (minpoly F (algebraMap F K c * x)).natDegree = (minpoly F x).natDegree := by
  have hE : IntermediateField.adjoin F {algebraMap F K c * x} = IntermediateField.adjoin F {x} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F x)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h : algebraMap F K (c⁻¹ : Fˣ) * (algebraMap F K c * x) = x := by
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      have hm := mul_mem (IntermediateField.algebraMap_mem
        (IntermediateField.adjoin F {algebraMap F K c * x}) ((c⁻¹ : Fˣ) : F))
        (IntermediateField.mem_adjoin_simple_self F (algebraMap F K c * x))
      rwa [h] at hm
  rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x), hE]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.nameCentral :
    UpperTheory.Zero.LLC.NameCentral := by
  intro g _ n hn K _ _ hK τ θ hcusp hreg hnames c v
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hn)
  haveI : Simple τ := DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ hcusp.2.1
  obtain ⟨l, hl⟩ := UpperTheory.Zero.LLC.schur_scalar τ (GeneralLinearGroup.scalar (Fin n) c)
    (UpperTheory.Zero.LLC.scalar_comm c)
  obtain ⟨⟨z, hzdeg, hS⟩, -⟩ := UpperTheory.Zero.LLC.pin g n hn K hK θ hreg
  let b : Module.Basis (Fin n) (ZMod g) K := Module.finBasisOfFinrankEq _ _ hK
  let L : Kˣ →* Gn g n := Units.map (Algebra.leftMulMatrix b).toMonoidHom
  let cK : Kˣ := Units.map (algebraMap (ZMod g) K).toMonoidHom c
  let z' : Kˣ := cK * z
  have hz' : (z' : K) = algebraMap (ZMod g) K c * z := rfl
  have hy : ((L z : Gn g n) : Matrix (Fin n) (Fin n) (ZMod g)) = Algebra.leftMulMatrix b z := rfl
  have hsy : ((GeneralLinearGroup.scalar (Fin n) c * L z : Gn g n) : Matrix (Fin n) (Fin n) (ZMod g))
      = Algebra.leftMulMatrix b z' := by
    rw [Units.val_mul, hy, hz', map_mul, AlgHom.commutes]
    ext i j
    simp [GeneralLinearGroup.scalar, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
  have hchar : ∀ (w : Kˣ), (minpoly (ZMod g) (w : K)).natDegree = n → ∀ M : Gn g n,
      (M : Matrix (Fin n) (Fin n) (ZMod g)) = Algebra.leftMulMatrix b w →
      τ.character M = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, (θ (w ^ g ^ j) : ℂ) := by
    intro w hw M hM
    have hc : (M : Matrix (Fin n) (Fin n) (ZMod g)).charpoly = minpoly (ZMod g) (w : K) := by
      rw [hM]
      exact UpperTheory.Zero.LLC.charpoly_lmul b w hw
    refine hnames M ?_ w ?_
    · rw [hc]
      exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
    · rw [hc]
      exact minpoly.aeval _ _
  have hz'deg : (minpoly (ZMod g) (z' : K)).natDegree = n := by
    rw [hz', UpperTheory.Zero.LLC.natDegree_smul]
    exact hzdeg
  have h1 := hchar z hzdeg (L z) hy
  have h2 := hchar z' hz'deg _ hsy
  have hρ : τ.ρ (GeneralLinearGroup.scalar (Fin n) c) = l • (1 : Module.End ℂ τ.V) :=
    LinearMap.ext fun w => by rw [hl]; simp
  have h3 : τ.character (GeneralLinearGroup.scalar (Fin n) c * L z) = l * τ.character (L z) := by
    simp only [FDRep.character, map_mul, hρ, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  have hcpow : ∀ j : ℕ, cK ^ g ^ j = cK := by
    intro j
    ext
    simp [cK, Units.val_pow_eq_pow_val, ← map_pow, ZMod.pow_card_pow]
  have hsum : ∑ j ∈ Finset.range n, (θ (z' ^ g ^ j) : ℂ)
      = (θ cK : ℂ) * ∑ j ∈ Finset.range n, (θ (z ^ g ^ j) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [z', mul_pow, hcpow, map_mul, Units.val_mul]
  rw [h1, h2, hsum] at h3
  have hne : ((-1 : ℂ) ^ (n - 1) * ∑ j ∈ Finset.range n, (θ (z ^ g ^ j) : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hS
  have hl' : l = (θ cK : ℂ) := by
    apply mul_right_cancel₀ hne
    linear_combination -h3
  rw [hl, hl']
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Res

variable {Ω : Type} [Field Ω]

private def toRes (A : ValuationSubring Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω] :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp
    { toFun := fun x => ⟨algebraMap F Ω (x : F), ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.map (algebraMap F Ω).toIntAlgHom)⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }

private theorem toRes_eq_zero_iff (A : ValuationSubring Ω) {F : Type} [Field F] [NumberField F] [Algebra F Ω] (x : 𝓞 F) :
    toRes A F x = 0 ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := by
  unfold toRes
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
  exact A.valuation_lt_one_iff _

private theorem toRes_eq_of_val {A : ValuationSubring Ω} {F F' : Type} [Field F] [NumberField F] [Algebra F Ω]
    [Field F'] [NumberField F'] [Algebra F' Ω] (x : 𝓞 F) (y : 𝓞 F')
    (hxy : A.valuation (algebraMap F Ω (x : F) - algebraMap F' Ω (y : F')) < 1) : toRes A F x = toRes A F' y := by
  unfold toRes
  rw [RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (A.valuation_lt_one_iff _).2 hxy

private theorem exists_emb {A : ValuationSubring Ω} {F : Type} [Field F] [NumberField F] [Algebra F Ω]
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A v) {K : Type} [Field K] (red : 𝓞 F →+* K)
    (hs : Function.Surjective red) (hk : RingHom.ker red = v.asIdeal) :
    ∃ ι : K →+* IsLocalRing.ResidueField A, ∀ x, ι (red x) = toRes A F x := by
  refine ⟨RingHom.liftOfSurjective red hs ⟨toRes A F, fun x hx => ?_⟩, fun x => ?_⟩
  · rw [hk] at hx
    rw [RingHom.mem_ker, toRes_eq_zero_iff]
    exact (hv x).2 hx
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem card_K {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {K : Type} [Field K]
    (red : 𝓞 F →+* K) (hs : Function.Surjective red) (hk : RingHom.ker red = v.asIdeal) :
    Nat.card K = normV v := by
  have e := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs)
  exact (Nat.card_congr e.toEquiv).symm

open Classical in
private theorem range_sub {κ K : Type} [Field κ] [Field K] (ι : K →+* κ) (q : ℕ) (hq : 1 < q) (hc : Nat.card K = q) :
    (ι.range : Set κ) = ((X ^ q - X : κ[X]).roots.toFinset : Set κ) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite K
  have hne : (X ^ q - X : κ[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero κ hq
  have hsub : (ι.range : Set κ) ⊆ ((X ^ q - X : κ[X]).roots.toFinset : Set κ) := by
    rintro _ ⟨y, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_sub, eval_pow, eval_X]
    rw [← map_pow, ← hc, Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Finset.finite_toSet _)
  have h1 : (ι.range : Set κ).ncard = q := by
    rw [RingHom.coe_range, ← Set.image_univ, Set.ncard_image_of_injective _ ι.injective, Set.ncard_univ, hc]
  rw [h1, Set.ncard_coe_finset]
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq κ hq]

private theorem exists_equiv {κ K K' : Type} [Field κ] [Field K] [Field K'] (ι : K →+* κ) (ι' : K' →+* κ) (q : ℕ) (hq : 1 < q)
    (hc : Nat.card K = q) (hc' : Nat.card K' = q) : ∃ e : K ≃+* K', ∀ y, ι' (e y) = ι y := by
  have hr : ι.range = ι'.range := by
    apply SetLike.coe_injective
    rw [range_sub ι q hq hc, range_sub ι' q hq hc']
  let e1 : K ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict ⟨ι.rangeRestrict.injective, ι.rangeRestrict_surjective⟩
  let e2 : K' ≃+* ι'.range := RingEquiv.ofBijective ι'.rangeRestrict ⟨ι'.rangeRestrict.injective, ι'.rangeRestrict_surjective⟩
  refine ⟨(e1.trans (RingEquiv.subringCongr hr)).trans e2.symm, fun y => ?_⟩
  have h2 : ∀ z : ι'.range, ι' (e2.symm z) = z := fun z => by
    have : (e2 (e2.symm z) : κ) = z := by rw [RingEquiv.apply_symm_apply]
    exact this
  exact h2 (RingEquiv.subringCongr hr (e1 y))

end Res

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem res_read {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (D : Ext h g n) (R : Ine (F := E) A →* D.Kˣ) (hR : D.Res R)
    (t : Ine (F := E) A) : ∃ (t' : Ine (F := D.E') A) (x : 𝓞 D.E'),
      (∀ z : Ω, (t : G E Ω) z = (t' : G D.E' Ω) z) ∧
      Valued.v ((D.a' (ineIncl D.h' t') : D.w'.adicCompletion D.E') - algebraMap D.E' (D.w'.adicCompletion D.E') (x : D.E')) < 1 ∧
      ((R t : D.Kˣ) : D.K) = D.red x := by
  obtain ⟨t', ht', e⟩ := DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
  obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _ (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' ⟨t', ht'⟩).le
  have hne := DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx
  refine ⟨⟨t', ht'⟩, x, fun z => by rw [← e]; rfl, hx, ?_⟩
  have := hR t ⟨t', ht'⟩ x (Units.mk0 _ hne) e.symm rfl hx
  rw [this]; rfl

private theorem core {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (D D' : Ext h g n)
    (R : Ine (F := E) A →* D.Kˣ) (R' : Ine (F := E) A →* D'.Kˣ) (hR : D.Res R) (hR' : D'.Res R')
    (hm : ∀ (t : Ine (F := D.E') A) (t' : Ine (F := D'.E') A), (∀ z : Ω, (t : G D.E' Ω) z = (t' : G D'.E' Ω) z) →
      ∀ (x : 𝓞 D.E') (y : 𝓞 D'.E'),
      Valued.v ((D.a' (ineIncl D.h' t) : D.w'.adicCompletion D.E') - algebraMap D.E' (D.w'.adicCompletion D.E') (x : D.E')) < 1 →
      Valued.v ((D'.a' (ineIncl D'.h' t') : D'.w'.adicCompletion D'.E') - algebraMap D'.E' (D'.w'.adicCompletion D'.E') (y : D'.E')) < 1 →
      A.valuation (algebraMap D.E' Ω (x : D.E') - algebraMap D'.E' Ω (y : D'.E')) < 1) :
    ∃ e : D.K ≃+* D'.K, ∀ t, ((R' t : D'.Kˣ) : D'.K) = e (R t : D.Kˣ) := by
  obtain ⟨ι, hι⟩ := exists_emb D.h' D.red D.surj D.ker
  obtain ⟨ι', hι'⟩ := exists_emb D'.h' D'.red D'.surj D'.ker
  have hq : 1 < g ^ n := Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt
  obtain ⟨e, he⟩ := exists_equiv ι ι' (g ^ n) hq ((card_K D.red D.surj D.ker).trans D.card)
    ((card_K D'.red D'.surj D'.ker).trans D'.card)
  refine ⟨e, fun t => ι'.injective ?_⟩
  obtain ⟨t1, x, h1, a1, r1⟩ := res_read hn D R hR t
  obtain ⟨t2, y, h2, a2, r2⟩ := res_read hn D' R' hR' t
  rw [he, r1, r2, hι, hι']
  exact (toRes_eq_of_val x y (hm t1 t2 (fun z => by rw [← h1, h2]) x y a1 a2)).symm

theorem resIndep : ResIndep := by
  intro E Ω _ _ _ _ _ A w h g _ i hi n hn D D' R R' hR hR'
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hq : 1 < g ^ n := Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (g : Ω) (show 0 < g ^ n - 1 by omega)
  refine core hn D D' R R' hR hR' fun t t' htt x y hx hy => ?_
  have hg := DiscreteGroups.sglob.DzType.natCast_mem_of_normV D.w' g n hn D.card
  have hg' := DiscreteGroups.sglob.DzType.natCast_mem_of_normV D'.w' g n hn D'.card
  have h1 := tameRecAll D.E' Ω g A D.w' D.h' hg D.unr D.a' D.ha' π (by rw [D.card]; exact hπ) t x hx
  have h2 := tameRecAll D'.E' Ω g A D'.w' D'.h' hg' D'.unr D'.a' D'.ha' π (by rw [D'.card]; exact hπ) t' y hy
  rw [← htt] at h2
  have e : algebraMap D.E' Ω (x : D.E') - algebraMap D'.E' Ω (y : D'.E') =
      ((t : G D.E' Ω) π / π - algebraMap D'.E' Ω (y : D'.E')) - ((t : G D.E' Ω) π / π - algebraMap D.E' Ω (x : D.E')) := by ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h2 h1)

end UpperTheory.Zero.LLC

end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Pure

private def eta {I K : Type} [Group I] [Field K] (g n : ℕ) (R : I →* Kˣ) (θ : Kˣ →* ℂˣ) (j : ℤ) : I →* ℂˣ :=
  (θ ^ g ^ (j % (n : ℤ)).toNat).comp R

private theorem eta_apply {I K : Type} [Group I] [Field K] (g n : ℕ) (R : I →* Kˣ) (θ : Kˣ →* ℂˣ) (j : ℤ) (t : I) :
    eta g n R θ j t = θ (R t) ^ g ^ (j % (n : ℤ)).toNat := by
  simp [eta, MonoidHom.pow_apply]

end Pure

section Scalars

end Scalars

theorem parEx : ParEx := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz
  haveI : CharZero (HeightOneSpectrum.adicCompletion E w) :=
    (RingHom.charZero_iff (ϕ := i.toRingHom) i.injective).1 inferInstance
  obtain ⟨n, c⟩ := y
  have hcls : GlobalTheory.LocLanglands.cls c.rep = (⟨n, c⟩ : IrrGL _) := by
    simp [GlobalTheory.LocLanglands.cls, IrrCl.cl_rep]
  obtain ⟨⟨ω, -, hω, hωu⟩, -, -, hpos, -⟩ := clBasic _ (⟨n, c⟩ : IrrGL _)
  have hn : 0 < n := hpos hy
  obtain ⟨φ, hφ⟩ := deg_surjective (h := h) 1
  rw [← hcls] at hy hdz
  obtain ⟨hτc, hτu⟩ := typeEx E Ω A w h g i hi n hn c.rep
  obtain ⟨τ, hτ, hτi⟩ := hτc hy hdz
  obtain ⟨D⟩ := extEx E Ω A w h g i hi n hn
  obtain ⟨⟨R, hR⟩, hRs⟩ := resEx E Ω A w h g i hi n hn D
  have hT := hRs R hR
  have hrank := hT.rank
  haveI : Module.Finite (ZMod g) D.K := Module.finite_of_finrank_pos (by omega)
  haveI : Finite D.K := Module.finite_of_finite (ZMod g)
  letI : Fintype D.K := Fintype.ofFinite _
  have hcard : Fintype.card D.K = g ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hrank]
  have hfix : ∀ x : D.Kˣ, x ^ g ^ n = x := fun x => Units.ext (by
    rw [Units.val_pow_eq_pow_val, ← hcard, FiniteField.pow_card])
  have hper : ∀ (x : D.Kˣ) (q r : ℕ), x ^ g ^ (n * q + r) = x ^ g ^ r := by
    intro x q r
    induction q with
    | zero => simp
    | succ q ih => rw [show n * (q + 1) + r = n + (n * q + r) by ring, pow_add, pow_mul, hfix, ih]
  have hmod : ∀ (x : D.Kˣ) (m : ℕ), x ^ g ^ m = x ^ g ^ (m % n) := by
    intro x m
    conv_lhs => rw [← Nat.div_add_mod m n]
    exact hper x _ _
  have hcong : ∀ (x : D.Kˣ) (p q : ℕ), (p : ℤ) ≡ q [ZMOD n] → x ^ g ^ p = x ^ g ^ q := by
    intro x p q hpq
    have h1 : ((p % n : ℕ) : ℤ) = ((q % n : ℕ) : ℤ) := by push_cast; exact hpq
    rw [hmod x p, hmod x q, (by exact_mod_cast h1 : p % n = q % n)]
  obtain ⟨hNex, hNuniq, -, hNtr⟩ := nameLaws g n hn D.K hrank
  obtain ⟨θ, hθr, hθN⟩ := hNex τ hτ
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hex : ∀ j : ℤ, (((j % (n : ℤ)).toNat : ℕ) : ℤ) = j % n := fun j =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hnz.ne')
  have hexlt : ∀ j : ℤ, (j % (n : ℤ)).toNat < n := by
    intro j
    have h1 := hex j
    have h2 := Int.emod_lt_of_pos j hnz
    omega
  have heta : ∀ (j : ℤ) (t : ↥(Ine A)), eta g n R θ j t = θ (R t ^ g ^ (j % (n : ℤ)).toNat) := by
    intro j t
    rw [eta_apply, map_pow]
  have hopen : IsOpen (SetLike.coe (eta g n R θ 0).ker) := by
    refine Subgroup.isOpen_mono ?_ hT.isOpen
    intro t ht
    rw [MonoidHom.mem_ker] at ht ⊢
    rw [heta, ht, one_pow, map_one]
  have hshift : ∀ (j : ℤ) (t t' : ↥(Ine A)), (ineIncl h) t' = φ * (ineIncl h) t * φ⁻¹ →
      eta g n R θ j t' = eta g n R θ (j + 1) t := by
    intro j t t' ht
    rw [heta, heta, hT.frob φ t t' hφ ht, ← pow_mul, ← pow_succ']
    congr 1
    apply hcong
    push_cast [hex]
    exact ((Int.mod_modEq j n).add_right 1).trans (Int.mod_modEq (j + 1) n).symm
  have hinj : ∀ j j' : ℤ, eta g n R θ j = eta g n R θ j' ↔ (n : ℤ) ∣ j - j' := by
    intro j j'
    constructor
    · intro he
      have h1 : θ ^ g ^ (j % (n : ℤ)).toNat = θ ^ g ^ (j' % (n : ℤ)).toNat := by
        refine MonoidHom.ext fun x => ?_
        obtain ⟨t, rfl⟩ := hT.surj x
        have := congrArg (fun f => f t) he
        simpa [eta_apply, MonoidHom.pow_apply] using this
      have h2 := hθr _ _ (hexlt j) (hexlt j') h1
      have h3 : j % (n : ℤ) = j' % n := by rw [← hex j, ← hex j', h2]
      exact Int.ModEq.dvd (show j' ≡ j [ZMOD n] from h3.symm)
    · intro hd
      have h3 : j % (n : ℤ) = j' % n := (Int.modEq_iff_dvd.mpr hd).symm
      simp only [eta, h3]
  obtain ⟨V, hVirr, hVdim, hVφ, hVine, hVtame⟩ := indEx E Ω A w h φ hφ n hn (eta g n R θ) hopen
    hshift hinj (ω (a φ) : ℂ) (Units.ne_zero _)
  have hInFor : InFor g n R θ V := by
    intro t
    rw [hVine t]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : ((j : ℤ) % (n : ℤ)) = j := Int.emod_eq_of_lt (by omega) (by omega)
    rw [heta, h1, Int.toNat_natCast]
  obtain ⟨⟨δ, hδ⟩, hδu, -, hirr, -, -, -, hm, -⟩ := wDBasic E Ω A w h V
  refine ⟨V, hVirr, hVdim, hVtame ?_, ?_, ?_⟩
  · intro j t ht
    rw [heta, hT.wild t ht, one_pow, map_one]
  · intro ω' hω' σ'
    rw [hωu ω' hω']
    have hNC := nameCentral g n hn D.K hrank τ θ hτ hθr hθN
    obtain ⟨ψ, hψ0, hψ⟩ := hτi
    obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hψ0 (LinearMap.ext hcon)
    have hcent : ∀ t : ↥(Ine A), θ (∏ j ∈ Finset.range n, R t ^ g ^ j) = ω (a (ineIncl h t)) := by
      intro t
      obtain ⟨u, hu1, hu2⟩ := resBase E Ω A w h a ha g i hi n hn D R hR t
      have key := hψ (GeneralLinearGroup.scalar (Fin n) u) v
      have hred : GlobalTheory.GLp.red g n (GeneralLinearGroup.scalar (Fin n) u) =
          GeneralLinearGroup.scalar (Fin n) (Units.map (PadicInt.toZMod : ℤ_[g] →+* ZMod g).toMonoidHom u) := by
        ext p q
        by_cases hpq : p = q <;> simp [GlobalTheory.GLp.red, GeneralLinearGroup.scalar, Matrix.diagonal_apply, hpq]
      set z : (HeightOneSpectrum.adicCompletion E w)ˣ :=
        Units.map (i.toRingHom.comp PadicInt.Coe.ringHom).toMonoidHom u with hz
      have hinc : GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n (GeneralLinearGroup.scalar (Fin n) u)) =
          GeneralLinearGroup.scalar (Fin n) z := by
        ext p q
        by_cases hpq : p = q <;> simp [GlobalTheory.GLp.inc, GeneralLinearGroup.scalar, Matrix.diagonal_apply, hpq, z] <;> rfl
      rw [hred, MonoidHom.comp_apply, hinc, hNC, map_smul] at key
      rw [hω z (ψ v)] at key
      have heq := smul_left_injective ℂ hv key
      have hzeq : a (ineIncl h t) = z := Units.ext (by rw [hu1]; simp [z] <;> rfl)
      have hpeq : ∏ j ∈ Finset.range n, R t ^ g ^ j = Units.map (algebraMap (ZMod g) D.K : ZMod g →* D.K)
          (Units.map (PadicInt.toZMod : ℤ_[g] →+* ZMod g).toMonoidHom u) := Units.ext (by simp [hu2])
      rw [hzeq, hpeq]
      exact Units.ext heq
    have hδeq : δ = ω.comp a := by
      apply hδu φ δ (ω.comp a) hφ
      · apply Units.ext
        rw [← hδ, hVφ]
        rfl
      · intro t
        apply Units.ext
        rw [← hδ, MonoidHom.comp_apply, ← hcent, map_prod]
        have hpol : V.inePol ↑t = (Multiset.map (fun z => X - C z)
            (do let b ← Multiset.map (fun j => θ (R t ^ g ^ j)) (Multiset.range n); pure (b : ℂ))).prod := by
          rw [hInFor t]
          simp [Finset.prod_eq_multiset_prod, Multiset.map_map]
        rw [(hm t _ hpol).1]
        simp [Finset.prod_eq_multiset_prod]
    rw [hδ σ', hδeq]
    rfl
  · intro g' _ i' hi' n' hn' D' R' hR' θ' hθ'r τ' hτ' hN' σ' hσ' hinfl'
    obtain ⟨hgg, hii⟩ := isoUniq _ g g' i i' hi hi'
    subst g'
    have hi2 : i' = i := hii i' hi'
    subst i'
    have hnn : n' = n := congrArg Sigma.fst hσ'
    subst n'
    have hchar := hτu σ' τ τ' (hσ'.trans hcls.symm) hτ hτ' hτi hinfl'
    have hNτ : Names g n θ' τ := by
      simpa only [Names, hchar] using hN'
    obtain ⟨e, he⟩ := resIndep E Ω A w h g i hi n hn D D' R R' hR hR'
    obtain ⟨hN2, hr2⟩ := hNtr D'.K e τ θ'
    obtain ⟨j, -, hj⟩ := hNuniq τ θ _ hθr (hr2 hθ'r) hθN (hN2 hNτ)
    have hI := (tameUniq E Ω A w h g n D.K R hT θ hθr V hInFor).1 j
    rw [← hj] at hI
    refine ⟨(hirr hVirr).1, fun t => ?_⟩
    rw [hI t]
    apply Finset.prod_congr rfl
    intro k _
    congr 3
    simp only [MonoidHom.comp_apply]
    congr 1
    apply Units.ext
    simp [he t]

end UpperTheory.Zero.LLC

end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

private theorem exists_red {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (ht : TameChar χ) :
    ∃ χ₀ : (ZMod g)ˣ →* ℂˣ, ∀ (u : ℤ_[g]ˣ) (x : (w.adicCompletion E)ˣ),
      (x : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) →
      χ x = χ₀ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u) := by
  let f : ℤ_[g]ˣ →* (ZMod g)ˣ := Units.map (PadicInt.toZMod (p := g)).toMonoidHom
  have hloc : IsLocalHom (PadicInt.toZMod (p := g)) := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ IsLocalRing.maximalIdeal ℤ_[g] := hna
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at h1
    rw [h1] at ha
    exact not_isUnit_zero ha⟩
  have hf : Function.Surjective f :=
    IsLocalRing.surjective_units_map_of_local_ringHom (PadicInt.toZMod (p := g)) (ZMod.ringHom_surjective _) hloc
  let φ : ℤ_[g]ˣ →* (w.adicCompletion E)ˣ :=
    Units.map ((i.toRingHom.comp (algebraMap ℤ_[g] ℚ_[g])).toMonoidHom)
  let c : ℤ_[g]ˣ →* ℂˣ := χ.comp φ
  have hker : f.ker ≤ c.ker := by
    intro u hu
    have h0 : PadicInt.toZMod ((u : ℤ_[g]) - 1) = 0 := by
      have h1 : f u = 1 := hu
      have h2 : PadicInt.toZMod (u : ℤ_[g]) = 1 := congrArg Units.val h1
      rw [map_sub, h2, map_one, sub_self]
    have h3 : (u : ℤ_[g]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact h0
    have h4 : ‖(u : ℤ_[g]) - 1‖ < 1 := PadicInt.mem_nonunits.1 h3
    refine ht (φ u) ?_
    have h5 : ((φ u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 = i (((u : ℤ_[g]) - 1 : ℤ_[g]) : ℚ_[g]) := by
      show i ((u : ℤ_[g]) : ℚ_[g]) - 1 = _
      rw [PadicInt.coe_sub, map_sub, PadicInt.coe_one, map_one]
    rw [h5]
    exact (DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi _).2 (by rwa [← PadicInt.norm_def])
  refine ⟨MonoidHom.liftOfSurjective f hf ⟨c, hker⟩, fun u x hx => ?_⟩
  have hxu : x = φ u := Units.ext hx
  rw [hxu]
  exact (MonoidHom.liftOfRightInverse_comp_apply f _ (Function.rightInverse_surjInv hf) ⟨c, hker⟩ u).symm

private theorem norm_eq_prod {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Nat.card K = g ^ n) (hn : 0 < n) (z : Kˣ) :
    algebraMap (ZMod g) K (Algebra.norm (ZMod g) (z : K)) = ∏ j ∈ Finset.range n, ((z ^ g ^ j : Kˣ) : K) := by
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (by omega))
  rw [FiniteField.algebraMap_norm_eq_pow, hK, Nat.card_zmod]
  simp only [Units.val_pow_eq_pow_val]
  rw [Finset.prod_pow_eq_pow_sum, Nat.geomSum_eq hg]

private theorem inflates_tw {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) {n : ℕ} (σ : IrrRep (GL (Fin n) (w.adicCompletion E))) (τ : FDRep ℂ (Gn g n))
    (χ₀ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχs : IsSmoothChar χ)
    (hl : ∀ (u : ℤ_[g]ˣ) (x : (w.adicCompletion E)ˣ), (x : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) →
      χ x = χ₀ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u))
    (hσ : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ) :
    GlobalTheory.SerSys.TameGen.Inflates
      ((irrTwist σ (detChar (Fin n) χ) (hχs.detChar (n := Fin n))).ρ.comp (GeneralLinearGroup.map i.toRingHom))
      (DiscreteGroups.sglob.DzTw.twFD τ χ₀) := by
  have hdet : ∀ k : GL (Fin n) ℤ_[g],
      χ (GeneralLinearGroup.det (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k))) =
        χ₀ (GeneralLinearGroup.det (GlobalTheory.GLp.red g n k)) := by
    intro k
    rw [hl (GeneralLinearGroup.det k) _ ?_]
    · congr 1
      refine Units.ext ?_
      show PadicInt.toZMod ((k : Matrix (Fin n) (Fin n) ℤ_[g]).det) =
        ((GlobalTheory.GLp.red g n k : Matrix (Fin n) (Fin n) (ZMod g))).det
      exact RingHom.map_det _ _
    · show (i.toRingHom.mapMatrix ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix (k : Matrix (Fin n) (Fin n) ℤ_[g]))).det =
        i.toRingHom ((algebraMap ℤ_[g] ℚ_[g]) (k : Matrix (Fin n) (Fin n) ℤ_[g]).det)
      rw [RingHom.map_det, RingHom.map_det]
  obtain ⟨φ, hφ0, hφ⟩ := hσ
  refine ⟨φ, hφ0, fun k v => ?_⟩
  show φ ((((detChar (Fin n) χ₀ (GlobalTheory.GLp.red g n k)) : ℂˣ) : ℂ) • τ.ρ (GlobalTheory.GLp.red g n k) v) =
    (((detChar (Fin n) χ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k))) : ℂˣ) : ℂ) •
      σ.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k)) (φ v)
  rw [map_smul, hφ k v, detChar_apply, detChar_apply, hdet k, MonoidHom.comp_apply]

end UpperTheory.Zero.LLC

open UpperTheory.Zero.LLC in
theorem UpperTheory.Zero.LLC.parTw : UpperTheory.Zero.LLC.ParTw := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz V hV χ hχ ht
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_ringHom (f := i.toRingHom) i.injective
  obtain ⟨⟨ω₀, -, hω₀, -⟩, htw, h1, -⟩ := clBasic (w.adicCompletion E) y
  obtain ⟨⟨ω₁, -, -, huniq⟩, -⟩ := clBasic (w.adicCompletion E) (y.tw χ hχ)
  obtain ⟨hd, -, -, hmul, hcen⟩ := htw χ hχ
  have hB := wDBasic E Ω A w h V
  obtain ⟨-, -, -, hirr, -, -, -, hine, hT⟩ := hB
  obtain ⟨hTd, hTi, hTe, -, -, -, hTt, -⟩ := hT (χ.comp a) (ha.smooth hχ)
  have hI : IsIrrWD (V.lpTwist (χ.comp a) (ha.smooth hχ)) := hTi hV.irr
  refine ⟨hI, ?_, ?_, ?_, ?_⟩
  · rw [hTd, hV.dim, hd]
  · exact hTt (fun σ hσ => (tameArt E Ω A w h a ha χ hχ).1 ht σ hσ) hV.tame
  · intro ω hω σ
    have e1 : ω = ω₀ * χ ^ y.1 := (huniq ω hω).trans (huniq _ (hcen ω₀ hω₀)).symm
    rw [hTe, hV.central ω₀ hω₀ σ, hV.dim, e1]
    simp
  · intro g' _ i' hi' n hn D R hR θ hθ τ hτ hN σ hσ hinf
    obtain ⟨χ₀, hχ₀⟩ := exists_red i' hi' χ ht
    have hrank : Module.finrank (ZMod g') D.K = n := ((resEx E Ω A w h g' i' hi' n hn D).2 R hR).rank
    have hK : Nat.card D.K = g' ^ n := by
      haveI : Module.Finite (ZMod g') D.K := Module.finite_of_finrank_pos (by omega)
      rw [Module.natCard_eq_pow_finrank (K := ZMod g'), Nat.card_zmod, hrank]
    have hχi : IsSmoothChar χ⁻¹ := IsSmoothChar.inv hχ
    have hl : ∀ (u : ℤ_[g']ˣ) (x : (w.adicCompletion E)ˣ), (x : w.adicCompletion E) = i' ((u : ℤ_[g']) : ℚ_[g']) →
        χ⁻¹ x = χ₀⁻¹ (Units.map (PadicInt.toZMod (p := g')).toMonoidHom u) := by
      intro u x hx
      rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hχ₀ u x hx]
    have hcl : cls (irrTwist σ (detChar (Fin n) χ⁻¹) (hχi.detChar (n := Fin n))) = y := by
      have e1 : cls (irrTwist σ (detChar (Fin n) χ⁻¹) (hχi.detChar (n := Fin n))) = (cls σ).tw χ⁻¹ hχi :=
        Sigma.ext rfl (heq_of_eq (clTwist_cl σ _ _).symm)
      have e2 : ∀ (c : (w.adicCompletion E)ˣ →* ℂˣ) (hc : IsSmoothChar c), c = 1 → y.tw c hc = y := by
        rintro c hc rfl
        exact h1 hc
      have hs : IsSmoothChar (χ * χ⁻¹) := IsSmoothChar.mul hχ hχi
      rw [e1, hσ, hmul χ⁻¹ hχi hs]
      exact e2 _ hs (mul_inv_cancel χ)
    have hty := hV.type g' i' hi' n hn D R hR (θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹)
      (DiscreteGroups.sglob.DzTw.isRegularChar_mul D.K χ₀⁻¹ hθ) (DiscreteGroups.sglob.DzTw.twFD τ χ₀⁻¹)
      (DiscreteGroups.sglob.DzTw.isCusp_twFD τ χ₀⁻¹ hτ) (DiscreteGroups.sglob.DzTw.char_twFD D.K hK hn χ₀⁻¹ θ τ hN)
      (irrTwist σ (detChar (Fin n) χ⁻¹) (hχi.detChar (n := Fin n))) hcl
      (inflates_tw i' σ τ χ₀⁻¹ χ⁻¹ hχi hl hinf)
    refine ⟨((wDBasic E Ω A w h _).2.2.2.1 hI).1, fun t => ?_⟩
    have hval : χ (a (ineIncl h t)) = DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t) := by
      obtain ⟨u, hu, hun⟩ := resBase E Ω A w h a ha g' i' hi' n hn D R hR t
      rw [hχ₀ u _ hu]
      show χ₀ _ = χ₀ _
      congr 1
      refine Units.ext ((algebraMap (ZMod g') D.K).injective ?_)
      show algebraMap (ZMod g') D.K (PadicInt.toZMod (u : ℤ_[g'])) = algebraMap (ZMod g') D.K (Algebra.norm (ZMod g') (R t : D.K))
      rw [hun, norm_eq_prod hK hn]
    have hpoint : ∀ j : ℕ, ((θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹) (R t ^ g' ^ j) * (χ.comp a) (ineIncl h t) : ℂˣ) = θ (R t ^ g' ^ j) := by
      intro j
      have e3 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹ (R t ^ g' ^ j) * DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t) = 1 := by
        have e4 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹ = (DiscreteGroups.sglob.DzType.nmChar D.K χ₀)⁻¹ := rfl
        have e5 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t ^ g' ^ j) = DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t) := by
          rw [map_pow, ← MonoidHom.pow_apply, DiscreteGroups.sglob.DzTw.nmChar_pow]
        rw [e4, MonoidHom.inv_apply, e5, inv_mul_cancel]
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hval, mul_assoc, e3, mul_one]
    have hm2 := hine t ((Finset.range n).val.map fun j => (θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹) (R t ^ g' ^ j))
      (by
        simp only [bind_pure_comp, Multiset.fmap_def, Multiset.map_map]
        exact hty.2 t)
    rw [hm2.2.2 (χ.comp a) (ha.smooth hχ), Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => ?_)
    simp only [Function.comp_apply]
    rw [hpoint j]
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GLp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Fin

private theorem charpoly_one {R : Type} [CommRing R] (M : Matrix (Fin 1) (Fin 1) R) :
    M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]

private theorem smul_of_finrank_one {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hV : Module.finrank ℂ V = 1) (f : V →ₗ[ℂ] V) (v : V) : f v = LinearMap.trace ℂ V f • v := by
  obtain ⟨b, hb, hall⟩ := finrank_eq_one_iff'.1 hV
  obtain ⟨c, hc⟩ := hall (f b)
  have hf : f = c • LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨d, rfl⟩ := hall x
    simp [hc.symm, smul_smul, mul_comm]
  have ht : LinearMap.trace ℂ V f = c := by
    rw [hf, map_smul, LinearMap.trace_id, hV]; simp
  rw [ht, hf]; simp

end Fin

section Key

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem fixed_ne_bot_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) {H : Subgroup G} {v : V}
    (hv : ∀ u ∈ H, ρ u v = v) (h0 : v ≠ 0) : fixed σ H ≠ ⊥ := by
  refine (Submodule.ne_bot_iff _).2 ⟨e.toIntertwiningMap v, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, fun h1 => ?_⟩
  · rw [← e.toIntertwiningMap.isIntertwining, hv u hu]
  · have h2 : e.toLinearEquiv v = 0 := h1
    exact h0 (e.toLinearEquiv.injective (h2.trans (map_zero _).symm))

private theorem dz_one : DZ (IrrGL.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one) :=
  fixed_ne_bot_of_equiv (equivRep (IrrRep.det (k := k) (Fin 1) 1 isSmoothChar_one)) (v := (1 : ℂ))
    (fun u _ => by
      show (((1 : kˣ →* ℂˣ) (GeneralLinearGroup.det u) : ℂˣ) : ℂ) • (1 : ℂ) = 1
      simp) (one_ne_zero (α := ℂ))

variable {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem character_one {θ : Kˣ →* ℂˣ} {τ : FDRep ℂ (Gn g 1)} (hN : Names g 1 θ τ) :
    Module.finrank ℂ τ = 1 := by
  have h1 := hN 1 (by rw [charpoly_one]; exact irreducible_X_sub_C _) 1 (by rw [charpoly_one]; simp)
  rw [FDRep.char_one] at h1
  simp at h1
  exact_mod_cast h1

private theorem val_of_inflates {i : ℚ_[g] ≃+* k} {θ : Kˣ →* ℂˣ} {τ : FDRep ℂ (Gn g 1)} (hN : Names g 1 θ τ)
    {σ : IrrRep (GL (Fin 1) k)} {χ : kˣ →* ℂˣ} {hχ : IsSmoothChar χ} (e : σ.ρ.Equiv (IrrRep.det (Fin 1) χ hχ).ρ)
    (hinf : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ)
    (u : ℤ_[g]ˣ) (z : Kˣ) (hz : algebraMap (ZMod g) K (PadicInt.toZMod (u : ℤ_[g])) = z) (x : kˣ)
    (hx : (x : k) = i ((u : ℤ_[g]) : ℚ_[g])) : χ x = θ z := by
  obtain ⟨φ, hφ0, hφ⟩ := hinf
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hφ0 (LinearMap.ext hc)
  set c : GL (Fin 1) ℤ_[g] := GeneralLinearGroup.scalar (Fin 1) u with hc
  have hy0 : ((red g 1 c : Gn g 1) : Mt g 1) 0 0 = PadicInt.toZMod (u : ℤ_[g]) := by
    simp [red, hc, GeneralLinearGroup.scalar]
  have hd : GeneralLinearGroup.det (GeneralLinearGroup.map i.toRingHom (inc g 1 c)) = x := by
    ext
    rw [hx]
    simp [inc, hc, GeneralLinearGroup.scalar]
  have hσ : ∀ (t : GL (Fin 1) k) (y : σ.V), σ.ρ t y = (χ (GeneralLinearGroup.det t) : ℂ) • y := by
    intro t y
    apply e.toLinearEquiv.injective
    have h1 : e.toIntertwiningMap (σ.ρ t y) = (IrrRep.det (Fin 1) χ hχ).ρ t (e.toIntertwiningMap y) := by
      rw [← e.toIntertwiningMap.isIntertwining]
    refine h1.trans ?_
    rw [map_smul]
    rfl
  have hτ : τ.character (red g 1 c) = ((θ z : ℂˣ) : ℂ) := by
    have := hN (red g 1 c) (by rw [charpoly_one]; exact irreducible_X_sub_C _) z
      (by rw [charpoly_one, hy0]; simp [hz])
    simpa using this
  have h2 := hφ c v
  rw [smul_of_finrank_one (character_one hN) (τ.ρ (red g 1 c)) v, map_smul] at h2
  have h3 : LinearMap.trace ℂ τ (τ.ρ (red g 1 c)) = ((θ z : ℂˣ) : ℂ) := hτ
  rw [h3] at h2
  have h4 : (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) (inc g 1 c) (φ v) = ((χ x : ℂˣ) : ℂ) • φ v := by
    rw [MonoidHom.comp_apply, hσ, hd]
  rw [h4] at h2
  exact (Units.ext (smul_left_injective ℂ hv h2)).symm

end Key

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem irr_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : IsIrrWD (WD.lpOfChar h ξ hξ) := by
  refine ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) (fun _ => hξ), rfl, ?_⟩
  have h1 : (WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) (fun _ => hξ)).ρ =
      GlobalTheory.FiniteGL.lineRep ((Units.coeHom ℂ).comp ξ) := by
    refine MonoidHom.ext fun σ => LinearMap.ext fun v => funext fun i => ?_
    simp [GlobalTheory.FiniteGL.lineRep_apply, diagEnd_apply]
  rw [h1]
  exact GlobalTheory.FiniteGL.lineRep_isIrreducible _

private theorem dim_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : (WD.lpOfChar h ξ hξ).lpDim = 1 := by
  simp [WD.lpOfChar]

private theorem dual_lpOfChar {ξ ξ' : Weil h →* ℂˣ} (hξ : IsSmooth ξ) (hξ' : IsSmooth ξ') (e : ∀ σ, ξ' σ = (ξ σ)⁻¹) :
    (WD.lpOfChar h ξ hξ).lpDual = WD.lpOfChar h ξ' hξ' := by
  rw [WD.lpOfChar, WD.lpDual_mk, WD.lpOfChar]
  refine WD.sound ⟨(Pi.basisFun ℂ (Fin 1)).dualBasis.equivFun, fun σ f => ?_, fun f => ?_⟩
  · funext i
    simp [Module.Basis.dualBasis_equivFun, diagEnd_apply, e]
    have h1 : (diagEnd fun _ : Fin 1 => ((ξ σ : ℂ))⁻¹) (Pi.single i 1) = ((ξ σ : ℂ))⁻¹ • (Pi.single i 1 : Fin 1 → ℂ) := by
      funext j
      simp [diagEnd_apply]
    rw [h1, map_smul, smul_eq_mul]
  · funext i
    simp

private theorem typeAt_ofChar {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    TypeAt (IrrGL.ofChar χ hχ) (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)) := by
  intro g _ i hi n hn D R hR θ hθ τ hτ hN σ hcl hinf
  obtain rfl : n = 1 := congrArg Sigma.fst hcl
  obtain ⟨e⟩ : Nonempty (σ.ρ.Equiv (IrrRep.det (Fin 1) χ hχ).ρ) :=
    IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) (w.adicCompletion E))) hcl)
  refine ⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 rfl, fun t => ?_⟩
  obtain ⟨u, hu, hu'⟩ := resBase E Ω A w h a ha g i hi 1 one_pos D R hR t
  have hz : algebraMap (ZMod g) D.K (PadicInt.toZMod (u : ℤ_[g])) = (R t : D.Kˣ) := by
    rw [hu']; simp
  have key := val_of_inflates hN e hinf u (R t) hz (a (ineIncl h t)) hu
  rw [WD.inePol_of_mem_Ine _ t.2, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp [key]

end UpperTheory.Zero.LLC

open UpperTheory.Zero.LLC in
theorem UpperTheory.Zero.LLC.parOne :
    UpperTheory.Zero.LLC.ParOne := by
  intro E Ω _ _ _ _ _ A w h a ha χ hχ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hdz : DZ (IrrGL.ofChar χ hχ) ↔ TameChar χ := by
    have h1 := twTame _ (IrrGL.ofChar 1 isSmoothChar_one) χ hχ one_pos dz_one
    rwa [IrrGL.tw_ofChar, IrrGL.ofChar_inj.2 (one_mul χ)] at h1
  have heig : ∀ σ, ((WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).eig σ).prod = (χ (a σ) : ℂ) := fun σ => by
    rw [eig_lpOfChar]; simp
  have hcc := GlobalTheory.LocLanglands.ExtTwist.hasCentralChar_ofChar χ hχ
  refine ⟨irr_lpOfChar _ _, dim_lpOfChar _ _, hcc, heig, hdz, fun ht => ⟨irr_lpOfChar _ _, dim_lpOfChar _ _, ?_, ?_, typeAt_ofChar ha χ hχ⟩,
    fun χ' hχ' h'' => ⟨IrrGL.tw_ofChar _ _ _ _, ?_⟩, fun h'' => ⟨?_, ?_⟩, fun χ' hχ' e => IrrGL.ofChar_inj.1 e⟩
  · exact (PositivityTheory.LocalParametersCuspidal.DZC.tame_lpOfChar_iff _ _).2 ((tameArt E Ω A w h a ha χ hχ).1 ht)
  · intro ω hω σ
    obtain ⟨ω₀, -, -, hu⟩ := (clBasic _ (IrrGL.ofChar χ hχ)).1
    rw [heig, hu ω hω, hu χ hcc]
  · exact PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.lpOfChar_lpTwist _ _ _ fun σ => rfl
  · exact GlobalTheory.LocLanglands.CuspModel.dualCl_ofChar _ _ _ _ rfl
  · exact dual_lpOfChar _ _ fun σ => rfl

end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

private theorem tw_tw (y : IrrGL k) {χ χ' : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ')
    (h'' : IsSmoothChar (χ * χ')) : (y.tw χ hχ).tw χ' hχ' = y.tw (χ * χ') h'' :=
  ((clBasic k y).2.1 χ hχ).2.2.2.1 χ' hχ' h''

private theorem tw_one (y : IrrGL k) (h1 : IsSmoothChar (1 : kˣ →* ℂˣ)) : y.tw 1 h1 = y :=
  (clBasic k y).2.2.1 h1

private theorem tw_congr (y : IrrGL k) {χ χ' : kˣ →* ℂˣ} (e : χ = χ') (hχ : IsSmoothChar χ)
    (hχ' : IsSmoothChar χ') : y.tw χ hχ = y.tw χ' hχ' := by
  subst e; rfl

private theorem tw_tw_inv' (y : IrrGL k) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    (y.tw χ hχ).tw χ⁻¹ hχ.inv = y := by
  rw [tw_tw y hχ hχ.inv (hχ.mul hχ.inv), tw_congr y (mul_inv_cancel χ) _ isSmoothChar_one, tw_one]

private theorem eq_tw_of_tw_eq {y y' : IrrGL k} {χ χ' : kˣ →* ℂˣ} {hχ : IsSmoothChar χ}
    {hχ' : IsSmoothChar χ'} (e : y.tw χ hχ = y'.tw χ' hχ') :
    y' = y.tw (χ * χ'⁻¹) (hχ.mul hχ'.inv) := by
  rw [← tw_tw y hχ hχ'.inv, e, tw_tw_inv']

end Classes

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem lpOfChar_congr' {ξ ξ' : Weil h →* ℂˣ} (e : ξ = ξ') (hξ : IsSmooth ξ) (hξ' : IsSmooth ξ') :
    WD.lpOfChar h ξ hξ = WD.lpOfChar h ξ' hξ' := by
  subst e; rfl

private theorem lpTwist_congr' (V : WD h) {ξ ξ' : Weil h →* ℂˣ} (e : ξ = ξ') (hξ : IsSmooth ξ)
    (hξ' : IsSmooth ξ') : V.lpTwist ξ hξ = V.lpTwist ξ' hξ' := by
  subst e; rfl

private theorem lpTwist_lpTwist' (V : WD h) {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {χ χ' : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ')
    (h'' : IsSmoothChar (χ * χ')) :
    (V.lpTwist (χ.comp a) (ha.smooth hχ)).lpTwist (χ'.comp a) (ha.smooth hχ') =
      V.lpTwist ((χ * χ').comp a) (ha.smooth h'') := by
  have e : (χ * χ').comp a = χ.comp a * χ'.comp a := MonoidHom.mul_comp _ _ _
  exact (((wDBasic E Ω A w h V).2.2.2.2.2.2.2.2 (χ.comp a) (ha.smooth hχ)).2.2.2.1 (χ'.comp a)
    (ha.smooth hχ') (e ▸ ha.smooth h'')).trans (lpTwist_congr' V e.symm _ _)

private def Rel (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (x : IrrGL (w.adicCompletion E)) (V : WD h) : Prop :=
  (∃ χ hχ, x = .ofChar χ hχ ∧ V = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)) ∨
  ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i) ∧
    ∃ (y₀ : IrrGL (w.adicCompletion E)) (V₀ : WD h) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      y₀.IsCusp ∧ DZ y₀ ∧ Par a y₀ V₀ ∧ x = y₀.tw χ hχ ∧ V = V₀.lpTwist (χ.comp a) (ha.smooth hχ))

private theorem twist_eq_of_tw_eq {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (hq : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i)
    {y₀ y₁ : IrrGL (w.adicCompletion E)} {V₀ V₁ : WD h} {χ χ₁ : (w.adicCompletion E)ˣ →* ℂˣ}
    {hχ : IsSmoothChar χ} {hχ₁ : IsSmoothChar χ₁}
    (c : y₀.IsCusp) (d : DZ y₀) (p : Par a y₀ V₀) (c₁ : y₁.IsCusp) (d₁ : DZ y₁) (p₁ : Par a y₁ V₁)
    (e : y₀.tw χ hχ = y₁.tw χ₁ hχ₁) :
    V₀.lpTwist (χ.comp a) (ha.smooth hχ) = V₁.lpTwist (χ₁.comp a) (ha.smooth hχ₁) := by
  obtain ⟨g, hg, i, hi⟩ := hq
  haveI := hg
  have hy := eq_tw_of_tw_eq e
  have hψ : IsSmoothChar (χ * χ₁⁻¹) := hχ.mul hχ₁.inv
  have pos : 0 < y₀.1 := (clBasic _ y₀).2.2.2.1 c
  have tame : TameChar (χ * χ₁⁻¹) := (twTame _ y₀ _ hψ pos d).1 (hy ▸ d₁)
  have pt := parTw E Ω A w h a ha g i hi y₀ c d V₀ p _ hψ tame
  have hV : V₀.lpTwist ((χ * χ₁⁻¹).comp a) (ha.smooth hψ) = V₁ :=
    (parUniq E Ω A w h a ha g i hi y₁ c₁ d₁ V₁ p₁).1 _ (hy ▸ pt)
  rw [← hV, lpTwist_lpTwist' V₀ ha hψ hχ₁ (hψ.mul hχ₁)]
  exact lpTwist_congr' V₀ (by rw [inv_mul_cancel_right]) _ _

private theorem ofChar_eq_of_tw_eq {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (hq : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i)
    {ψ χ : (w.adicCompletion E)ˣ →* ℂˣ} {hψ : IsSmoothChar ψ} {hχ : IsSmoothChar χ}
    {y₀ : IrrGL (w.adicCompletion E)} {V₀ : WD h} (c : y₀.IsCusp) (d : DZ y₀) (p : Par a y₀ V₀)
    (e : IrrGL.ofChar ψ hψ = y₀.tw χ hχ) :
    WD.lpOfChar h (ψ.comp a) (ha.smooth hψ) = V₀.lpTwist (χ.comp a) (ha.smooth hχ) := by
  obtain ⟨g, hg, i, hi⟩ := hq
  haveI := hg
  have hψ' : IsSmoothChar (ψ * χ⁻¹) := hψ.mul hχ.inv
  have po := parOne E Ω A w h a ha (ψ * χ⁻¹) hψ'
  have hy : y₀ = .ofChar (ψ * χ⁻¹) hψ' := by
    have h1 := tw_tw_inv' y₀ hχ
    rw [← e] at h1
    rw [← h1]
    exact ((parOne E Ω A w h a ha ψ hψ).2.2.2.2.2.2.1 χ⁻¹ hχ.inv hψ').1
  have tame : TameChar (ψ * χ⁻¹) := po.2.2.2.2.1.1 (hy ▸ d)
  have hV : WD.lpOfChar h ((ψ * χ⁻¹).comp a) (ha.smooth hψ') = V₀ :=
    (parUniq E Ω A w h a ha g i hi y₀ c d V₀ p).1 _ (hy ▸ po.2.2.2.2.2.1 tame)
  rw [← hV, (po.2.2.2.2.2.2.1 χ hχ (hψ'.mul hχ)).2]
  exact lpOfChar_congr' (by rw [inv_mul_cancel_right]) _ _

private theorem rel_unique {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {x : IrrGL (w.adicCompletion E)} {V V' : WD h} (H : Rel a ha x V) (H' : Rel a ha x V') : V = V' := by
  rcases H with ⟨χ, hχ, e, rfl⟩ | ⟨hq, y₀, V₀, χ, hχ, c, d, p, e, rfl⟩ <;>
    rcases H' with ⟨χ', hχ', e', rfl⟩ | ⟨hq', y₁, V₁, χ₁, hχ₁, c₁, d₁, p₁, e', rfl⟩
  · have : χ = χ' := (parOne E Ω A w h a ha χ hχ).2.2.2.2.2.2.2.2 χ' hχ' (e.symm.trans e')
    subst this
    rfl
  · exact ofChar_eq_of_tw_eq ha hq' c₁ d₁ p₁ (e.symm.trans e')
  · exact (ofChar_eq_of_tw_eq ha hq c d p (e'.symm.trans e)).symm
  · exact twist_eq_of_tw_eq ha hq c d p c₁ d₁ p₁ (e.symm.trans e')

private theorem rel_tw {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {x : IrrGL (w.adicCompletion E)} {V : WD h} (H : Rel a ha x V)
    {χ : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    Rel a ha (x.tw χ hχ) (V.lpTwist (χ.comp a) (ha.smooth hχ)) := by
  rcases H with ⟨ψ, hψ, rfl, rfl⟩ | ⟨hq, y₀, V₀, ψ, hψ, c, d, p, rfl, rfl⟩
  · have := (parOne E Ω A w h a ha ψ hψ).2.2.2.2.2.2.1 χ hχ (hψ.mul hχ)
    exact Or.inl ⟨ψ * χ, hψ.mul hχ, this.1, this.2⟩
  · exact Or.inr ⟨hq, y₀, V₀, ψ * χ, hψ.mul hχ, c, d, p, tw_tw y₀ hψ hχ (hψ.mul hχ),
      lpTwist_lpTwist' V₀ ha hψ hχ (hψ.mul hχ)⟩

private theorem rel_of_good {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {x : IrrGL (w.adicCompletion E)} (c : x.IsCusp) (gd : GoodCusp x) : ∃ V, Rel a ha x V := by
  rcases gd with h1 | ⟨hq, y₀, χ, hχ, hfix, rfl⟩
  · obtain ⟨-, χ, hχ, e⟩ := (clBasic _ x).2.2.2.2.1 h1
    exact ⟨_, Or.inl ⟨χ, hχ, e, rfl⟩⟩
  · have c₀ : y₀.IsCusp := (((clBasic _ y₀).2.1 χ hχ).2.1).1 c
    obtain ⟨g, hg, i, hi⟩ := id hq
    haveI := hg
    obtain ⟨V₀, p⟩ := parEx E Ω A w h a ha g i hi y₀ c₀ hfix
    exact ⟨_, Or.inr ⟨hq, y₀, V₀, χ, hχ, c₀, hfix, p, rfl, rfl⟩⟩

theorem goodMap : GoodMap := by
  intro E Ω _ _ _ _ _ A w h a ha
  haveI : Nonempty (WD h) := ⟨WD.lpOfChar h (MonoidHom.comp 1 a) (ha.smooth isSmoothChar_one)⟩
  have key : ∀ {x V}, Rel a ha x V → Classical.epsilon (Rel a ha x) = V := fun H =>
    rel_unique ha (Classical.epsilon_spec ⟨_, H⟩) H
  refine ⟨fun x => Classical.epsilon (Rel a ha x), ?_, ?_, ?_⟩
  · intro χ hχ
    exact key (Or.inl ⟨χ, hχ, rfl, rfl⟩)
  · intro x c gd χ hχ
    obtain ⟨V, hV⟩ := rel_of_good ha c gd
    show Classical.epsilon _ = (Classical.epsilon (Rel a ha x)).lpTwist _ _
    rw [key hV, key (rel_tw ha hV hχ)]
  · intro hq y c d
    obtain ⟨g, hg, i, hi⟩ := id hq
    haveI := hg
    obtain ⟨V, p⟩ := parEx E Ω A w h a ha g i hi y c d
    have hV : Rel a ha y V := Or.inr ⟨hq, y, V, 1, isSmoothChar_one, c, d, p, (tw_one y _).symm,
      (((wDBasic E Ω A w h V).2.2.2.2.2.2.2.2 _ _).2.2.2.2.1 (MonoidHom.one_comp a)).symm⟩
    show Par a y (Classical.epsilon (Rel a ha y))
    rw [key hV]
    exact p

end UpperTheory.Zero.LLC

end
end
