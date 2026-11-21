import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFiniteFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGalois
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramForm
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase

section
section
set_option autoImplicit false

open GlobalTheory.HTLat

namespace GlobalTheory

theorem exists_pow_prime_root_of_card_torsion {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime]
    {c : ℕ} (hcard : ∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) (k : ℕ) (y : M)
    (hy : y ^ (l ^ k) = 1) : ∃ z : M, z ^ (l ^ (k + 1)) = 1 ∧ z ^ l = y := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let T : ℕ → Subgroup M := fun n => (powMonoidHom (l ^ n)).ker
  have hT : ∀ n, Nat.card (T n) = l ^ (c * n) := fun n => by
    rw [← hcard n]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [T, MonoidHom.mem_ker])
  let φ : T (k + 1) →* M := (powMonoidHom l).comp (T (k + 1)).subtype
  have hker : Nat.card φ.ker = l ^ c := by
    rw [← mul_one c, ← hT 1]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, ?_⟩
        invFun := fun z => ⟨⟨z.1, ?_⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have := y.2
      simp only [T, φ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        powMonoidHom_apply, Subgroup.coe_subtype] at this
      simpa [T, MonoidHom.mem_ker] using this
    · have hz : (z : M) ^ l = 1 := by simpa [T] using MonoidHom.mem_ker.1 z.2
      simp only [T, MonoidHom.mem_ker, powMonoidHom_apply]
      rw [pow_succ' l k, pow_mul, hz, one_pow]
    · have := z.2
      simpa [T, φ, MonoidHom.mem_ker] using this
  have hrange : Nat.card φ.range = l ^ (c * k) := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hker, hT (k + 1), mul_add, mul_one, pow_add, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hl c) h1
  have hfin : Finite (T k) := Nat.finite_of_card_ne_zero (by rw [hT k]; exact (pow_pos hl _).ne')
  have hle : φ.range ≤ T k := by
    rintro _ ⟨z, rfl⟩
    have := z.2
    simp only [T, MonoidHom.mem_ker, powMonoidHom_apply] at this ⊢
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply,
      Subgroup.coe_subtype]
    rw [← pow_mul, ← pow_succ', this]
  have heq : φ.range = T k := Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hT k])
  have hyT : y ∈ T k := by simpa [T, MonoidHom.mem_ker] using hy
  rw [← heq] at hyT
  obtain ⟨z, hz⟩ := hyT
  exact ⟨z.1, MonoidHom.mem_ker.1 z.2, hz⟩

theorem exists_tate_lev_eq_of_card_torsion :
    ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (c : ℕ),
      (∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) →
      ∀ (N : ℕ) (x : M), x ^ (l ^ N) = 1 → ∃ t : Tate l M, t.lev N = x := by
  intro M _ l _ c hcard N x hx
  have h := exists_pow_prime_root_of_card_torsion hcard
  choose r hr1 hr2 using h
  let g : (n : ℕ) → {y : M // y ^ (l ^ (N + n)) = 1} := fun n =>
    Nat.rec ⟨x, hx⟩ (fun n y => ⟨r (N + n) y.1 y.2, hr1 (N + n) y.1 y.2⟩) n
  have hg0 : (g 0).1 = x := rfl
  have hgs : ∀ n, (g (n + 1)).1 ^ l = (g n).1 := fun n => hr2 (N + n) (g n).1 (g n).2
  have hgk : ∀ n k, (g (n + k)).1 ^ (l ^ k) = (g n).1 := fun n k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_mul]
      show ((g (n + k + 1)).1 ^ l) ^ (l ^ k) = _
      rw [hgs, ih]
  let s : ℕ → M := fun n => (g n).1 ^ (l ^ N)
  have hs : ∀ n, s n ^ l ^ n = 1 ∧ s (n + 1) ^ l = s n := fun n => by
    refine ⟨?_, ?_⟩
    · simp only [s]
      rw [← pow_mul, ← pow_add, (g n).2]
    · simp only [s]
      rw [← pow_mul, mul_comm, pow_mul, hgs]
  refine ⟨Tate.mk s hs, ?_⟩
  rw [Tate.lev_mk]
  simp only [s]
  have := hgk 0 N
  rw [zero_add] at this
  rw [this, hg0]

end GlobalTheory
end

open GlobalTheory.HTLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateModule_levelComponent_eq_of_card_torsion : ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (c : ℕ), (∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) → ∀ (N : ℕ) (x : M), x ^ (l ^ N) = 1 → ∃ t : Tate l M, t.lev N = x := by
  atlas_forward_decl GlobalTheory.exists_tate_lev_eq_of_card_torsion
end

section
section
open GlobalTheory.HTLat

namespace GlobalTheory.TateRel

theorem lev_sum {M : Type} [CommGroup M] {l : ℕ} {ι : Type} (s : Finset ι) (f : ι → Tate l M) (N : ℕ) :
    (∑ i ∈ s, f i).lev N = ∏ i ∈ s, (f i).lev N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, Tate.lev_add, ih]

theorem prod_pow_eq_one (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (φ : Fin n → (M →* M)) (c : Fin n → ℤ_[l]) (h : ∑ i, c i • Tate.map l (φ i) = 0) (N : ℕ)
    (m : Fin n → ℤ) (hm : ∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N)))
    (t : Tate l M) : ∏ i, φ i (t.lev N) ^ m i = 1 := by
  have h0 : ((∑ i, c i • Tate.map l (φ i)) t).lev N = 1 := by rw [h]; rfl
  rw [LinearMap.sum_apply, lev_sum] at h0
  rw [← h0]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Tate.lev_smul, Tate.lev_map]
  set y := φ i (t.lev N)
  have hy : y ^ ((l ^ N : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← map_pow, Tate.lev_pow, map_one]
  have hc : ((GlobalTheory.PDiv.digit N (c i) : ℕ) : ZMod (l ^ N)) = ((m i : ℤ) : ZMod (l ^ N)) := by
    rw [GlobalTheory.PDiv.cast_digit, hm i]
  have hc' : (((GlobalTheory.PDiv.digit N (c i) : ℕ) : ℤ) : ZMod (l ^ N)) = ((m i : ℤ) : ZMod (l ^ N)) := by
    rw [Int.cast_natCast]; exact hc
  rw [ZMod.intCast_eq_intCast_iff'] at hc'
  rw [zpow_eq_zpow_emod (m i) hy, ← hc', ← zpow_eq_zpow_emod _ hy, zpow_natCast]

end GlobalTheory.TateRel
end

open GlobalTheory.HTLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_endomorphism_pow_levelComponent_eq_one_of_relation : ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : Fin n → (M →* M)) (c : Fin n → ℤ_[l]), ∑ i, c i • Tate.map l (φ i) = 0 → ∀ (N : ℕ) (m : Fin n → ℤ), (∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N))) → ∀ t : Tate l M, ∏ i, φ i (t.lev N) ^ m i = 1 := by
  atlas_forward_decl GlobalTheory.TateRel.prod_pow_eq_one
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SepClosedDivisible

theorem divisible_algClosure : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ m : ℕ, (m : K) ≠ 0 → ∀ f : A ⟶ A, IsMonHom f → (∀ x : ptOver K Ω ⟶ A, x ^ m = 1 → x ≫ f = 1) → ∃ h : (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).obj A ⟶ (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).obj A, IsMonHom h ∧ (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).map f = h ^ m := by
  intro K Ω _ _ _ _ A _ hA m hm f hf hkill
  set L := AlgebraicClosure Ω
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with ht
  let j : Ω →ₐ[K] L := IsScalarTower.toAlgHom K Ω L
  have hmL : (m : L) ≠ 0 := by
    intro h; apply hm; apply (algebraMap K L).injective; simpa using h
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K A hA
  have hcΩ := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K Ω A hA g hg m hm
  have hcL := GlobalTheory.SepClosedTorsion.card_torsion_eq (Ω := Ω) (Ω' := L) A hA hm
  have hpos : m ^ (2 * g) ≠ 0 := pow_ne_zero _ hm0
  haveI : Finite {x : ptOver K L ⟶ A // x ^ m = 1} := Nat.finite_of_card_ne_zero (by rw [← hcL, hcΩ]; exact hpos)
  let emb : (ptOver K Ω ⟶ A) →* (ptOver K L ⟶ A) := MonoidHom.mk' (fun x => ptOverMap j ≫ x) fun x y => MonObj.comp_mul _ x y
  have hemb : Function.Injective emb := by
    intro x y e
    have := epi_ptOverMap j
    exact Over.OverMorphism.ext ((cancel_epi (ptOverMap j).left).1
      (by simpa using congrArg (fun q => q.left) (show ptOverMap j ≫ x = ptOverMap j ≫ y from e)))
  let emb' : {x : ptOver K Ω ⟶ A // x ^ m = 1} → {x : ptOver K L ⟶ A // x ^ m = 1} :=
    fun x => ⟨emb x.1, by rw [← map_pow, x.2, map_one]⟩
  have hemb' : Function.Injective emb' := fun x y e => Subtype.ext (hemb (congrArg Subtype.val e))
  have hbij := hemb'.bijective_of_nat_card_le hcL.ge
  have step1 : ∀ y : ptOver K L ⟶ A, y ^ m = 1 → y ≫ f = 1 := by
    intro y hy
    obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy⟩
    have hx' : ptOverMap j ≫ x.1 = y := congrArg Subtype.val hx
    rw [← hx', Category.assoc, hkill x.1 x.2, MonObj.comp_one]
  have hgp : IsGrpPullback ((Over.pullback t).obj A) A t (pullback.fst A.hom t) := isGrpPullback_pullback A t
  have hB : IsAbelianScheme ((Over.pullback t).obj A) := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hgp (𝟙 (Sp L)) t (Category.id_comp t).symm
  have hFf : IsMonHom ((Over.pullback t).map f) := inferInstance
  refine (GlobalTheory.TorsionDivisible.finite_torsion_and_divisible L _ hB m hmL).2 _ hFf ?_
  intro x hx
  apply e.injective
  have h1 : e x ^ m = 1 := by rw [← map_pow, hx, map_one]
  have h2 : e x ≫ f = 1 := step1 (e x) h1
  rw [map_one, ← h2]
  apply Over.OverMorphism.ext
  rw [he, Over.comp_left, Over.comp_left, he]
  simp
  rw [pullback.lift_fst]

end GlobalTheory.SepClosedDivisible

end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisible_algClosure_of_kills_torsion_sepClosed : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ m : ℕ, (m : K) ≠ 0 → ∀ f : A ⟶ A, IsMonHom f → (∀ x : ptOver K Ω ⟶ A, x ^ m = 1 → x ≫ f = 1) → ∃ h : (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).obj A ⟶ (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).obj A, IsMonHom h ∧ (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).map f = h ^ m := by
  atlas_forward_decl GlobalTheory.SepClosedDivisible.divisible_algClosure
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvd_coords_of_definite_parallelogram_form : ∀ (E : Type) [AddCommGroup E] (H : AddSubgroup E) (Q : E → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f ∈ H, Q f = 0 → f = 0) → ∀ (n : ℕ) (u : Fin n → E), (∀ i, u i ∈ H) → LinearIndependent ℤ u → ∃ e : ℕ, 0 < e ∧ ∀ (k : ℕ) (m : Fin n → ℤ) (h : E), h ∈ H → k • h = ∑ i, m i • u i → ∀ i, (k : ℤ) ∣ e * m i := by
  first | exact @GlobalTheory.exists_dvd_coords_of_definite_form | exact GlobalTheory.exists_dvd_coords_of_definite_form | (intros; apply GlobalTheory.exists_dvd_coords_of_definite_form <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SS.AbAmple

open GlobalTheory.CechPic GlobalTheory.TripleExt

theorem cubeCls_eq_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (c : Pic A.left) : cubeCls (x3 A) c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have h := GlobalTheory.CubeTop.cubeTheorem S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have h₀ := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 h
  rw [cls_linComb hL, Fin.sum_univ_eight] at h₀
  have e : x3 A = ![x3 A 0, x3 A 1, x3 A 2] := by
    funext i; fin_cases i <;> rfl
  rw [e, GlobalTheory.SS.AmpCub.cubeCls_three]
  rw [← h₀]
  simp
  abel

end GlobalTheory.SS.AbAmple

namespace GlobalTheory.SS

open GlobalTheory.CechPic AbAmple

theorem exists_ampleCub_of_isAbelianScheme :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B →
      ∃ L : LB B.left, GlobalTheory.SS.AmpleCub B L := by
  intro k _ _ B _ hB
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom := geometricallyIntegral_of_smooth _
  have : IsIntegral B.left :=
    GeometricallyIntegral.geometrically_isIntegral (f := B.hom) (𝟙 _) _ _ (IsPullback.id_horiz B.hom)
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  have hst : ∀ x : B.left, UniqueFactorizationMonoid (B.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth k B.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  obtain ⟨y⟩ : Nonempty B.left := inferInstance
  obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  obtain ⟨L, s, hL, hs⟩ := exists_nonzeroLocus_eq_of_isAffineOpen B.left hst W hW ⟨y, hy⟩
  exact AmpCub.exists_ampleCub (cubeCls_eq_zero B hB (cls L hL)) ⟨L, hL, s, rfl, hs⟩ hW ⟨y, hy⟩

end GlobalTheory.SS
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_ample_cubical_lineBundle_abelianVariety : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∃ L : LB B.left, GlobalTheory.SS.AmpleCub B L := by
  atlas_forward_decl GlobalTheory.SS.exists_ampleCub_of_isAbelianScheme
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ActTrivialInj

theorem exists_nat_eq_mul {F : Type} [Field F] [NumberField F] {O : Type} [CommRing O] [Algebra O F]
    [IsFractionRing O F] {x : O} (hx : x ≠ 0) : ∃ n : ℕ, n ≠ 0 ∧ ∃ r : O, (n : O) = x * r := by
  set y := algebraMap O F x with hydef
  have hy : y ≠ 0 := by
    intro h
    apply hx
    apply IsFractionRing.injective O F
    rw [map_zero]
    exact h
  have hint : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  have hp0 : (minpoly ℚ y).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hy
  set q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ y) with hqdef
  have hq : Polynomial.aeval y q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) (minpoly ℚ y) (minpoly.aeval ℚ y)
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) (minpoly ℚ y)
  set c := q.coeff 0 with hcdef
  have hc : c ≠ 0 := by
    intro h
    have h' := congrArg (fun P => P.coeff 0) hb
    simp only [Polynomial.coeff_map, Polynomial.coeff_smul] at h'
    rw [← hcdef, h, map_zero, eq_comm, smul_eq_zero] at h'
    rcases h' with h' | h'
    · exact nonZeroDivisors.ne_zero b.2 h'
    · exact hp0 h'
  have hO : Polynomial.aeval x q = 0 := by
    apply IsFractionRing.injective O F
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact hq
  have key := congrArg (Polynomial.aeval x) (Polynomial.X_mul_divX_add q)
  rw [hO, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, ← hcdef, algebraMap_int_eq, eq_intCast] at key
  have hc' : (c : O) = x * -(Polynomial.aeval x q.divX) := by linear_combination key
  refine ⟨c.natAbs, Int.natAbs_ne_zero.2 hc, ?_⟩
  have hn : ((c.natAbs : ℕ) : O) = ((|c| : ℤ) : O) := by rw [← Int.natCast_natAbs, Int.cast_natCast]
  rcases abs_choice c with h | h
  · exact ⟨-(Polynomial.aeval x q.divX), by rw [hn, h, hc']⟩
  · exact ⟨Polynomial.aeval x q.divX, by rw [hn, h, Int.cast_neg, hc']; ring⟩

theorem eq_zero_of_act_pullback_eq_one : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (x : O), (OAct.pullback (spMap (algebraMap K (AlgebraicClosure Ω))) A α).act x = 1 → x = 0 := by
  rintro K Ω _ _ _ _ A _ _ hA ⟨d, hd, hsm⟩ l _ hl F _ _ O _ _ _ α x hx
  by_contra hx0
  have hl' : l.Prime := Fact.out
  set L := AlgebraicClosure Ω
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with htdef
  have hgp := isGrpPullback_pullback A t
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hgp (𝟙 (Sp L)) t (Category.id_comp t).symm
  have h1 : ∀ y : ptOver K L ⟶ A, y ≫ α.act x = 1 := by
    intro y
    obtain ⟨v, rfl⟩ := e.surjective y
    have hv : e (v ≫ (OAct.pullback t A α).act x) = e v ≫ α.act x := by
      apply Over.OverMorphism.ext
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc]
      congr 1
      exact pullback.lift_fst _ _ _
    rw [← hv, hx, comp_one, map_one]
  obtain ⟨n, hn0, r, hr⟩ := exists_nat_eq_mul (F := F) hx0
  have h0 : α.act 0 = 1 := by
    have h00 := α.add 0 0
    rw [add_zero] at h00
    exact mul_left_cancel (h00.symm.trans (_root_.mul_one _).symm)
  have hnat : ∀ m : ℕ, ∀ y : ptOver K L ⟶ A, y ≫ α.act (m : O) = y ^ m := by
    intro m y
    induction m with
    | zero => rw [Nat.cast_zero, h0, comp_one, pow_zero]
    | succ m ih => rw [Nat.cast_succ, α.add, comp_mul, ih, α.one, Category.comp_id, pow_succ]
  have hall : ∀ y : ptOver K L ⟶ A, y ^ n = 1 := by
    intro y
    haveI := α.hom r
    rw [← hnat, hr, α.mul, ← Category.assoc, h1, one_comp]
  obtain ⟨v, m, hlm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 l hl'.ne_one
  have hsub : ∀ y : ptOver K L ⟶ A, y ^ (l ^ (v + 1)) = 1 → y ^ (l ^ v) = 1 := by
    intro y hy
    have e1 : (y ^ l ^ v) ^ l = 1 := by rw [← pow_mul, ← pow_succ]; exact hy
    have e2 : (y ^ l ^ v) ^ m = 1 := by rw [← pow_mul, ← hnm]; exact hall y
    have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl').2 hlm
    have e3 := pow_gcd_eq_one.2 ⟨e1, e2⟩
    rwa [hcop.gcd_eq_one, pow_one] at e3
  have hlK : ∀ k : ℕ, ((l ^ k : ℕ) : K) ≠ 0 := fun k => by rw [Nat.cast_pow]; exact pow_ne_zero _ hl
  have cN := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K L A hA d hsm (l ^ (v + 1)) (hlK _)
  have cv := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K L A hA d hsm (l ^ v) (hlK _)
  have hfin : Finite {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [cv]; exact pow_ne_zero _ (pow_ne_zero _ hl'.ne_zero))
  have hle := Nat.card_le_card_of_injective
    (fun y : {y : ptOver K L ⟶ A // y ^ (l ^ (v + 1)) = 1} =>
      (⟨y.1, hsub y.1 y.2⟩ : {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1}))
    (fun a b h => Subtype.ext (congrArg (fun z : {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1} => z.1) h))
  rw [cN, cv] at hle
  have hlt : (l ^ v) ^ (2 * d) < (l ^ (v + 1)) ^ (2 * d) :=
    Nat.pow_lt_pow_left (Nat.pow_lt_pow_right hl'.one_lt (Nat.lt_succ_self v)) (by omega)
  omega

end GlobalTheory.ActTrivialInj

end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_acts_trivially_abelianVariety_algClosure : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (x : O), (OAct.pullback (spMap (algebraMap K (AlgebraicClosure Ω))) A α).act x = 1 → x = 0 := by
  atlas_forward_decl GlobalTheory.ActTrivialInj.eq_zero_of_act_pullback_eq_one
end

section
namespace GlobalTheory

theorem padicInt_toZModPow_not_dvd_mul :
    ∀ (l : ℕ) [Fact l.Prime] (c : ℤ_[l]), c ≠ 0 → ∀ e : ℕ, 0 < e →
      ∃ N : ℕ, ∀ m : ℤ, PadicInt.toZModPow N c = (m : ZMod (l ^ N)) →
        ¬ ((l : ℤ) ^ N ∣ e * m) := by
  intro l _ c hc e he
  have hl : l.Prime := Fact.out
  refine ⟨c.valuation + e.factorization l + 1, ?_⟩
  intro m hm hdvd
  set v := c.valuation with hv
  set a := e.factorization l with ha
  have hm1 : (l : ℤ) ^ (v + 1) ∣ m := by
    have he' : (e : ℤ) = (l : ℤ) ^ a * ((e / l ^ a : ℕ) : ℤ) := by
      exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self e l).symm
    have hcop : IsCoprime ((l : ℤ) ^ (v + 1)) ((e / l ^ a : ℕ) : ℤ) := by
      have h := (Nat.coprime_ordCompl hl he.ne').pow_left (v + 1)
      have := Nat.isCoprime_iff_coprime.mpr h
      simpa [Nat.cast_pow] using this
    rw [he', show v + a + 1 = a + (v + 1) by ring, pow_add, mul_assoc] at hdvd
    have h2 := (mul_dvd_mul_iff_left (pow_ne_zero a (by exact_mod_cast hl.ne_zero : (l : ℤ) ≠ 0))).mp hdvd
    exact hcop.dvd_of_dvd_mul_left h2
  have h0 : PadicInt.toZModPow (v + 1) c = 0 := by
    rw [← PadicInt.cast_toZModPow (v + 1) (v + a + 1) (by omega) c, hm,
      ZMod.cast_intCast (pow_dvd_pow l (by omega))]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hm1
  have hmem : c ∈ (Ideal.span {(l : ℤ_[l]) ^ (v + 1)} : Ideal ℤ_[l]) := by
    rw [← PadicInt.ker_toZModPow]
    exact h0
  have := (PadicInt.mem_span_pow_iff_le_valuation c hc (v + 1)).mp hmem
  omega

end GlobalTheory

alias _root_.GlobalTheory.T.padicInt_exists_level_not_dvd_mul_lift := _root_.GlobalTheory.padicInt_toZModPow_not_dvd_mul
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CMFaithful

theorem linearIndependent_actTate : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => actTate α.toRingAct l (ptOver K Ω) (a i)) := by
  intro K Ω _ _ _ _ A _ _ hA hd F _ _ O _ _ _ α l _ hl n a ha
  obtain ⟨d, hd0, hdim⟩ := hd
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  let t := spMap (algebraMap K (AlgebraicClosure Ω))
  let B := (Over.pullback t).obj A
  let β := OAct.pullback t A α
  have hB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  haveI : IsCommMonObj B := hB.comm
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_symmetric_ample_cubical_lineBundle_abelianVariety (AlgebraicClosure Ω) B hB
  obtain ⟨Q, hQ1, hQ2, hQ3, -⟩ := GlobalTheory.SS.exists_quadraticForm_end (AlgebraicClosure Ω) B hB L hL
  let ψ : O →+ Additive (B ⟶ B) := AddMonoidHom.mk' (fun x => Additive.ofMul (β.act x))
    (fun x y => by rw [β.add]; rfl)
  let H : AddSubgroup (Additive (B ⟶ B)) :=
    { carrier := {f | IsMonHom (Additive.toMul f)}
      add_mem' := fun {f g} hf hg => by
        change IsMonHom (Additive.toMul f * Additive.toMul g)
        haveI : IsMonHom (Additive.toMul f) := hf
        haveI : IsMonHom (Additive.toMul g) := hg
        rw [Hom.mul_def]; infer_instance
      zero_mem' := by
        change IsMonHom (1 : B ⟶ B)
        rw [Hom.one_def]; infer_instance
      neg_mem' := fun {f} hf => by
        change IsMonHom (Additive.toMul f)⁻¹
        haveI : IsMonHom (Additive.toMul f) := hf
        infer_instance }
  have hu : ∀ i, ψ (a i) ∈ H := fun i => β.hom (a i)
  have hinj : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun x hx =>
    GlobalTheory.T.eq_zero_of_acts_trivially_abelianVariety_algClosure K Ω A hA ⟨d, hd0, hdim⟩ l hl F O α x (by
      have : Additive.toMul (ψ x) = Additive.toMul 0 := congrArg _ hx
      exact this)
  have hindep : LinearIndependent ℤ (fun i => ψ (a i)) := by
    have h1 : LinearIndependent ℤ (fun i => algebraMap O F (a i)) := ha.restrict_scalars' ℤ
    have h2 : LinearIndependent ℤ a := by
      refine LinearIndependent.of_comp (algebraMap O F).toAddMonoidHom.toIntLinearMap ?_
      exact h1
    exact h2.map' ψ.toIntLinearMap (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨e, he, hE⟩ := GlobalTheory.T.exists_dvd_coords_of_definite_parallelogram_form (Additive (B ⟶ B)) H (fun f => Q (Additive.toMul f))
    (fun f g => by
      have := hQ1 (Additive.toMul f) (Additive.toMul g)
      simpa [div_eq_mul_inv] using this)
    (fun f => hQ2 _) (fun f hf h0 => by
      have := hQ3 (Additive.toMul f) hf h0
      exact this) n (fun i => ψ (a i)) hu hindep
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨j, hj⟩ := hne
  obtain ⟨N, hN⟩ := GlobalTheory.T.padicInt_exists_level_not_dvd_mul_lift l (c j) hj e he
  haveI : NeZero (l ^ N) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let m : Fin n → ℤ := fun i => ((PadicInt.toZModPow N (c i)).val : ℤ)
  have hm : ∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N)) := fun i => by
    simp [m]
  let φ : Fin n → ((ptOver K Ω ⟶ A) →* (ptOver K Ω ⟶ A)) := fun i => actPts α.toRingAct (ptOver K Ω) (a i)
  have kill := GlobalTheory.T.prod_endomorphism_pow_levelComponent_eq_one_of_relation (ptOver K Ω ⟶ A) l n φ c hc N m hm
  let x : O := ∑ i, m i • a i
  have hcomp : ∀ y : ptOver K Ω ⟶ A, y ≫ α.act x = ∏ i, (y ≫ α.act (a i)) ^ m i := by
    intro y
    let χ : O →+ Additive (ptOver K Ω ⟶ A) := AddMonoidHom.mk' (fun z => Additive.ofMul (y ≫ α.act z))
      (fun z w => by rw [α.add, MonObj.comp_mul]; rfl)
    have e1 : χ x = ∑ i, m i • χ (a i) := by simp only [x, map_sum, map_zsmul]
    have e2 := congrArg Additive.toMul e1
    rw [toMul_sum] at e2
    simp only [toMul_zsmul] at e2
    exact e2
  have hcard : ∀ k : ℕ, Nat.card {y : ptOver K Ω ⟶ A // y ^ (l ^ k) = 1} = l ^ (2 * d * k) := fun k => by
    rw [GlobalTheory.T.card_abelianVariety_torsion_sepClosed K Ω A hA d hdim (l ^ k) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm k]
  have hx : ∀ y : ptOver K Ω ⟶ A, y ^ (l ^ N) = 1 → y ≫ α.act x = 1 := by
    intro y hy
    obtain ⟨tt, rfl⟩ := GlobalTheory.T.exists_tateModule_levelComponent_eq_of_card_torsion (ptOver K Ω ⟶ A) l (2 * d) hcard N y hy
    rw [hcomp, ← kill tt]
    rfl
  obtain ⟨h, hh, hfh⟩ := GlobalTheory.T.divisible_algClosure_of_kills_torsion_sepClosed K Ω A hA (l ^ N) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl) (α.act x) (α.hom x) hx
  have hsum : (l ^ N) • Additive.ofMul h = ∑ i, m i • ψ (a i) := by
    rw [← ofMul_pow, ← hfh]
    change ψ x = _
    simp only [x, map_sum, map_zsmul]
  have := hE (l ^ N) m (Additive.ofMul h) hh hsum j
  exact hN (m j) (hm j) (by exact_mod_cast this)

end GlobalTheory.CMFaithful
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_numberFieldEndomorphisms_tateModule : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => actTate α.toRingAct l (ptOver K Ω) (a i)) := by
  atlas_forward_decl GlobalTheory.CMFaithful.linearIndependent_actTate
end

section
open scoped Matrix
open Polynomial

namespace GlobalTheory.CyclicVector

theorem exists_linearIndependent_iterates_of_linearIndependent_pow {K : Type} [Field K] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) K)
    (hg : LinearIndependent K (fun i : Fin r => g ^ (i : ℕ))) :
    ∃ v : Fin r → K, LinearIndependent K (fun i : Fin r => (g ^ (i : ℕ)) *ᵥ v) := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval' (Matrix.toLin' g))
  set v := (Module.AEval'.of (Matrix.toLin' g)).symm x with hv
  refine ⟨v, ?_⟩
  rw [Fintype.linearIndependent_iff] at hg ⊢
  intro c hc
  let q : K[X] := ∑ j : Fin r, monomial (j : ℕ) (c j)
  have haq : aeval g q = ∑ j : Fin r, c j • g ^ (j : ℕ) := by
    simp [q, map_sum, aeval_monomial, Algebra.smul_def]
  have ha : ∀ p : K[X], aeval (Matrix.toLin' g) p = Matrix.toLin' (aeval g p) := fun p =>
    (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin r)) g p)
  have hqv : aeval g q *ᵥ v = 0 := by
    rw [haq, Matrix.sum_mulVec]
    have hs : ∀ j : Fin r, (c j • g ^ (j : ℕ)) *ᵥ v = c j • (g ^ (j : ℕ) *ᵥ v) := fun j => by
      ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    simpa [hs] using hc
  have hmem : q ∈ Module.annihilator K[X] (Module.AEval' (Matrix.toLin' g)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    apply (Module.AEval'.of (Matrix.toLin' g)).symm.injective
    rw [Module.AEval.of_symm_smul, map_zero, ha]
    exact hqv
  have hq : aeval g q = 0 := by
    apply Matrix.toLin'.injective
    rw [map_zero, ← ha]
    refine LinearMap.ext fun u => ?_
    have := Module.mem_annihilator.1 hmem (Module.AEval'.of (Matrix.toLin' g) u)
    have h2 := congrArg (Module.AEval'.of (Matrix.toLin' g)).symm this
    rw [Module.AEval.of_symm_smul, map_zero] at h2
    simpa using h2
  exact hg c (haq ▸ hq)

end GlobalTheory.CyclicVector
end

section
open scoped Matrix
open IntermediateField

namespace GlobalTheory

theorem exists_pow_linearIndependent_of_isFractionRing (O F : Type) [CommRing O] [Field F]
    [NumberField F] [Algebra O F] [IsFractionRing O F] :
    ∃ α : O, LinearIndependent ℚ (fun i : Fin (Module.finrank ℚ F) => algebraMap O F (α ^ (i : ℕ))) := by
  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element ℚ F
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := O) γ
  have hfin : Finite (IntermediateField ℚ F) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ F ⟨γ, hγ⟩
  obtain ⟨t, t', htt, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun t : ℕ => ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯)
  have h1 : algebraMap O F x + (t : F) * algebraMap O F y ∈
      ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ := mem_adjoin_simple_self _ _
  have h2 : algebraMap O F x + (t' : F) * algebraMap O F y ∈
      ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ := by
    rw [he]; exact mem_adjoin_simple_self _ _
  set L := ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ with hL
  have hyL : algebraMap O F y ∈ L := by
    have hd : ((t : F) - t') * algebraMap O F y ∈ L := by
      have := L.sub_mem h1 h2
      convert this using 1; ring
    have htt' : ((t : F) - t') ≠ 0 := sub_ne_zero.2 (by exact_mod_cast htt)
    have hc : ((t : F) - t') ∈ L := L.sub_mem (L.natCast_mem t) (L.natCast_mem t')
    have := L.mul_mem (L.inv_mem hc) hd
    rwa [← mul_assoc, inv_mul_cancel₀ htt', one_mul] at this
  have hxL : algebraMap O F x ∈ L := by
    have := L.sub_mem h1 (L.mul_mem (L.natCast_mem t) hyL)
    simpa using this
  have hγL : γ ∈ L := hxy ▸ L.div_mem hxL hyL
  have htop : L = ⊤ := by
    rw [eq_top_iff, ← hγ, adjoin_simple_le_iff]; exact hγL
  refine ⟨x + t • y, ?_⟩
  have ha : algebraMap O F (x + t • y) = algebraMap O F x + (t : F) * algebraMap O F y := by
    rw [map_add, map_nsmul, nsmul_eq_mul]
  have hint : IsIntegral ℚ (algebraMap O F (x + t • y)) := Algebra.IsIntegral.isIntegral _
  have hdeg : (minpoly ℚ (algebraMap O F (x + t • y))).natDegree = Module.finrank ℚ F := by
    rw [← adjoin.finrank hint, ha, ← hL, htop, finrank_top']
  have h' := (linearIndependent_pow (K := ℚ) (algebraMap O F (x + t • y))).comp
    (Fin.cast hdeg.symm) (Fin.cast_injective _)
  have hf : (fun i : Fin (Module.finrank ℚ F) => algebraMap O F ((x + t • y) ^ (i : ℕ))) =
      (fun i : Fin (minpoly ℚ (algebraMap O F (x + t • y))).natDegree =>
        algebraMap O F (x + t • y) ^ (i : ℕ)) ∘ Fin.cast hdeg.symm := by
    ext i; simp [map_pow]
  rw [hf]; exact h'

end GlobalTheory
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Matrix

namespace GlobalTheory.CyclicLattice

theorem exists_linearIndependent_mulVec_pow {R : Type} [CommRing R] [IsDomain R] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) R) (hg : LinearIndependent R (fun i : Fin r => g ^ (i : ℕ))) :
    ∃ v : Fin r → R, LinearIndependent R (fun i : Fin r => (g ^ (i : ℕ)) *ᵥ v) := by
  classical
  let K := FractionRing R
  let f := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  let gK := g.map f
  let Φ : Matrix (Fin r) (Fin r) R →ₗ[R] Matrix (Fin r) (Fin r) K :=
    (Algebra.linearMap R K).mapMatrix
  have hΦ : Function.Injective Φ := fun a a' h => by
    ext i j
    exact hf (congrFun (congrFun h i) j)
  have hgK : LinearIndependent K (fun i : Fin r => gK ^ (i : ℕ)) := by
    have h1 := hg.map' Φ (LinearMap.ker_eq_bot.2 hΦ)
    have h2 : (Φ ∘ fun i : Fin r => g ^ (i : ℕ)) = fun i : Fin r => gK ^ (i : ℕ) := by
      funext i
      simp only [Function.comp_apply, gK, ← Matrix.map_pow]
      rfl
    rw [h2] at h1
    exact (LinearIndependent.iff_fractionRing R K).mp h1
  obtain ⟨w, hw⟩ :=
    GlobalTheory.CyclicVector.exists_linearIndependent_iterates_of_linearIndependent_pow gK hgK
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) w
  choose u hu using hs
  refine ⟨u, ?_⟩
  let Ψ : (Fin r → R) →ₗ[R] (Fin r → K) :=
    LinearMap.pi (fun i => (Algebra.linearMap R K).comp (LinearMap.proj i))
  have hΨ : Function.Injective Ψ := fun a a' h => funext fun i => hf (congrFun h i)
  have hfu : (f ∘ u) = (f s) • w := funext fun j => by
    simpa [Algebra.smul_def] using hu j
  have key : (Ψ ∘ fun i : Fin r => g ^ (i : ℕ) *ᵥ u) =
      fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w) := by
    funext i
    ext k
    have e1 := RingHom.map_mulVec f (g ^ (i : ℕ)) u k
    simp only [Function.comp_apply]
    change f ((g ^ (i : ℕ) *ᵥ u) k) = _
    rw [e1, Matrix.map_pow, hfu, Matrix.mulVec_smul]
  have hsK : f s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have h3 : LinearIndependent K (fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w)) := by
    have := hw.units_smul (fun _ => Units.mk0 (f s) hsK)
    have e : (fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w)) =
        (fun _ : Fin r => Units.mk0 (f s) hsK) • (fun i : Fin r => gK ^ (i : ℕ) *ᵥ w) := by
      funext i
      simp [Units.smul_def]
    rw [e]
    exact this
  have h4 := (LinearIndependent.iff_fractionRing R K).mpr h3
  rw [← key] at h4
  exact h4.of_comp

theorem exists_smul_mem_span_of_linearIndependent {R M : Type} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] {r : ℕ} (b : Module.Basis (Fin r) R M) (w : Fin r → M)
    (hw : LinearIndependent R w) :
    ∃ c : R, c ≠ 0 ∧ ∀ t : M, c • t ∈ Submodule.span R (Set.range w) := by
  classical
  let N : Matrix (Fin r) (Fin r) R := b.toMatrix w
  have hsum : ∀ z : Fin r → R, b.equivFun (∑ j, z j • w j) = N *ᵥ z := by
    intro z
    ext i
    simp [N, Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct, mul_comm]
  have hdet : N.det ≠ 0 := by
    intro h0
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hz0
    have : ∑ j, z j • w j = 0 := b.equivFun.injective (by rw [hsum, hz, map_zero])
    funext j
    exact Fintype.linearIndependent_iff.1 hw z this j
  refine ⟨N.det, hdet, fun t => ?_⟩
  have : N.det • t = ∑ j, (N.adjugate *ᵥ b.equivFun t) j • w j := by
    apply b.equivFun.injective
    rw [hsum, map_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_smul_mem_span_orbit : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (O F : Type) [CommRing O] [Field F] [NumberField F] [Algebra O F] [IsFractionRing O F] (ρ : O →+* Module.End ℤ_[l] T), Module.finrank ℤ_[l] T = Module.finrank ℚ F → (∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => ρ (a i))) → ∃ (v : T) (c : ℤ_[l]), c ≠ 0 ∧ ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v) := by
  intro l _ T _ _ _ _ O F _ _ _ _ _ ρ hrank hind
  obtain ⟨α, hα⟩ := GlobalTheory.exists_pow_linearIndependent_of_isFractionRing O F
  set n := Module.finrank ℚ F with hn
  let b : Module.Basis (Fin n) ℤ_[l] T := Module.finBasisOfFinrankEq ℤ_[l] T hrank
  set φ := ρ α with hφdef
  set g := LinearMap.toMatrix b b φ with hgdef
  have hpow : ∀ i : ℕ, LinearMap.toMatrix b b (φ ^ i) = g ^ i := fun i => by
    induction i with
    | zero => simp [LinearMap.toMatrix_one]
    | succ k ih => rw [pow_succ, LinearMap.toMatrix_mul, ih, pow_succ]
  have hφ : LinearIndependent ℤ_[l] (fun i : Fin n => φ ^ (i : ℕ)) := by
    have := hind n (fun i => α ^ (i : ℕ)) hα
    simpa [φ, map_pow] using this
  have hg : LinearIndependent ℤ_[l] (fun i : Fin n => g ^ (i : ℕ)) := by
    have := hφ.map' (LinearMap.toMatrix b b).toLinearMap (LinearMap.toMatrix b b).ker
    simpa [Function.comp_def, hpow] using this
  obtain ⟨u, hu⟩ := exists_linearIndependent_mulVec_pow g hg
  set v : T := b.equivFun.symm u with hv
  have hw : ∀ i : ℕ, b.equivFun ((φ ^ i) v) = g ^ i *ᵥ u := by
    intro i
    have hu' : u = ⇑(b.repr v) := by
      rw [hv, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [← hpow, hu', LinearMap.toMatrix_mulVec_repr, Module.Basis.equivFun_apply]
  have hli : LinearIndependent ℤ_[l] (fun i : Fin n => (φ ^ (i : ℕ)) v) := by
    have hfun : (fun i : Fin n => (φ ^ (i : ℕ)) v) =
        b.equivFun.symm.toLinearMap ∘ (fun i : Fin n => g ^ (i : ℕ) *ᵥ u) := by
      funext i
      apply b.equivFun.injective
      simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hw]
    rw [hfun]
    exact hu.map' _ b.equivFun.symm.ker
  obtain ⟨c, hc, hct⟩ := exists_smul_mem_span_of_linearIndependent b _ hli
  refine ⟨v, c, hc, fun t => Submodule.span_mono ?_ (hct t)⟩
  rintro _ ⟨i, rfl⟩
  exact ⟨α ^ (i : ℕ), by simp [φ, map_pow]⟩

end GlobalTheory.CyclicLattice
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_mem_span_orbit_of_numberField_lattice : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (O F : Type) [CommRing O] [Field F] [NumberField F] [Algebra O F] [IsFractionRing O F] (ρ : O →+* Module.End ℤ_[l] T), Module.finrank ℤ_[l] T = Module.finrank ℚ F → (∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => ρ (a i))) → ∃ (v : T) (c : ℤ_[l]), c ≠ 0 ∧ ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v) := by
  atlas_forward_decl GlobalTheory.CyclicLattice.exists_smul_mem_span_orbit
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMComm

theorem commute_of_cyclic {l : ℕ} [Fact l.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    [Module.IsTorsionFree ℤ_[l] T] {O : Type} [CommRing O] (ρ : O →+* Module.End ℤ_[l] T) (v : T) (c : ℤ_[l])
    (hc : c ≠ 0) (hv : ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v))
    (g h : Module.End ℤ_[l] T) (hg : ∀ a, g * ρ a = ρ a * g) (hh : ∀ a, h * ρ a = ρ a * h) :
    g * h = h * g := by
  set P := Submodule.span ℤ_[l] (Set.range ρ) with hP
  have hcen : ∀ k : Module.End ℤ_[l] T, (∀ a, k * ρ a = ρ a * k) → ∀ x ∈ P, k * x = x * k := by
    intro k hk x hx
    have : P ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℤ_[l] {k}) := by
      rw [hP, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact hk a
    have h1 := this hx
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at h1
    exact h1 k rfl
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hx' : ∀ a, x * ρ a = ρ a * x := fun a => by
      have := hcen (ρ a) (fun b => by rw [← map_mul, ← map_mul, mul_comm]) x hx
      exact this.symm
    exact hcen x hx' y hy
  have hev : ∀ w : T, ∃ x ∈ P, x v = c • w := by
    intro w
    have := hv w
    rw [show (Set.range fun a => ρ a v) = (LinearMap.applyₗ v : Module.End ℤ_[l] T →ₗ[ℤ_[l]] T) '' Set.range ρ by
      rw [← Set.range_comp]; rfl, Submodule.span_image] at this
    obtain ⟨x, hx, e⟩ := this
    exact ⟨x, hx, e⟩
  refine LinearMap.ext fun t => ?_
  obtain ⟨x, hx, ex⟩ := hev t
  obtain ⟨y, hy, ey⟩ := hev (g v)
  obtain ⟨z, hz, ez⟩ := hev (h v)
  have hgx := hcen g hg x hx
  have hhx := hcen h hh x hx
  have k1 : c • c • c • (g * h) t = x (z (y v)) := by
    have e1 : c • (g * h) t = x (g (h v)) := by
      rw [← map_smul, ← ex, Module.End.mul_apply]
      change (g * (h * x)) v = x (g (h v))
      rw [hhx, ← _root_.mul_assoc, hgx, _root_.mul_assoc]; rfl
    have e2 : c • x (g (h v)) = x (z (g v)) := by
      rw [← map_smul, ← map_smul, ← ez]
      change x ((g * z) v) = x ((z * g) v)
      rw [hcen g hg z hz]
    rw [e1, e2, ← map_smul, ← map_smul, ← ey]
  have k2 : c • c • c • (h * g) t = x (y (z v)) := by
    have e1 : c • (h * g) t = x (h (g v)) := by
      rw [← map_smul, ← ex, Module.End.mul_apply]
      change (h * (g * x)) v = x (h (g v))
      rw [hgx, ← _root_.mul_assoc, hhx, _root_.mul_assoc]; rfl
    have e2 : c • x (h (g v)) = x (y (h v)) := by
      rw [← map_smul, ← map_smul, ← ey]
      change x ((h * y) v) = x ((y * h) v)
      rw [hcen h hh y hy]
    rw [e1, e2, ← map_smul, ← map_smul, ← ez]
  have k3 : x (z (y v)) = x (y (z v)) := by
    change (x * (z * y)) v = (x * (y * z)) v
    rw [hcomm z hz y hy]
  have k4 : (c * c * c) • (g * h) t = (c * c * c) • (h * g) t := by
    rw [mul_smul, mul_smul, k1, k3, ← k2, mul_smul, mul_smul]
  exact smul_right_injective T (mul_ne_zero (mul_ne_zero hc hc) hc) k4

theorem galTate_comm_actTate {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] {O : Type} [CommRing O] (α : OAct O A) (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[K] Ω) (a : O) :
    galTate A l σ * actTate α.toRingAct l (ptOver K Ω) a = actTate α.toRingAct l (ptOver K Ω) a * galTate A l σ :=
  LinearMap.ext fun t => Tate.ext fun n => by
    change specAut σ ≫ (t.lev n ≫ α.act a) = (specAut σ ≫ t.lev n) ≫ α.act a
    rw [Category.assoc]

theorem galTate_commute_of_hasCMBy : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F], HasCMBy A F → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ := by
  intro K Ω _ _ _ _ A _ _ hA F _ _ hF l _ hl σ τ
  obtain ⟨⟨d, hd, hdeg⟩, O, _, _, _, ⟨α⟩⟩ := hF
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hcard : ∀ n : ℕ, Nat.card {x : ptOver K Ω ⟶ A // x ^ (l ^ n) = 1} = l ^ (2 * d * n) := fun n => by
    rw [GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K Ω A hA d hd (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm n]
  obtain ⟨hfree, hfin, hrank⟩ := GlobalTheory.TateFree.free_finite_finrank (ptOver K Ω ⟶ A) l (2 * d) hcard
  haveI := hfree
  haveI := hfin
  obtain ⟨v, c, hc, hv⟩ := GlobalTheory.T.exists_smul_mem_span_orbit_of_numberField_lattice l (Tate l (ptOver K Ω ⟶ A)) O F (actTate α.toRingAct l (ptOver K Ω))
    (hrank.trans hdeg.symm) (GlobalTheory.T.linearIndependent_numberFieldEndomorphisms_tateModule K Ω A hA
      ⟨d, by have := Module.finrank_pos (R := ℚ) (M := F); omega, hd⟩ F O α l hl)
  exact commute_of_cyclic _ v c hc hv _ _ (galTate_comm_actTate A α l σ) (galTate_comm_actTate A α l τ)

end GlobalTheory.CMComm
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModule_galoisImages_commute_of_complexMultiplication : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F], HasCMBy A F → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ := by
  atlas_forward_decl GlobalTheory.CMComm.galTate_commute_of_hasCMBy
end
