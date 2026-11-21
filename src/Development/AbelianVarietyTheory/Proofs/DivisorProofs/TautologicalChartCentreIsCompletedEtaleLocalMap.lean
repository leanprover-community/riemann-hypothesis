import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartGaloisRigidStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensOfDataFrom
import Development.AbelianVarietyTheory.Definitions.Divisors.PerFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMaximalLePrimeAddDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedComplementDimBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimQuotientLeOfMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingOfRegularQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCompletionOfQuasiFiniteGaloisRigid

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QFChart

section Alg

variable {O V K : Type} [CommRing O] [CommRing V] [Field K]

theorem mem_of_isIntegralElem {k₀ : Subfield K} (hk : IsAlgClosed k₀) (θ : O →+* K) (hθ : ∀ a, θ a ∈ k₀) {z : K}
    (hz : θ.IsIntegralElem z) : z ∈ k₀ := by
  have h₁ : IsIntegral k₀ z := by
    obtain ⟨P, hP, hPz⟩ := hz
    refine ⟨P.map (θ.codRestrict k₀ hθ), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hPz
  obtain ⟨w, hw⟩ := minpoly.mem_range_of_degree_eq_one k₀ z
    (IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible h₁))
  exact hw ▸ w.2

theorem exists_algClosure [IsLocalRing O] [IsAlgClosed K] (θ : O →+* K) (hθ : ∀ a ∈ maximalIdeal O, θ a = 0) :
    ∃ k₀ : Subfield K, IsAlgClosed k₀ ∧ (∀ a, θ a ∈ k₀) ∧
      ∀ z ∈ k₀, θ.IsIntegralElem z ∧ ∀ A : Subring K, (∀ a, θ a ∈ A) → z ∈ A → z⁻¹ ∈ A := by
  let : Algebra (ResidueField O) K := (Ideal.Quotient.lift (maximalIdeal O) θ hθ).toAlgebra
  have e : ∀ a, algebraMap (ResidueField O) K (residue O a) = θ a := fun _ => rfl
  refine ⟨(algebraicClosure (ResidueField O) K).toSubfield, (algebraicClosure.isAlgClosure (ResidueField O) K).isAlgClosed,
    fun a => e a ▸ (algebraicClosure (ResidueField O) K).algebraMap_mem _, fun z hz => ⟨?_, fun A hA hzA => ?_⟩⟩
  · have h : IsIntegral (ResidueField O) z := (mem_algebraicClosure_iff'.1 hz)
    obtain ⟨P, hP, hPz⟩ := h
    obtain ⟨P₀, h₀, -, h₂⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective (residue_surjective (R := O)) P) hP
    refine ⟨P₀, h₂, ?_⟩
    rw [← h₀, Polynomial.eval₂_map] at hPz
    exact hPz
  · let B : Subalgebra (ResidueField O) K :=
      { A with algebraMap_mem' := fun r => by obtain ⟨a, rfl⟩ := residue_surjective r; exact hA a }
    exact B.inv_mem_of_algebraic (x := ⟨z, hzA⟩) (mem_algebraicClosure_iff.1 hz)

theorem eq_zero_of_inv_mem [IsLocalRing V] (ev : V →+* K) {r : V} (hr : r ∈ maximalIdeal V) (h : (ev r)⁻¹ ∈ ev.range) :
    ev r = 0 := by
  by_contra h0
  obtain ⟨r', hr'⟩ := h
  have h₁ : 1 - r * r' ∈ RingHom.ker ev := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hr', mul_inv_cancel₀ h0, sub_self]
  have h₂ := le_maximalIdeal (RingHom.ker_ne_top ev) h₁
  have h₃ := add_mem h₂ (Ideal.mul_mem_right r' _ hr)
  rw [sub_add_cancel] at h₃
  exact (maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 h₃)

theorem cycAway_mem {n : ℕ} (hn : n ≠ 0) {k₀ : Subfield K} (hk : IsAlgClosed k₀) (θ : cycAway n →+* K) (a : cycAway n) :
    θ a ∈ k₀ := by
  let v : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
  have hv : (n : cycAway n) * v = 1 := Subtype.ext (by simp [v, hn])
  have hz : θ (zetaAway n) ^ n = 1 := by
    rw [← cycBase_ζ hn]
    exact ((cycBase hn).prim K θ).pow_eq_one
  obtain ⟨x, hx⟩ := a
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · refine mem_of_isIntegralElem hk (Int.castRingHom K) (fun a => intCast_mem k₀ a) (z := θ (zetaAway n))
        ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hn, ?_⟩
      simp [hz]
    · have h : θ v = (n : K)⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← map_natCast θ, ← map_mul, hv, map_one])
      exact (h ▸ inv_mem (natCast_mem k₀ n) : θ v ∈ k₀)
  | zero => exact (map_zero θ ▸ zero_mem _ : θ 0 ∈ k₀)
  | one => exact (map_one θ ▸ one_mem _ : θ 1 ∈ k₀)
  | add x y hx' hy' hx hy => exact (map_add θ _ _ ▸ add_mem hx hy : θ (⟨x, hx'⟩ + ⟨y, hy'⟩) ∈ k₀)
  | neg x hx' hx => exact (map_neg θ _ ▸ neg_mem hx : θ (-⟨x, hx'⟩) ∈ k₀)
  | mul x y hx' hy' hx hy => exact (map_mul θ _ _ ▸ mul_mem hx hy : θ (⟨x, hx'⟩ * ⟨y, hy'⟩) ∈ k₀)

end Alg

section Points

variable {K : Type} [Field K] {k₀ : Subfield K} {X Y : Scheme.{0}}

theorem defOver_comp {P : Sp K ⟶ X} (h : DefOver k₀ P) (f : X ⟶ Y) : DefOver k₀ (P ≫ f) := by
  obtain ⟨P₀, rfl⟩ := h
  exact ⟨P₀ ≫ f, (Category.assoc _ _ _).symm⟩

theorem defOver_spMap {O : Type} [CommRing O] {θ : O →+* K} (h : ∀ a, θ a ∈ k₀) : DefOver k₀ (spMap θ) :=
  ⟨spMap (θ.codRestrict k₀ h), by rw [← spMap_comp]; rfl⟩

theorem mem_of_defOver {y : Y} (θ : Y.presheaf.stalk y →+* K) (h : DefOver k₀ (spMap θ ≫ Y.fromSpecStalk y)) (a) :
    θ a ∈ k₀ := by
  obtain ⟨P₀, hP⟩ := h
  have hs : P₀ (closedPoint k₀) ⤳ y := by
    have h₁ : (spMap k₀.subtype ≫ P₀) (closedPoint K) ∈ Set.range (Y.fromSpecStalk y) := by
      rw [hP]; exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rw [Scheme.range_fromSpecStalk] at h₁
    have h₃ : (spMap k₀.subtype ≫ P₀) (closedPoint K) = P₀ (closedPoint k₀) :=
      (Scheme.Hom.comp_apply _ _ _).trans (congrArg P₀ (Subsingleton.elim _ _))
    exact h₃ ▸ h₁
  have h₂ : Spec.map (Y.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := .of k₀) P₀ ≫
      CommRingCat.ofHom k₀.subtype) ≫ Y.fromSpecStalk y = spMap θ ≫ Y.fromSpecStalk y := by
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hP]
  rw [cancel_mono] at h₂
  have h₃ := congrArg (fun f => f.hom a) (Spec.map_injective h₂)
  exact (h₃ ▸ (Scheme.stalkClosedPointTo (R := .of k₀) P₀ (Y.presheaf.stalkSpecializes hs a)).2 : θ a ∈ k₀)

theorem defOver_of_comp (hk : IsAlgClosed k₀) {P : Sp K ⟶ X} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (h : DefOver k₀ (P ≫ f)) : DefOver k₀ P := by
  let x : X := P (closedPoint K)
  let θ : X.presheaf.stalk x →+* K := (Scheme.stalkClosedPointTo (R := .of K) P).hom
  have hl : IsLocalHom θ := Scheme.isLocalHom_stalkClosedPointTo' (R := K) P
  have e : spMap θ ≫ X.fromSpecStalk x = P := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of K) P
  have h₁ : ∀ a, θ.comp (f.stalkMap x).hom a ∈ k₀ := mem_of_defOver _ (by
    have e₁ : spMap (f.stalkMap x).hom ≫ Y.fromSpecStalk (f x) = X.fromSpecStalk x ≫ f :=
      Scheme.SpecMap_stalkMap_fromSpecStalk f
    rw [spMap_comp, Category.assoc, e₁, ← Category.assoc, e]
    exact h)
  rw [← e]
  refine defOver_comp (defOver_spMap fun a => mem_of_isIntegralElem hk _ h₁ ?_) _
  have hf := (GlobalTheory.residueField_map_finite_of_quasiFinite (f.stalkMap x).hom (f.quasiFiniteAt x)).to_isIntegral
  have hi := (RingHom.isIntegral_of_surjective _ (residue_surjective (R := Y.presheaf.stalk (f x)))).trans _ _ hf (residue _ a)
  exact hi.map (ResidueField.lift θ)

end Points

section Pow

variable {K : Type} [Field K] {k₀ : Subfield K} {o : Type} [CommRing o] {ζ : o} {h n : ℕ} {F : SFam h n ζ} {r : ℕ}

theorem defOver_pow (hk : IsAlgClosed k₀) {k : ℕ} (hu : IsUnit (k : o)) (P : Sp K ⟶ (LowChart.powA F r).left)
    (h₀ : DefOver k₀ (P ≫ (LowChart.powA F r).hom))
    (h₁ : ∀ i, DefOver k₀ (P ≫ (LowChart.coord F i).left ≫ (𝟙 F.univ.A ^ k).left)) : DefOver k₀ P := by
  have := F.univ.ab.comm
  have := F.univ.ab.smooth
  have := F.univ.ab.proper
  have hu' : IsUnit (k : Γ(F.X, ⊤)) := by
    have := hu.map ((Scheme.ΓSpecIso (.of o)).inv ≫ F.s.appTop).hom
    rwa [map_natCast] at this
  have := GrpTangent.isFinite_id_pow F.univ.A hu'
  have : Epi (spMap k₀.subtype) := by
    have : Flat (spMap k₀.subtype) := by
      rw [spMap, Flat.SpecMap_iff]
      exact RingHom.Flat.of_isField (Field.toIsField k₀) _
    have : Surjective (spMap k₀.subtype) := ⟨Function.surjective_to_subsingleton _⟩
    exact Flat.epi_of_flat_of_surjective _
  obtain ⟨u, hu⟩ := h₀
  choose p hp using fun i => defOver_of_comp hk (P := P ≫ (LowChart.coord F i).left) (𝟙 F.univ.A ^ k).left
    (by rw [Category.assoc]; exact h₁ i)
  have hpu : ∀ i, p i ≫ F.univ.A.hom = u := fun i => by
    rw [← cancel_epi (spMap k₀.subtype), hu, ← Category.assoc, hp, Category.assoc, Over.w]
  refine ⟨LowChart.lift u p hpu, LowChart.hom_ext _ _ ?_ fun i => ?_⟩
  · rw [Category.assoc, LowChart.lift_hom, hu]
  · rw [Category.assoc, LowChart.lift_coord, hp]

theorem exists_essFiniteType_stalk (y : (LowChart.powA F r).left) :
    ∃ b : o →+* (LowChart.powA F r).left.presheaf.stalk y, b.EssFiniteType := by
  have e0 : ∀ p : PrimeSpectrum o, (StructureSheaf.toStalk o p).hom.EssFiniteType := fun p =>
    Algebra.EssFiniteType.of_isLocalization (R := o) ((Spec.structureSheaf o).presheaf.stalk p) p.asIdeal.primeCompl
  exact ⟨_, RingHom.EssFiniteType.comp (e0 (LowChart.toO F r y)) (LocallyOfFiniteType.stalkMap (LowChart.toO F r) y)⟩

theorem c₀_smul_single [IsNoetherianRing o] (y : (LowChart.powA F r).left) (k : ℕ) (i : Fin r) :
    (LowChart.c₀ F y ((k : ℤ) • Pi.single i 1)).left ≫ Pdiv.PullbackComparison.pφ (LowChart.toPow F y ≫ (LowChart.powA F r).hom) F.univ.A =
      LowChart.toPow F y ≫ (LowChart.coord F i).left ≫ (𝟙 F.univ.A ^ k).left := by
  classical
  have e : LowChart.c₀ F y ((k : ℤ) • Pi.single i 1) = LowChart.pt F y i ^ k := by
    show ∏ j, LowChart.pt F y j ^ (((k : ℤ) • Pi.single i 1 : Fin r → ℤ) j) = _
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp
  have pb := Pdiv.PullbackComparison.isGrpPullback (LowChart.toPow F y ≫ (LowChart.powA F r).hom) F.univ.A
  have e₁ := map_pow (pushHom pb (𝟙_ _)) (LowChart.pt F y i) k
  have e₂ : pushHom pb (𝟙_ _) (LowChart.pt F y i) ^ k = pushHom pb (𝟙_ _) (LowChart.pt F y i) ≫ (𝟙 F.univ.A ^ k) := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e, ← Category.assoc, ← LowChart.pt_left]
  exact congrArg (fun q => q.left) (e₁.trans e₂)

end Pow

section Core

variable {O W V : Type} [CommRing O] [CommRing W] [CommRing V] [IsLocalRing O] [IsLocalRing W] [IsLocalRing V]

omit [IsLocalRing W] in

theorem essFiniteType_residue (ib : W →+* V) {σ : Type} [Finite σ] (s : σ → V)
    (h : ∀ x : V, ∃ a ∈ Subring.closure (Set.range ib ∪ Set.range s), ∃ b ∈ Subring.closure (Set.range ib ∪ Set.range s),
      IsUnit b ∧ x * b - a ∈ maximalIdeal V) : ((residue V).comp ib).EssFiniteType := by
  classical
  let := ((residue V).comp ib).toAlgebra
  have := Fintype.ofFinite σ
  refine (Algebra.essFiniteType_iff _ _).2 ⟨Finset.univ.image fun i => residue V (s i), fun z => ?_⟩
  have key : ∀ a ∈ Subring.closure (Set.range ib ∪ Set.range s), residue V a ∈
      Algebra.adjoin W (↑(Finset.univ.image fun i => residue V (s i)) : Set (ResidueField V)) := fun a ha => by
    refine (Subring.closure_le (t := (Algebra.adjoin W
      (↑(Finset.univ.image fun i => residue V (s i)) : Set (ResidueField V))).toSubring.comap (residue V))).2 ?_ ha
    rintro _ (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · exact (Algebra.adjoin W (↑(Finset.univ.image fun i => residue V (s i)) : Set (ResidueField V))).algebraMap_mem w
    · exact Algebra.subset_adjoin (by simp)
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨a, ha, b, hb, hu, hx⟩ := h x
  refine ⟨residue V b, key b hb, hu.map _, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, map_mul, sub_eq_zero] at hx
  exact hx ▸ key a ha

end Core

section General

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

theorem unifOver_of_isMumfordFam {F : SFam g n ζ} {S : Scheme.{0}} {j : F.X ⟶ S} {V : Type} [CommRing V] [IsDomain V]
    [IsLocalRing V] {ξ : Sp V ⟶ S} {Q : Data V} {G₁ : Over (Sp V)} [GrpObj G₁] {y : Sp (FractionRing V) ⟶ F.X}
    {α₁ : pullback G₁.hom (jK V) ⟶ F.univ.A.left} (hG : IsSemiAbelian G₁) (hy : y ≫ j = jK V ≫ ξ)
    (h : IsMumfordFam F y α₁ Q) : UnifOver F j ξ Q := by
  refine ⟨h.isCN, fun R' _ _ _ ρ hR hρ hf D ε hD => ?_⟩
  obtain ⟨G', _, _, π, A, U, hπ, κ, πK, α, α₂, hκ, -, hA, hsq, hL, -⟩ := h.unif R' ρ hR hρ hf D ε hD
  obtain ⟨E, hE, -⟩ := grpPullback_iso hπ (isGrpPullback_pullback G₁ (spMap ρ))
  exact ⟨G', inferInstance, inferInstance, A, U, κ ≫ y, α, α₂,
    isSemiAbelian_of_grpIso E (IsSemiAbelian.pullback _ G₁ hG),
    by rw [Category.assoc, hy, ← Category.assoc, hκ, Category.assoc], hA, hsq, hL⟩

theorem quasiFinite_of_sepAt {S : Scheme.{0}} {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ S) (Q : Data V)
    (τ₀ : Gens Q) {m N : ℕ} (s : Fin m ⊕ Fin N → V)
    (hsep : ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) → SepAt Q τ₀ s ev k₀)
    {h n' r k : ℕ} (hn : n' ≠ 0) (F' : SFam h n' (zetaAway n')) (y : (LowChart.powA F' r).left) (hk : IsUnit (k : cycAway n'))
    {W : Type} [CommRing W] [IsLocalRing W] (ga : (LowChart.powA F' r).left.presheaf.stalk y →+* W) [IsLocalHom ga]
    (hga₁ : ∀ q : Ideal W, q.IsPrime → (maximalIdeal _).map ga ≤ q → q = maximalIdeal W) (hga₂ : ((residue W).comp ga).Finite)
    (ib : W →+* V) [IsLocalHom ib] (hb : FromBase Q τ₀ ib)
    (β : Q.B.left ⟶ F'.univ.A.left) (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left)
    (hβ : IsGrpPullback Q.B F'.univ.A
      (spMap (ib.comp ga) ≫ (LowChart.powA F' r).left.fromSpecStalk y ≫ (LowChart.powA F' r).hom) β)
    (hβ₂ : IsSquare β β₂) (hL : LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂))
    (hc : ∀ i, ∃ a, (Q.c a).left ≫ β = spMap (ib.comp ga) ≫ (LowChart.powA F' r).left.fromSpecStalk y ≫
      (LowChart.coord F' i).left ≫ (𝟙 F'.univ.A ^ k).left)
    (hV₁ : ∀ q : Ideal V, q.IsPrime →
      (∀ a ∈ Subring.closure (Set.range ib ∪ Set.range s), a ∈ maximalIdeal V → a ∈ q) → q = maximalIdeal V)
    (hV₂ : ∀ x : V, ∃ a ∈ Subring.closure (Set.range ib ∪ Set.range s), ∃ b ∈ Subring.closure (Set.range ib ∪ Set.range s),
      IsUnit b ∧ x * b - a ∈ maximalIdeal V) :
    (∀ p : Ideal V, p.IsPrime → (maximalIdeal (S.presheaf.stalk (ξ (closedPoint V)))).map
        (Scheme.stalkClosedPointTo (R := .of V) ξ).hom ≤ p → p = maximalIdeal V) ∧
      ((residue V).comp (Scheme.stalkClosedPointTo (R := .of V) ξ).hom).Finite := by
  let O : Type := S.presheaf.stalk (ξ (closedPoint V))
  let φ : O →+* V := (Scheme.stalkClosedPointTo (R := .of V) ξ).hom
  have hl : IsLocalHom φ := Scheme.isLocalHom_stalkClosedPointTo' (R := V) ξ
  have eφ : spMap φ ≫ S.fromSpecStalk _ = ξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of V) ξ
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K), (∀ a ∈ maximalIdeal O, ev.comp φ a = 0) →
      ∀ a ∈ Subring.closure (Set.range ib ∪ Set.range s),
        (ev.comp φ).IsIntegralElem (ev a) ∧ (a ∈ maximalIdeal V → ev a = 0) := by
    intro K _ _ ev hev
    obtain ⟨k₀, hk₀, hφ, hint⟩ := exists_algClosure (ev.comp φ) hev
    have hz : ∀ a ∈ maximalIdeal V, ev a ∈ k₀ → ev a = 0 := fun a ha h₀ =>
      eq_zero_of_inv_mem ev ha ((hint _ h₀).2 ev.range (fun b => ⟨φ b, rfl⟩) ⟨a, rfl⟩)
    have e₁ : spMap ev ≫ ξ = spMap (ev.comp φ) ≫ S.fromSpecStalk _ := by rw [spMap_comp, Category.assoc, eφ]
    obtain ⟨-, hA, hB⟩ := hsep K ev k₀ hk₀ (fun p => by
      have h₁ : spMap (ev.comp φ) p = closedPoint O := by
        refine PrimeSpectrum.ext (((maximalIdeal.isMaximal O).eq_of_le (spMap (ev.comp φ) p).isPrime.ne_top ?_).symm)
        intro a ha
        show ev.comp φ a ∈ p.asIdeal
        rw [hev a ha]
        exact zero_mem _
      rw [e₁]
      exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (S.fromSpecStalk _) h₁).trans Scheme.fromSpecStalk_closedPoint))
      (e₁ ▸ defOver_comp (defOver_spMap hφ) _)
    have hA' := hA _ _ _ _ F' _ β β₂ (Nat.one_le_iff_ne_zero.2 hn) (by
      obtain ⟨θ, hθ⟩ := Spec.map_surjective (spMap ev ≫ (spMap (ib.comp ga) ≫
        (LowChart.powA F' r).left.fromSpecStalk y ≫ (LowChart.powA F' r).hom) ≫ F'.s)
      rw [← hθ]
      exact defOver_spMap (θ := θ.hom) (cycAway_mem hn hk₀ _)) hβ hβ₂ hL
    have hP : DefOver k₀ (spMap (ev.comp (ib.comp ga)) ≫ (LowChart.powA F' r).left.fromSpecStalk y) := by
      refine defOver_pow hk₀ hk _ ?_ fun i => ?_
      · have h₁ := defOver_comp (hA' 0) F'.univ.A.hom
        have h₂ : (Q.c 0).left ≫ Q.B.hom = 𝟙 _ := Over.w (Q.c 0)
        rw [Category.assoc, Category.assoc, hβ.1.w, ← Category.assoc (Q.c 0).left, h₂] at h₁
        rw [spMap_comp, Category.assoc, Category.assoc]
        exact (Category.id_comp (spMap (ib.comp ga) ≫ (LowChart.powA F' r).left.fromSpecStalk y ≫
          (LowChart.powA F' r).hom)) ▸ h₁
      · obtain ⟨a, ha⟩ := hc i
        have h₁ := hA' a
        rw [ha] at h₁
        rw [spMap_comp, Category.assoc, Category.assoc]
        exact h₁
    have hy := mem_of_defOver _ hP
    have hW : ∀ w ∈ maximalIdeal W, ev.comp ib w = 0 := by
      have h₁ := hga₁ (RingHom.ker (ev.comp ib)) (RingHom.ker_isPrime _) (Ideal.map_le_iff_le_comap.2 fun a ha =>
        hz _ (map_nonunit (ib.comp ga) a ha) (hy a))
      intro w hw
      rw [← h₁] at hw
      exact hw
    have hW' : ∀ w, ev (ib w) ∈ k₀ := fun w => mem_of_isIntegralElem hk₀ _ hy
      ((hga₂.to_isIntegral (residue W w)).map (Ideal.Quotient.lift (maximalIdeal W) (ev.comp ib) hW))
    have hs := hB W ib hb hW'
    intro a ha
    have h₀ : ev a ∈ k₀ := by
      refine (Subring.closure_le (t := k₀.toSubring.comap ev)).2 ?_ ha
      rintro _ (⟨w, rfl⟩ | ⟨i, rfl⟩)
      · exact hW' w
      · exact hs i
    exact ⟨(hint _ h₀).1, fun hm => hz a hm h₀⟩
  refine ⟨fun p hp hle => ?_, ?_⟩
  · let K := AlgebraicClosure p.ResidueField
    let ev : V →+* K := (algebraMap p.ResidueField K).comp (algebraMap V p.ResidueField)
    have hker : ∀ a, ev a = 0 ↔ a ∈ p := fun a =>
      (map_eq_zero_iff _ (algebraMap p.ResidueField K).injective).trans Ideal.algebraMap_residueField_eq_zero
    exact hV₁ p hp fun a ha hm => (hker a).1
      ((key K ev (fun b hb => (hker _).2 (hle (Ideal.mem_map_of_mem _ hb))) a ha).2 hm)
  · let K := AlgebraicClosure (ResidueField V)
    let ev : V →+* K := (algebraMap (ResidueField V) K).comp (residue V)
    have key' := key K ev fun b hb => (map_eq_zero_iff _ (algebraMap (ResidueField V) K).injective).2
      ((residue_eq_zero_iff _).2 (map_nonunit φ b hb))
    let := (ResidueField.map φ).toAlgebra
    have hint : ∀ a ∈ Subring.closure (Set.range ib ∪ Set.range s), IsAlgebraic (ResidueField O) (residue V a) := fun a ha => by
      obtain ⟨P, hP, hPa⟩ := (key' a ha).1
      refine IsIntegral.isAlgebraic ⟨P.map (residue O), hP.map _, (algebraMap (ResidueField V) K).injective ?_⟩
      rw [Polynomial.eval₂_map, Polynomial.hom_eval₂, map_zero]
      exact hPa
    have : Algebra.IsAlgebraic (ResidueField O) (ResidueField V) := ⟨fun z => by
      obtain ⟨x, rfl⟩ := residue_surjective z
      obtain ⟨a, ha, b, hb, hu, hx⟩ := hV₂ x
      rw [← residue_eq_zero_iff, map_sub, map_mul, sub_eq_zero] at hx
      rw [(eq_mul_inv_iff_mul_eq₀ (hu.map (residue V)).ne_zero).2 hx]
      exact (hint a ha).mul (hint b hb).inv⟩
    obtain ⟨b, hb₀⟩ := exists_essFiniteType_stalk y
    have f₀ : (algebraMap ℤ (cycAway n')).EssFiniteType :=
      (RingHom.finiteType_algebraMap.2 (finiteType_cycAway n')).essFiniteType
    have f₁ := (f₀.comp hb₀).comp hga₂.to_finiteType.essFiniteType
    have f₂ : (ResidueField.map ib).EssFiniteType :=
      RingHom.EssFiniteType.of_comp (residue W) (essFiniteType_residue ib s hV₂)
    have f₃ := f₁.comp f₂
    rw [Subsingleton.elim (RingHom.comp _ _) ((ResidueField.map φ).comp (Int.castRingHom _))] at f₃
    have : Algebra.EssFiniteType (ResidueField O) (ResidueField V) := RingHom.EssFiniteType.of_comp _ f₃
    have f₄ : (ResidueField.map φ).Finite := Algebra.finite_of_essFiniteType_of_isAlgebraic
    exact f₄.comp (RingHom.Finite.of_surjective _ (residue_surjective (R := O)))

end General

section Taut

open GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ}

theorem coord_ne_zero (C : TChart.Taut ζ g n φ) (k : Fin C.m ⊕ Fin C.N) : C.s k ≠ 0 := by
  intro h0
  let := C.ψ.toAlgebra
  have : Module.Flat (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R := C.compl.2.2.1
  have hreg := Module.Flat.isSMulRegular_of_isRegular (M := C.R) (MvPolynomial.isRegular_X (R := C.W) (n := k))
  apply one_ne_zero (α := C.R)
  apply hreg
  show MvPolynomial.X k • (1 : C.R) = MvPolynomial.X k • (0 : C.R)
  rw [smul_zero, Algebra.smul_def, _root_.mul_one]
  exact h0

theorem psi_mem_closure (C : TChart.Taut ζ g n φ) (a : MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) :
    C.ψ a ∈ Subring.closure (Set.range C.iw ∪ Set.range C.s) := by
  induction a using MvPolynomial.induction_on with
  | C w => exact Subring.subset_closure (Or.inl ⟨w, rfl⟩)
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p k hp => rw [map_mul]; exact mul_mem hp (Subring.subset_closure (Or.inr ⟨k, rfl⟩))

theorem lowBase_smul_single (B : LowBase ζ n) (k : ℕ) (i : Fin B.T.r) :
    (B.T.c₀ ((k : ℤ) • Pi.single i 1)).left ≫ B.β = B.u ≫ (LowChart.coord B.F i).left ≫ (𝟙 B.F.univ.A ^ k).left := by
  have e : B.T.c₀ ((k : ℤ) • Pi.single i 1) = B.T.c₀ (Pi.single i 1) ^ k := by
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul, B.T.c₀_zero, pow_zero]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, B.T.c₀_add, ih, pow_succ]
  have e₁ := map_pow (pushHom B.cart (𝟙_ _)) (B.T.c₀ (Pi.single i 1)) k
  have e₂ : pushHom B.cart (𝟙_ _) (B.T.c₀ (Pi.single i 1)) ^ k =
      pushHom B.cart (𝟙_ _) (B.T.c₀ (Pi.single i 1)) ≫ (𝟙 B.F.univ.A ^ k) := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e, ← Category.assoc, ← B.coord]
  exact congrArg (fun q => q.left) (e₁.trans e₂)

theorem quasiFinite_tautChart : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → (∀ p : Ideal C.R, p.IsPrime → (maximalIdeal (S.presheaf.stalk (ξ (closedPoint C.R)))).map (Scheme.stalkClosedPointTo ξ).hom ≤ p → p = maximalIdeal C.R) ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  intro hS g hg φ hφ hsi n hn ho F Z z i OZ d S π j _ BD hM hB C G₁ _ _ y α₁ ξ hF hy
  classical
  obtain ⟨J, hd, hJ, hval, hbl, -, -, hj, -⟩ := hB
  obtain ⟨τ₀, hτ, hb⟩ := exists_gens_of_dataFrom C.T C.iw C.s C.form n C.Q C.e finSumFinEquiv C.data
  have hrk : Module.finrank ℤ C.Q.X ≤ g := by
    rw [C.e.toIntLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    have := C.genus
    omega
  have hsep := hS g hg n hn ho F Z z i hM.isThetaCompact.1 φ hφ hsi d J S π j hd hJ hval hbl hj _ C.Q ξ
    (unifOver_of_isMumfordFam hF.1 hy hF.2.2.2.1) C.m C.N C.s (C.ε.map (pullBalEquiv id C.e.toIntLinearEquiv)) τ₀ hrk
    (C.cone.pull_equiv C.e.toIntLinearEquiv) (fun x hx => C.defin (C.e x) (by simpa using hx))
    (fun l => ⟨C.bd l, coord_ne_zero C _⟩) C.tor hτ
  obtain ⟨β, β₂, w, hβ, hsq, hw, hc, -⟩ := C.data
  have hl : IsLocalHom (Scheme.stalkClosedPointTo (R := .of C.W) C.u).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := C.W) C.u
  have hl' : IsLocalHom C.iw := C.ψ_loc
  have eu : spMap (Scheme.stalkClosedPointTo (R := .of C.W) C.u).hom ≫ Scheme.fromSpecStalk _ _ = C.u :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of C.W) C.u
  have eq₁ : spMap (C.iw.comp (Scheme.stalkClosedPointTo (R := .of C.W) C.u).hom) ≫ Scheme.fromSpecStalk _ _ =
      spMap C.iw ≫ C.u := by
    rw [spMap_comp, Category.assoc, eu]
  have hLT : (abelian₂ C.T.B C.T.M.L).IsLB := LB.isLB_linComb C.T.M.isLB _ _
  have hLQ : (abelian₂ C.Q.B C.Q.M.L).IsLB := LB.isLB_linComb C.Q.M.isLB _ _
  exact quasiFinite_of_sepAt ξ C.Q τ₀ C.s hsep (by omega) C.F _ (isUnit_natCast (show n ≠ 0 by omega))
    (Scheme.stalkClosedPointTo (R := .of C.W) C.u).hom
    (fun q hq hle => ((maximalIdeal.isMaximal _).eq_of_le hq.ne_top (C.u_et.2.1.symm.trans_le hle)).symm) C.u_et.2.2
    C.iw hb (β ≫ C.β) (β₂ ≫ C.β₂)
    ((hβ.comp C.cart).congr (by rw [reassoc_of% eq₁]; rfl) rfl)
    ⟨by rw [Category.assoc, C.sq.1, ← Category.assoc, hsq.1, Category.assoc],
      by rw [Category.assoc, C.sq.2, ← Category.assoc, hsq.2, Category.assoc]⟩
    (LBIso.trans hLQ (pull_isLB hLT _) (pull_isLB C.F.univ.isLB _) ⟨w, hw⟩ (GlobalTheory.PolDeg.lbIso_pull_comp C.lb β₂ rfl))
    (fun l => ⟨C.e.symm (Pi.single l 1), by
      rw [← Category.assoc (C.Q.c _).left, hc, C.e.apply_symm_apply, Category.assoc, lowBase_smul_single C.toLowBase,
        reassoc_of% eq₁]
      rfl⟩)
    (fun q hq hle => le_antisymm (le_maximalIdeal hq.ne_top) (C.compl.2.2.2.1.symm.trans_le
      (Ideal.map_le_iff_le_comap.2 fun a ha => hle _ (psi_mem_closure C a) ha)))
    (fun x => by
      obtain ⟨a, b, hb, hx⟩ := C.compl.2.2.2.2 x
      exact ⟨_, psi_mem_closure C a, _, psi_mem_closure C b, hb, hx⟩)

end Taut

end GlobalTheory.QFChart
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiFinite_tautologicalChart_of_separation : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → (∀ p : Ideal C.R, p.IsPrime → (maximalIdeal (S.presheaf.stalk (ξ (closedPoint C.R)))).map (Scheme.stalkClosedPointTo ξ).hom ≤ p → p = maximalIdeal C.R) ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  atlas_forward_decl GlobalTheory.QFChart.quasiFinite_tautChart
end

section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.DedekindDimFormula
open ReciprocityTheory.CA

theorem isMaximal_comap_C {o : Type} [CommRing o] [IsJacobsonRing o] (N : ℕ)
    (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal] :
    (𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o)).IsMaximal := by
  have hi := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing 𝔑
  letI := Ideal.Quotient.field 𝔑
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hi
    (⊥ : Ideal (MvPolynomial (Fin N) o ⧸ 𝔑))
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this

theorem isCM_localization (o : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] :
    ∃ δ : ℕ, ∀ (p : Ideal o) [p.IsMaximal],
      IsCM (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = δ := by
  by_cases hf : IsField o
  · refine ⟨0, fun p _ => ?_⟩
    letI := hf.toField
    have hp : p = ⊥ := (Ideal.eq_bot_or_top p).resolve_right (Ideal.IsMaximal.ne_top inferInstance)
    have hd : ringKrullDim (Localization.AtPrime p) = 0 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp,
        Ideal.height_bot]
      rfl
    refine ⟨⟨inferInstance, 0, by rw [hd]; rfl, ?_⟩, hd⟩
    refine ⟨[], rfl, by simp, ?_⟩
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simp)]
    exact RingTheory.Sequence.IsWeaklyRegular.nil _ _
  · refine ⟨1, fun p _ => ?_⟩
    have hp : p ≠ ⊥ := by
      intro h
      exact hf (Ring.isField_iff_maximal_bot.mpr (h ▸ inferInstance))
    haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain o hp _
    have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)
    refine ⟨⟨inferInstance, 1, by rw [hd]; rfl, ?_⟩, by rw [hd]; rfl⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
    have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := hϖ.not_isUnit
    refine ⟨[ϖ], rfl, by simpa using hm, ?_⟩
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hm),
      RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    exact IsSMulRegular.of_ne_zero hϖ.ne_zero

theorem exists_maximal_mvPolynomial_localization' {o : Type} [CommRing o] (N : ℕ) (p : Ideal o) [p.IsMaximal] (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal]
    (hc : 𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o) = p) :
    ∃ (𝔑' : Ideal (MvPolynomial (Fin N) (Localization.AtPrime p))) (_ : 𝔑'.IsMaximal),
      𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      Nonempty (Localization.AtPrime 𝔑' ≃+* Localization.AtPrime 𝔑) ∧ 𝔑'.height = 𝔑.height := by
  classical
  letI : Algebra (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.algebraMvPolynomial
  let W : Submonoid (MvPolynomial (Fin N) o) := p.primeCompl.map (MvPolynomial.C (σ := Fin N))
  haveI hL : IsLocalization W (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  have hdisj : Disjoint (W : Set (MvPolynomial (Fin N) o)) (𝔑 : Set _) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, hm, rfl⟩ hx
    exact hm (hc ▸ (show m ∈ 𝔑.comap MvPolynomial.C from hx))
  let 𝔑' := 𝔑.map (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))
  haveI hP : 𝔑'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint W _ 𝔑 inferInstance hdisj
  have hcm : 𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) = 𝔑 :=
    IsLocalization.under_map_of_isPrime_disjoint W _ inferInstance hdisj
  haveI hM : 𝔑'.IsMaximal := by
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hJt
    have h1 : 𝔑 ≤ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) :=
      hcm ▸ Ideal.comap_mono hJ.le
    have h2 : J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) ≠ ⊤ := by
      intro h
      apply hJt
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Fin N) o) ∈ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) := h ▸ Submodule.mem_top
      simpa using this
    have h3 := (‹𝔑.IsMaximal›.eq_of_le h2 h1)
    have h4 : J = 𝔑' := by
      have h5 := IsLocalization.map_comap W (MvPolynomial (Fin N) (Localization.AtPrime p)) J
      change Ideal.map _ (J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) = J at h5
      rw [← h3] at h5
      exact h5.symm
    exact hJ.ne' h4
  refine ⟨𝔑', hM, ?_, ?_, IsLocalization.height_map_of_disjoint W 𝔑 hdisj⟩
  · haveI : (𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _)).IsPrime := Ideal.comap_isPrime _ _
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : (MvPolynomial.C (algebraMap o (Localization.AtPrime p) x) : MvPolynomial (Fin N) (Localization.AtPrime p)) =
        algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) (MvPolynomial.C x) := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rw [e]
    exact Ideal.mem_map_of_mem _ (by rw [← hc] at hx; exact hx)
  · haveI h0 : IsLocalization.AtPrime (Localization.AtPrime 𝔑')
        (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization W _ 𝔑'
    haveI : IsLocalization 𝔑.primeCompl (Localization.AtPrime 𝔑') := by
      have hsub : (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl = 𝔑.primeCompl :=
        Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hcm]
      have h0' : IsLocalization (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl (Localization.AtPrime 𝔑') := h0
      rw [hsub] at h0'
      exact h0'
    exact ⟨(IsLocalization.algEquiv 𝔑.primeCompl (Localization.AtPrime 𝔑') (Localization.AtPrime 𝔑)).toRingEquiv⟩

theorem polyEquidim : ∀ (o : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [IsJacobsonRing o] (N : ℕ),
    ∃ d : ℕ, ∀ (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal],
      IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = (d : ℕ∞) := by
  intro o _ _ _ _ N
  obtain ⟨δ, hδ⟩ := isCM_localization o
  refine ⟨δ + N, fun 𝔑 _ => ?_⟩
  haveI := isMaximal_comap_C N 𝔑
  obtain ⟨hCM, hdim⟩ := hδ (𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o))
  obtain ⟨𝔑', h𝔑', hc, ⟨e⟩, hh⟩ := exists_maximal_mvPolynomial_localization' N _ 𝔑 rfl
  have h := isCM_localization_mvPolynomial hCM N 𝔑' hc
  refine ⟨h.1.of_ringEquiv e, ?_⟩
  have h2 := h.2
  rw [hdim, hh] at h2
  have h3 : ((𝔑.height : ℕ∞) : WithBot ℕ∞) = (((δ + N : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [h2]; push_cast; ring
  exact WithBot.coe_injective h3

end GlobalTheory.DedekindDimFormula

namespace GlobalTheory.DedekindDimFormula

theorem affine_heights (o A : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [IsJacobsonRing o]
    [CommRing A] [IsDomain A] [Algebra o A] [Algebra.FiniteType o A] :
    ∃ h : ℕ, (∀ (M : Ideal A) [M.IsMaximal], M.height = (h : ℕ∞)) ∧
      ∀ (P M : Ideal A) [P.IsPrime] [M.IsMaximal],
        (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType o A›
  obtain ⟨d, hd⟩ := polyEquidim o N
  set Q := RingHom.ker (f : MvPolynomial (Fin N) o →+* A) with hQdef
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  let e : (MvPolynomial (Fin N) o ⧸ Q) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := (f : MvPolynomial (Fin N) o →+* A)) hf
  obtain ⟨M₀, hM₀⟩ := Ideal.exists_maximal (MvPolynomial (Fin N) o ⧸ Q)
  haveI : (M₀.comap (Ideal.Quotient.mk Q)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hQle : Q.height ≤ d := by
    rw [← (hd (M₀.comap (Ideal.Quotient.mk Q))).2]
    exact Ideal.height_mono fun x hx => by
      simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, M₀.zero_mem]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Q.height = k := by
    have : Q.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top d) hQle
    exact ⟨Q.height.toNat, (ENat.coe_toNat this).symm⟩
  have hkd : k ≤ d := by rw [hk] at hQle; exact_mod_cast hQle
  refine ⟨d - k, fun M _ => ?_, fun P M _ _ => ?_⟩
  · haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
    haveI : ((M.comap e).comap (Ideal.Quotient.mk Q)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨hCM, hh⟩ := hd ((M.comap e).comap (Ideal.Quotient.mk Q))
    have e1 := GlobalTheory.FinTypeIntCatenary.height_comap_mk Q (M.comap e) hCM
    rw [hh, hk, RingEquiv.height_comap] at e1
    have : ((d - k : ℕ) : ℕ∞) + k = M.height + k := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hkd, e1, add_comm]
    exact (WithTop.add_right_cancel (ENat.coe_ne_top k) this).symm
  · haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
    haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
    have h := GlobalTheory.FinTypeIntCatenary.height_le_of_equidim d (fun 𝔑 _ => hd 𝔑) Q (P.comap e) (M.comap e)
    rw [RingEquiv.height_comap, RingEquiv.height_comap] at h
    have hdim : ringKrullDim ((MvPolynomial (Fin N) o ⧸ Q) ⧸ P.comap e) = ringKrullDim (A ⧸ P) :=
      ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e
        (Ideal.map_comap_of_surjective _ e.surjective P).symm)
    rwa [hdim] at h

end GlobalTheory.DedekindDimFormula

namespace GlobalTheory.DedekindDimFormula

end GlobalTheory.DedekindDimFormula
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.ChartDim

theorem isAlgebraic_of_quasiFinite (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [FaithfulSMul A K]
    [Algebra.QuasiFinite A K] : Algebra.IsAlgebraic A K := by
  letI : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
  haveI : IsScalarTower A (FractionRing A) K := FractionRing.isScalarTower_liftAlgebra A K
  haveI : Algebra.QuasiFinite (FractionRing A) K := .of_restrictScalars A _ _
  haveI : Module.Finite (FractionRing A) K := Algebra.QuasiFinite.iff_of_isArtinianRing.1 inferInstance
  haveI : Algebra.IsAlgebraic A (FractionRing A) := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  exact Algebra.IsAlgebraic.trans A (FractionRing A) K

theorem trdeg_le (k A B K : Type) [CommRing k] [IsDomain k] [CommRing A] [IsDomain A] [CommRing B] [Field K] [Algebra k A]
    [Algebra k B] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [FaithfulSMul k A] [FaithfulSMul A K]
    [Algebra.IsAlgebraic A K] (b : B →ₐ[k] K) (hb : Function.Injective b) : Algebra.trdeg k B ≤ Algebra.trdeg k A := by
  refine (trdeg_le_of_injective b hb).trans ?_
  rw [← trdeg_add_eq k A (A := K), trdeg_eq_zero (R := A) (A := K), add_zero]

theorem ringKrullDim_le_of_isAlgebraic (A B K : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K]
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType ℤ B] [Algebra A K] [FaithfulSMul A K] [Algebra.IsAlgebraic A K]
    (b : B →+* K) (hb : Function.Injective b) : ringKrullDim B ≤ ringKrullDim A := by
  have ha := FaithfulSMul.algebraMap_injective A K
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : CharP A p := RingHom.charP _ ha p
  haveI : CharP B p := RingHom.charP _ hb p
  rcases CharP.char_is_prime_or_zero K p with h | rfl
  · haveI := Fact.mk h
    letI := ZMod.algebra A p
    letI := ZMod.algebra B p
    letI := ZMod.algebra K p
    haveI : IsScalarTower ℤ (ZMod p) A := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : IsScalarTower ℤ (ZMod p) B := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : IsScalarTower (ZMod p) A K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : Algebra.FiniteType (ZMod p) A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
    haveI : Algebra.FiniteType (ZMod p) B := Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
    obtain ⟨s, hs⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := ZMod p) (S := A))
    obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := ZMod p) (S := B))
    have hle := trdeg_le (ZMod p) A B K
      { b with commutes' := fun r => RingHom.congr_fun (Subsingleton.elim (b.comp (algebraMap (ZMod p) B)) _) r } hb
    rw [hs, ht] at hle
    rw [ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field s hs, ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field t ht]
    exact_mod_cast hle
  · haveI : CharZero A := CharP.charP_to_charZero _
    haveI : CharZero B := CharP.charP_to_charZero _
    haveI : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective_int _)
    have hle := trdeg_le ℤ A B K b.toIntAlgHom hb
    rw [IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one A (RingHom.injective_int _),
      IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one B (RingHom.injective_int _)]
    exact WithBot.coe_le_coe.2 (add_le_add_left (OrderHomClass.mono Cardinal.toENat hle) 1)

theorem finiteType_int_quotient {A : Type} [CommRing A] [Algebra.FiniteType ℤ A] (I : Ideal A) :
    @Algebra.FiniteType ℤ (A ⧸ I) _ _ (Ring.toIntAlgebra _) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mk I).toIntAlgHom Ideal.Quotient.mk_surjective

theorem finiteType_int_mvPolynomial (A σ : Type) [CommRing A] [Algebra.FiniteType ℤ A] [Finite σ] :
    @Algebra.FiniteType ℤ (MvPolynomial σ A) _ _ (Ring.toIntAlgebra _) := by
  have h : Algebra.FiniteType ℤ (MvPolynomial σ A) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  convert h
  · rfl
  · exact Subsingleton.elim _ _

theorem ringKrullDim_quotient_ker_le {A B K : Type} [CommRing A] [CommRing B] [Field K]
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType ℤ B] (a : A →+* K) (ha : a.QuasiFinite) (b : B →+* K) :
    ringKrullDim (B ⧸ RingHom.ker b) ≤ ringKrullDim (A ⧸ RingHom.ker a) := by
  haveI := RingHom.ker_isPrime a
  haveI := RingHom.ker_isPrime b
  letI := a.toAlgebra
  letI := (RingHom.kerLift a).toAlgebra
  haveI : IsScalarTower A (A ⧸ RingHom.ker a) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.QuasiFinite A K := ha
  haveI : Algebra.QuasiFinite (A ⧸ RingHom.ker a) K := .of_restrictScalars A _ _
  haveI : FaithfulSMul (A ⧸ RingHom.ker a) K := (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective a)
  haveI := isAlgebraic_of_quasiFinite (A ⧸ RingHom.ker a) K
  haveI := finiteType_int_quotient (RingHom.ker a)
  haveI := finiteType_int_quotient (RingHom.ker b)
  exact ringKrullDim_le_of_isAlgebraic _ _ K (RingHom.kerLift b) (RingHom.kerLift_injective b)

theorem exists_flat_quasiFinite {o : Type} [CommRing o] {X : Scheme.{0}} (s : X ⟶ Sp o) (D : ℕ)
    (hs : SmoothOfRelativeDimension D s) (y : X) :
    ∃ φ : MvPolynomial (Fin D) o →+* X.presheaf.stalk y, φ.Flat ∧ φ.QuasiFinite := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) s hs ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  obtain ⟨t, ht, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 ht hxW
  obtain ⟨⟨g, hg⟩, hxg⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen g
  have h1 := h' g hg Γ(X, X.basicOpen g)
  have h3 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv h1
  obtain ⟨φ, -, hφ⟩ := h3.exists_etale_mvPolynomial
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hxg⟩ : X.basicOpen g)
  haveI := (hW.basicOpen g).isLocalization_stalk ⟨y, hxg⟩
  letI := φ.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin D) o) Γ(X, X.basicOpen g) := hφ
  refine ⟨(algebraMap Γ(X, X.basicOpen g) (X.presheaf.stalk y)).comp φ, RingHom.Flat.comp ?_ ?_, RingHom.QuasiFinite.comp ?_ ?_⟩
  · exact (inferInstance : Module.Flat (MvPolynomial (Fin D) o) Γ(X, X.basicOpen g))
  · exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ ((hW.basicOpen g).primeIdealOf ⟨y, hxg⟩).asIdeal.primeCompl)
  · exact RingHom.quasiFinite_algebraMap.2 (.of_isLocalization ((hW.basicOpen g).primeIdealOf ⟨y, hxg⟩).asIdeal.primeCompl)
  · exact (inferInstance : Algebra.QuasiFinite (MvPolynomial (Fin D) o) Γ(X, X.basicOpen g))

theorem ringKrullDim_le_add_of_flat {B R : Type} [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (ψ : B →+* R) (hψ : ψ.Flat) :
    ringKrullDim B ≤ ringKrullDim R + ringKrullDim (B ⧸ RingHom.ker ((residue R).comp ψ)) := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  obtain ⟨h, hh, hle⟩ := DedekindDimFormula.affine_heights ℤ B
  set P := RingHom.ker ((residue R).comp ψ) with hP
  haveI : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  have h1 : ringKrullDim B ≤ (M.height : WithBot ℕ∞) :=
    (ringKrullDim_le_iff_isMaximal_height_le _).2 fun m hm => by rw [hh m, hh M]
  refine h1.trans ((hle P M).trans (add_le_add_left ?_ _))
  letI := ψ.toAlgebra
  haveI : Module.Flat B R := hψ
  haveI : (maximalIdeal R).LiesOver P := ⟨by rw [hP, ← RingHom.comap_ker, ker_residue]; rfl⟩
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown P (maximalIdeal R)]
  exact WithBot.coe_le_coe.2 le_self_add

theorem mem_of_mem_minimalPrimes {A : Type} [CommRing A] [IsNoetherianRing A] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (hD : Dense U) (Q : PrimeSpectrum A) (hQ : Q.asIdeal ∈ minimalPrimes A) : Q ∈ U := by
  classical
  let t := (minimalPrimes.finite_of_isNoetherianRing A).toFinset.erase Q.asIdeal
  have h1 : ¬ t.inf id ≤ Q.asIdeal := fun h => by
    obtain ⟨I, hI, hle⟩ := Q.isPrime.inf_le'.1 h
    obtain ⟨hne, hI⟩ := Finset.mem_erase.1 hI
    rw [Set.Finite.mem_toFinset] at hI
    exact hne (le_antisymm hle (hQ.2 hI.1 hle))
  obtain ⟨f, hf, hfQ⟩ := SetLike.not_le_iff_exists.1 h1
  obtain ⟨z, hz, hzU⟩ := hD.inter_open_nonempty _ (PrimeSpectrum.basicOpen f).isOpen ⟨Q, hfQ⟩
  obtain ⟨Q', hQ', hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := z.asIdeal) bot_le
  have hQQ : Q' = Q.asIdeal := by
    by_contra hne
    have : t.inf id ≤ Q' := Finset.inf_le (f := id) (Finset.mem_erase.2 ⟨hne, (Set.Finite.mem_toFinset _).2 hQ'⟩)
    exact hz (hle (this hf))
  exact ((PrimeSpectrum.le_iff_specializes Q z).1 (show Q.asIdeal ≤ z.asIdeal from hQQ ▸ hle)).mem_open hU hzU

theorem finiteType_sections {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {S : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] {U : S.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(S, U) := by
  have hl : LocallyOfFiniteType (Spec.map (Spec.preimage (hU.fromSpec ≫ s))) := by
    rw [Spec.map_preimage]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hl
  have h := hl.comp (RingHom.finiteType_algebraMap.2 (inferInstance : Algebra.FiniteType ℤ o))
  rw [← RingHom.finiteType_algebraMap]
  convert h using 1
  exact Subsingleton.elim _ _

theorem exists_stalk_hom {S : Scheme.{0}} {U : S.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(S, U)) :
    ∃ a : Γ(S, U) →+* S.presheaf.stalk (hU.fromSpec P), a.QuasiFinite ∧ (maximalIdeal _).comap a = P.asIdeal ∧
      ringKrullDim (S.presheaf.stalk (hU.fromSpec P)) = P.asIdeal.height := by
  have hx : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  letI : Algebra Γ(S, U) (S.presheaf.stalk (hU.fromSpec P)) :=
    TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨hU.fromSpec P, hx⟩ : U)
  haveI : IsLocalization.AtPrime (S.presheaf.stalk (hU.fromSpec P)) P.asIdeal := hU.isLocalization_stalk' P hx
  exact ⟨algebraMap _ _, RingHom.quasiFinite_algebraMap.2 (.of_isLocalization P.asIdeal.primeCompl),
    IsLocalization.AtPrime.under_maximalIdeal _ P.asIdeal, IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal _⟩

theorem ringKrullDim_sections_le {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {S X : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] (j : X ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (sX : X ⟶ Sp o) (D : ℕ)
    (hs : SmoothOfRelativeDimension D sX) {U : S.Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(S, U) ≤ ringKrullDim o + D := by
  haveI := finiteType_sections s hU
  haveI : IsNoetherianRing Γ(S, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI : IsNoetherianRing o := Algebra.FiniteType.isNoetherianRing ℤ _
  rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot Γ(S, U))]
  refine IntFiniteTypeDim.ringKrullDim_quotient_le_of_minimalPrimes _ _ fun Q hQ => ?_
  let q : PrimeSpectrum Γ(S, U) := ⟨Q, hQ.1.1⟩
  obtain ⟨y, hy⟩ : q ∈ hU.fromSpec ⁻¹' Set.range j :=
    mem_of_mem_minimalPrimes (j.isOpenEmbedding.isOpen_range.preimage hU.fromSpec.continuous)
      (hj.preimage hU.fromSpec.isOpenEmbedding.isOpenMap) q hQ
  obtain ⟨φ, -, hφ⟩ := exists_flat_quasiFinite sX D hs y
  obtain ⟨a, -, ha, -⟩ := exists_stalk_hom hU q
  let e : S.presheaf.stalk (hU.fromSpec q) →+* X.presheaf.stalk y :=
    (j.stalkMap y).hom.comp (S.presheaf.stalkCongr (.of_eq hy.symm)).hom.hom
  haveI : IsLocalHom e := RingHom.isLocalHom_comp _ _
  haveI := finiteType_int_mvPolynomial o (Fin D)
  have h := ringKrullDim_quotient_ker_le ((residue _).comp φ)
    ((RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _ residue_surjective)).comp hφ)
    ((residue _).comp (e.comp a))
  rw [← RingHom.comap_ker (residue _) (e.comp a), ker_residue, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap, ha] at h
  refine h.trans ((ringKrullDim_quotient_le _).trans ?_)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem flat_map {A B σ : Type} [CommRing A] [CommRing B] {f : A →+* B} (hf : f.Flat) :
    (MvPolynomial.map (σ := σ) f).Flat := by
  letI := f.toAlgebra
  letI : Algebra (MvPolynomial σ A) (MvPolynomial σ B) := MvPolynomial.algebraMvPolynomial
  haveI : Module.Flat A B := hf
  exact RingHom.Flat.isStableUnderBaseChange A B (MvPolynomial σ A) (MvPolynomial σ B) hf

theorem card_basis {r : ℕ} {J : Type} [Fintype J] (ε : Module.Basis J ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) :
    Fintype.card J = r * (r + 1) / 2 := by
  have e : balForms (id : ℤ → ℤ) (Fin r → ℤ) = GlobalTheory.Forms.symForms ℤ (Fin r → ℤ) ℤ :=
    Submodule.ext fun β => mem_balForms_int.trans GlobalTheory.Forms.mem_symForms.symm
  rw [← Module.finrank_eq_card_basis ε, e, GlobalTheory.Forms.finrank_symLattice, Module.finrank_fin_fun, Nat.choose_two_right,
    Nat.add_sub_cancel, mul_comm]

theorem exists_ringKrullDim_eq (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] : ∃ k : ℕ, ringKrullDim A = k := by
  obtain ⟨h, hh, -⟩ := haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int; DedekindDimFormula.affine_heights ℤ A
  have h1 : ringKrullDim A ≤ (h : ℕ∞) := (ringKrullDim_le_iff_isMaximal_height_le _).2 fun m hm => by rw [hh m]
  have h0 : 0 ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
  induction hA : ringKrullDim A with
  | bot => simp [hA] at h0
  | coe a =>
    rw [hA, WithBot.coe_le_coe] at h1
    exact ⟨a.toNat, by rw [← WithBot.coe_natCast, ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top h) h1)]⟩

theorem ringKrullDim_stalk_le {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {S X : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] (j : X ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (sX : X ⟶ Sp o) (D : ℕ)
    (hs : SmoothOfRelativeDimension D sX) {B R : Type} [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B] [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R) (hψ : ψ.Flat) (hB : ringKrullDim B = ringKrullDim o + D) {x : S}
    (f : S.presheaf.stalk x →+* R) [IsLocalHom f] (hf : ((residue R).comp f).Finite) :
    ringKrullDim (S.presheaf.stalk x) ≤ ringKrullDim R := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨P, rfl⟩ : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_stalk_hom hU P
  haveI := finiteType_sections s hU
  have h1 := ringKrullDim_quotient_ker_le (((residue R).comp f).comp a) ((RingHom.QuasiFinite.of_finite hf).comp ha₁)
    ((residue R).comp ψ)
  rw [← RingHom.comap_ker _ a, ← RingHom.comap_ker _ f, ker_residue, IsLocalRing.maximalIdeal_comap, ha₂] at h1
  haveI := P.isPrime
  haveI := finiteType_int_quotient P.asIdeal
  obtain ⟨k, hk⟩ := exists_ringKrullDim_eq (Γ(S, U) ⧸ P.asIdeal)
  have h2 := (RegularAscent.height_add_ringKrullDim_quotient_le P.asIdeal).trans
    ((ringKrullDim_sections_le s j hj sX D hs hU).trans (hB.ge.trans
      ((ringKrullDim_le_add_of_flat ψ hψ).trans (add_le_add_right h1 _))))
  rw [hk] at h2
  rw [ha₃]
  exact ENat.WithBot.add_le_add_natCast_right_iff.1 h2

theorem ringKrullDim_stalk_le_chart : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite → ringKrullDim (S.presheaf.stalk (ξ (closedPoint C.R))) ≤ ringKrullDim C.R := by
  intro g _ φ _ _ n hn _ F Z z i OZ d S π j _ BD _ hB C G₁ _ _ y α₁ ξ _ _ hf
  obtain ⟨J, -, -, -, -, hP, hD, -⟩ := hB
  have hn0 : n ≠ 0 := by omega
  haveI : IsProper (π ≫ z) := GlobalTheory.SchemeWords.isProper_of_isProjOver hP
  haveI := finiteType_cycAway n
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI : IsNoetherianRing C.R := C.compl.1
  have hd : SmoothOfRelativeDimension C.h C.F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim C.F.univ (by omega) (cycBase hn0).ζ.isUnit (isUnit_natCast hn0)
  haveI := GlobalTheory.smoothOfRelativeDimension_powObj C.F.univ.A C.h hd C.T.r
  haveI := C.F.smooth
  obtain ⟨χ, hχ, -⟩ := exists_flat_quasiFinite (LowChart.toO C.F C.T.r) (C.T.r * C.h + C.h * (C.h + 1) / 2)
    (smoothOfRelativeDimension_comp _ _ (LowChart.powA C.F C.T.r).hom C.F.s) (C.u (closedPoint C.W))
  haveI := finiteType_int_mvPolynomial (cycAway n) (Fin (C.T.r * C.h + C.h * (C.h + 1) / 2))
  haveI := finiteType_int_mvPolynomial (MvPolynomial (Fin (C.T.r * C.h + C.h * (C.h + 1) / 2)) (cycAway n)) (Fin C.m ⊕ Fin C.N)
  refine ringKrullDim_stalk_le (π ≫ z) j hD F.s _ F.smooth _ ((flat_map (hχ.comp C.u_et.1)).comp C.compl.2.2.1) ?_ _ hf
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin, card_basis C.ε, add_assoc, ← Nat.cast_add]
  congr 2
  obtain ⟨a, ha⟩ := Nat.even_mul_succ_self C.h
  obtain ⟨b, hb⟩ := Nat.even_mul_succ_self C.T.r
  have : (C.h + C.T.r) * (C.h + C.T.r + 1) = C.h * (C.h + 1) + C.T.r * (C.T.r + 1) + 2 * (C.T.r * C.h) := by ring
  rw [C.genus] at this
  omega

end GlobalTheory.TChart.ChartDim
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_stalk_le_tautologicalChartRing : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite → ringKrullDim (S.presheaf.stalk (ξ (closedPoint C.R))) ≤ ringKrullDim C.R := by
  atlas_forward_decl GlobalTheory.TChart.ChartDim.ringKrullDim_stalk_le_chart
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChartEt

theorem injective_of_flat_isLocalHom {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hf : f.Flat) [hl : IsLocalHom f] : Function.Injective f := by
  algebraize [f]
  have : IsLocalHom (algebraMap A B) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  exact FaithfulSMul.algebraMap_injective A B

theorem charZero_stalk_of_flat {o : Type} [CommRing o] [IsDomain o] [CharZero o] (X : Scheme.{0}) (s : X ⟶ Sp o)
    [Flat s] (x : X) : CharZero (X.presheaf.stalk x) := by
  have hf : (s.stalkMap x).hom.Flat := Flat.stalkMap s x
  have h0 : CharZero ((Sp o).presheaf.stalk (s x)) := by
    have : CharZero Γ(Sp o, ⊤) := (Scheme.ΓSpecIso (.of o)).hom.hom.charZero
    exact charZero_of_injective_ringHom (f := ((Sp o).presheaf.germ ⊤ (s x) trivial).hom)
      (germ_injective_of_isIntegral (Sp o) (U := ⊤) (s x) trivial)
  exact charZero_of_injective_ringHom (injective_of_flat_isLocalHom _ hf)

theorem essFiniteType_int_stalk (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] (x : X) :
    Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum (cycAway n) := s x
  have h2 : (algebraMap (cycAway n) ((Spec.structureSheaf (cycAway n)).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  haveI := finiteType_cycAway n
  have h3 : (algebraMap ℤ (cycAway n)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem charZero_stalk_centre {g n : ℕ} (F : SFam g n (zetaAway n)) {S : Scheme.{0}} (j : F.X ⟶ S)
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (y : Sp (FractionRing R) ⟶ F.X) (ξ : Sp R ⟶ S)
    (hy : y ≫ j = jK R ≫ ξ) : CharZero (S.presheaf.stalk (ξ (closedPoint R))) := by
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : Flat F.s := inferInstance
  let w : Sp (FractionRing R) := closedPoint (FractionRing R)
  have hsp : ξ (jK R w) ⤳ ξ (closedPoint R) := (specializes_closedPoint _).map ξ.continuous
  have hjw : j (y w) = ξ (jK R w) := by
    rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
  haveI : CharZero (F.X.presheaf.stalk (y w)) := charZero_stalk_of_flat F.X F.s (y w)
  haveI h₁ : CharZero (S.presheaf.stalk (j (y w))) := (j.stalkMap (y w)).hom.charZero
  rw [hjw] at h₁
  exact (S.presheaf.stalkSpecializes hsp).hom.charZero

end GlobalTheory.TChartEt

namespace GlobalTheory.TChartEt

theorem isEtaleCompletion_tautChart : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified := by
  intro hSep g hg φ hφ hns n hn ho F Z z i OZ d S π j _ BD hM hB C G₁ _ _ y α₁ ξ hF hy
  obtain ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ := hB
  haveI : GlobalTheory.IsNormalScheme S := hNB.1
  haveI : CharZero (S.presheaf.stalk (ξ (closedPoint C.R))) := charZero_stalk_centre F j y ξ hy
  haveI : LocallyOfFiniteType (π ≫ z) := by
    obtain ⟨N, ιP, hιP, e⟩ := hP
    rw [← e]
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (cycAway n) N
    infer_instance
  haveI : Algebra.EssFiniteType ℤ (S.presheaf.stalk (ξ (closedPoint C.R))) :=
    essFiniteType_int_stalk n S (π ≫ z) _
  haveI : IsNoetherianRing C.R := C.compl.1
  obtain ⟨hqf, hfin⟩ := GlobalTheory.T.quasiFinite_tautologicalChart_of_separation hSep g hg φ hφ hns n hn ho F Z z i OZ d S π j BD hM
    ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ C G₁ y α₁ ξ hF hy
  have hdim := GlobalTheory.T.ringKrullDim_stalk_le_tautologicalChartRing g hg φ hφ hns n hn ho F Z z i OZ d S π j BD hM
    ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ C G₁ y α₁ ξ hF hy hfin
  have hgal := GlobalTheory.T.tautologicalChart_galois_rigid_stalk hn F S j C G₁ y α₁ ξ hF hy
  exact GlobalTheory.T.isEtaleCompletion_of_quasiFinite_galoisRigid _ _ (Scheme.stalkClosedPointTo ξ).hom C.compl.2.1 hqf hfin hdim hgal

end GlobalTheory.TChartEt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalChart_centre_isCompletedEtaleLocalMap : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified := by
  atlas_forward_decl GlobalTheory.TChartEt.isEtaleCompletion_tautChart
end
