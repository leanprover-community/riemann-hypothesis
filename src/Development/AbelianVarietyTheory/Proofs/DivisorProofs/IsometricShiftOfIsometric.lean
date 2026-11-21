import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSymmetricImpliesSwapFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagModelOfIsIsometry
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagSmoothArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellVarietyDimensionCounts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeArithVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousSwapRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_flag_smooth_arithmetic : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)), SmoothOfRelativeDimension (Nat.card (CellVar a l)) (str a l) ∧ topologicalKrullDim (Part a l) = (Nat.card (CellVar a l) + 1 : ℕ) ∧ GlobalTheory.IsArithVar (str a l) (Nat.card (CellVar a l)) := by
  first | exact @GlobalTheory.FlagZ.smooth_dim_isArithVar_part | exact GlobalTheory.FlagZ.smooth_dim_isArithVar_part | (intros; apply GlobalTheory.FlagZ.smooth_dim_isArithVar_part <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_variety_dimension_counts : ∀ (ι : Type) [Fintype ι] (N : ℕ), Nat.card (CellVar (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd) = dimFl ι N ∧ (∀ j : Fin (N + 1), Nat.card (CellVar (id : ι → ι) (fun _ => j)) = dimGr ι N j) ∧ ∀ x : ι × Fin (N + 1), 0 < (x.2 : ℕ) → (x.2 : ℕ) < N → Nat.card (CellVar (fun y : {y // y ≠ x} => y.1.1) (fun y => y.1.2)) + 1 = dimFl ι N := by
  first | exact @GlobalTheory.FlagZ.Count.card_cellVar | exact GlobalTheory.FlagZ.Count.card_cellVar | (intros; apply GlobalTheory.FlagZ.Count.card_cellVar <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

theorem isArithVar_hasHh_unique : ∀ (ι : Type) [Fintype ι] (N : ℕ), GlobalTheory.IsArithVar (flStr ι N) (dimFl ι N) ∧
    (GlobalTheory.Published.ArExists → HasHh ι N) ∧
    ∀ (h : HasHh ι N) (Φ : Pol ι N →ₗ[ℝ] ℝ), IsHh ι N Φ → Φ = hh h := by
  intro ι _ N
  have hd := GlobalTheory.T.partial_flag_smooth_arithmetic ι (ι × Fin (N + 1)) N Prod.fst Prod.snd
  rw [(GlobalTheory.T.cell_variety_dimension_counts ι N).1] at hd
  exact ⟨hd.2.2, fun H => ((H ℤ _ _ _ hd.2.2).2 _ grLine).1, fun _ _ hΦ => hΦ.eq_hh hd.2.1⟩

end GlobalTheory.FlagZ
end

section
open CategoryTheory AlgebraicGeometry GlobalTheory.CovTop GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.HermLB

namespace GlobalTheory.FlagZ

variable {ι : Type} [Fintype ι] {N : ℕ}

@[reassoc] theorem permute_plEmb_π (s : ι → ι) (x : ι × Fin (N + 1)) :
    permute (N := N) s ≫ plEmb Prod.fst Prod.snd ≫ Limits.Pi.π _ x =
      plEmb Prod.fst Prod.snd ≫ Limits.Pi.π _ (s x.1, x.2) :=
  comap_plEmb_π _ _ _ _ _ _ x

theorem permute_comp (a b : ι → ι) : permute (N := N) a ≫ permute b = permute fun τ => a (b τ) := by
  rw [← cancel_mono (plEmb Prod.fst Prod.snd)]
  refine Limits.Pi.hom_ext _ _ fun x => ?_
  simp only [Category.assoc, permute_plEmb_π, permute_plEmb_π_assoc]

theorem permute_id : permute (ι := ι) (N := N) (fun τ => τ) = 𝟙 _ := by
  rw [← cancel_mono (plEmb Prod.fst Prod.snd)]
  refine Limits.Pi.hom_ext _ _ fun x => ?_
  simp only [Category.assoc, permute_plEmb_π, Category.id_comp]

theorem isIso_permute (σ : Equiv.Perm ι) : IsIso (permute (N := N) σ) :=
  ⟨⟨permute σ.symm, by rw [permute_comp]; simp only [Equiv.apply_symm_apply]; exact permute_id,
    by rw [permute_comp]; simp only [Equiv.symm_apply_apply]; exact permute_id⟩⟩

end GlobalTheory.FlagZ

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {q : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k}

theorem isometric_of_refines {N L : HermLB p} {π : N.B.ι → L.B.ι} (h : TwistTop.Refines N L π 0) :
    N.Isometric L :=
  isometric_of_chart π h.le (fun x j j' hj hj' => h.g X (𝟙 X) x j j' hj hj')
    fun σ j y hy => ((h.φ σ j y hy).trans (add_zero _)).symm

theorem isometric_pull_of_eq (L : HermLB p) {f g : Y ⟶ X} (e : f = g) (hf : f ≫ p = q) (hg : g ≫ p = q) :
    (L.pull f hf).Isometric (L.pull g hg) := by
  subst e
  exact Isometric.refl _

end GlobalTheory.HermLB

namespace GlobalTheory.FlagZ

variable {ι : Type} [Fintype ι] {N : ℕ}

theorem isometric_pull_detDual {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι) (l : κ → Fin (N + 1))
    {ι' κ' : Type} [Fintype ι'] [Finite κ'] (a' : κ' → ι') (f : ι' → ι) (e : κ' → κ)
    (h : ∀ k, a (e k) = f (a' k)) (hπ : comap a l a' f e h ≫ GlobalTheory.FlagZ.str a' (fun k => l (e k)) = GlobalTheory.FlagZ.str a l) (k : κ') :
    ((detDual a' (fun k => l (e k)) k).pull (comap a l a' f e h) hπ).Isometric (detDual a l (e k)) :=
  by
  unfold detDual
  exact (isometric_of_refines (refines_pull_pull (GlobalTheory.ProjSpace.hermitianTwistingSheaf ℤ (plDim N (l (e k))))
    (plEmb a' (fun k => l (e k)) ≫ Limits.Pi.π _ k) (toZ_ext _ _) (comap a l a' f e h) hπ (toZ_ext _ _))).trans
    (isometric_pull_of_eq _ (comap_plEmb_π a l a' f e h k) _ _)

theorem isometric_pull_flDet (s : ι → ι) (hπ : permute (N := N) s ≫ flStr ι N = flStr ι N) (τ : ι)
    (l : Fin (N + 1)) : ((flDet τ l).pull (permute s) hπ).Isometric (flDet (s τ) l) :=
  isometric_pull_detDual Prod.fst Prod.snd Prod.fst s (fun x => (s x.1, x.2)) (fun _ => rfl) hπ (τ, l)

theorem isometric_pull_grLine (s : ι → ι) (hπ : permute (N := N) s ≫ flStr ι N = flStr ι N) (x : ι × Fin N) :
    ((grLine x).pull (permute s) hπ).Isometric (grLine (s x.1, x.2)) := by
  refine icls_eq_iff.1 ?_
  rw [icls_pull, grLine, grLine, icls_tens, icls_dual, icls_tens, icls_dual, map_add, map_neg, ← icls_pull,
    ← icls_pull, icls_eq_iff.2 (isometric_pull_flDet s hπ x.1 _), icls_eq_iff.2 (isometric_pull_flDet s hπ x.1 _)]

theorem isSelfInter_comb_grLine_perm : Hypotheses2 → ∀ (ι : Type) [Fintype ι] (N : ℕ) (σ : Equiv.Perm ι) (n : ι × Fin N → ℤ)
    (a : ℝ), (comb (grLine (ι := ι) (N := N)) n).IsSelfInter a →
      (comb (grLine (ι := ι) (N := N)) fun x => n (σ x.1, x.2)).IsSelfInter a := by
  intro P ι _ N σ n a ha
  have hX := (isArithVar_hasHh_unique ι N).1
  have H := Published.cycleHeights_of_arCalc P.p4
  have hπ : permute (N := N) σ.symm ≫ flStr ι N = flStr ι N := toZ_ext _ _
  haveI : IsIso (permute (N := N) σ.symm) := isIso_permute σ.symm
  have h₁ := H.isSelfInter_pull_of_isIso_restrict hX hX (permute σ.symm) hπ ⊤ ⟨genericPoint _, trivial⟩ ha
  refine Isometric.isSelfInter hX (icls_eq_iff.1 ?_) h₁
  rw [← icls_eq_iff.2 (isometric_comb_pull grLine n _ hπ), icls_comb, icls_comb]
  refine Fintype.sum_equiv (Equiv.prodCongr σ.symm (Equiv.refl _)) _ _ fun x => ?_
  rw [icls_eq_iff.2 (isometric_pull_grLine σ.symm hπ x)]
  simp only [Equiv.prodCongr_apply, Equiv.apply_symm_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq]
  rfl

end GlobalTheory.FlagZ
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

namespace GlobalTheory.CovTest.Multisection

theorem nonempty_flag_of_field (K : Type) [Field K] (F : (Spec (CommRingCat.of K)).Modules)
    (hF : VB.IsVB F 2) : Nonempty (Vert.Flag F 2) := by
  have key : ∀ (G : (Spec (CommRingCat.of K)).Modules) (r : ℕ), VB.IsVB G r →
      ∃ e : Fin r → Γ(G, ⊤), VB.IsFrame e := by
    intro G r h
    obtain ⟨U, e, hx, he⟩ := h (IsLocalRing.closedPoint K)
    have hU : ⊤ ≤ U := fun x _ => (Subsingleton.elim x (IsLocalRing.closedPoint K)) ▸ hx
    exact ⟨_, he.res hU⟩
  have hO := VB.isVB_structureModule (Spec (CommRingCat.of K))
  obtain ⟨e, he⟩ := key F 2 hF
  obtain ⟨e', he'⟩ := key _ 2 (hO.biprod hO)
  exact ⟨(Vert.Flag.ofBiprod hO hO).ofIso (he'.iso he)⟩

theorem exists_multisection : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k)
    (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (_ : π ≫ q = p) (E : B.Modules),
    GlobalTheory.VB.IsVB E 2 → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ Y), IsArithVar (i ≫ p) d ∧
      (i ≫ π) (genericPoint Z) = genericPoint B ∧ (i ≫ π).residueDegree (genericPoint Z) ≠ 0 := by
  intro k _ B Y _ _ q p d hq hp π w E hE fl hfl
  let K : Type := B.residueField (genericPoint B)
  let g : Spec (CommRingCat.of K) ⟶ B := B.fromSpecResidueField (genericPoint B)
  obtain ⟨fl'⟩ := nonempty_flag_of_field K ((Scheme.Modules.pullback g).obj E) (hE.pullback g)
  obtain ⟨g', ⟨hg', -⟩, -⟩ := hfl _ g (fun _ => fl')
  have hc := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y g'
  obtain ⟨e₁, d₁⟩ := ProjDrop.deg_eq_of_fieldPoint π (g' (IsLocalRing.closedPoint K)) (genericPoint B)
    (Ω := K) _ (𝟙 (B.residueField (genericPoint B)) : B.residueField (genericPoint B) ⟶ CommRingCat.of K)
    (by rw [hc, hg', Spec.map_id]; exact (Category.id_comp _).symm)
  have h1 : ProjDrop.deg (𝟙 (B.residueField (genericPoint B)) :
      B.residueField (genericPoint B) ⟶ CommRingCat.of K).hom = 1 := by
    rw [CommRingCat.hom_id]
    exact ProjDrop.deg_equiv (RingEquiv.refl K)
  have hn : π.residueDegree (g' (IsLocalRing.closedPoint K)) ≠ 0 := by
    intro h
    rw [h1, h, zero_mul] at d₁
    exact one_ne_zero d₁
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (g' (IsLocalRing.closedPoint K))
  have g₁ : (i ≫ π) (genericPoint Z) = genericPoint B := by rw [Scheme.Hom.comp_apply, hi, e₁]
  have n₁ : (i ≫ π).residueDegree (genericPoint Z) ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp, residueDegree_of_isClosedImmersion i, mul_one, hi]
    exact hn
  have hproj : IsProjOver (i ≫ p) := ProjSpace.isProjOver_comp_of_isClosedImmersion i hp.isProjOver
  have hflat : Flat ((i ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    haveI := hq.flat
    haveI : CharZero (B.residueField ((i ≫ π) (genericPoint Z))) :=
      g₁.symm ▸ DimCover.charZero_residueField (q ≫ spMap (Int.castRingHom k))
    haveI := (RingHom.charZero_iff ((i ≫ π).residueFieldMap (genericPoint Z)).hom.injective).mp this
    exact ProjDrop.charZero_of_residueField (genericPoint Z)
  refine ⟨Z, inferInstance, i, ⟨hq.isDomain, hq.finite, inferInstance, hproj, hflat,
    DimCover.topologicalKrullDim_eq k B Z q (i ≫ p) d hq hproj hflat (i ≫ π)
      (by rw [Category.assoc, w]) g₁ n₁⟩, g₁, n₁⟩

end GlobalTheory.CovTest.Multisection

end
end

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_two_flag_bundle_section : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k)
    (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (_ : π ≫ q = p) (E : B.Modules),
    GlobalTheory.VB.IsVB E 2 → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ Y), IsArithVar (i ≫ p) d ∧
      (i ≫ π) (genericPoint Z) = genericPoint B ∧ (i ≫ π).residueDegree (genericPoint Z) ≠ 0 := by
  atlas_forward_decl GlobalTheory.CovTest.Multisection.exists_multisection
end

section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

namespace GlobalTheory.AlterationOrder

theorem isFinite_spMap_int (k : Type) [CommRing k] (h : Module.Finite ℤ k) :
    IsFinite (spMap (Int.castRingHom k)) := by
  unfold spMap
  rw [IsFinite.SpecMap_iff]
  change (algebraMap ℤ k).Finite
  exact RingHom.finite_algebraMap.2 h

theorem hom_ext_int {X : Scheme.{0}} (f g : X ⟶ Sp ℤ) : f = g :=
  specZIsTerminal.hom_ext f g

theorem isArithVar_int {k : Type} [CommRing k] {Z : Scheme.{0}} {r : Z ⟶ Sp k} {d : ℕ}
    (h : IsArithVar r d) : IsArithVar (r ≫ spMap (Int.castRingHom k)) d := by
  have := isFinite_spMap_int k h.finite
  obtain ⟨hp, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB r).1 h.isProjOver
  refine ⟨inferInstance, inferInstance, h.isIntegral, hL.isProjOver _, ?_, h.dim_eq⟩
  rw [hom_ext_int (_ ≫ spMap (Int.castRingHom ℤ)) (r ≫ spMap (Int.castRingHom k))]
  exact h.flat

theorem isArithVar_of_int {k : Type} [CommRing k] (hd : IsDomain k) (hf : Module.Finite ℤ k)
    {Z : Scheme.{0}} {r : Z ⟶ Sp k} {d : ℕ} (h : IsArithVar (r ≫ spMap (Int.castRingHom k)) d) :
    IsArithVar r d := by
  have := isFinite_spMap_int k hf
  obtain ⟨hp, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 h.isProjOver
  have : IsProper r := IsProper.of_comp r (spMap (Int.castRingHom k))
  refine ⟨hd, hf, h.isIntegral, hL.isProjOver _, ?_, h.dim_eq⟩
  rw [hom_ext_int (r ≫ spMap (Int.castRingHom k))
    ((r ≫ spMap (Int.castRingHom k)) ≫ spMap (Int.castRingHom ℤ))]
  exact h.flat

theorem regularAlteration_order : RegularAlteration → ∀ (k : Type) [CommRing k] (Z : Scheme.{0}) [IsIntegral Z] (r : Z ⟶ Sp k) (d : ℕ),
    IsArithVar r d → ∃ (B' : Scheme.{0}) (_ : IsIntegral B') (ρ : B' ⟶ Z), IsArithVar (ρ ≫ r) d ∧
      (∀ b : B', IsRegularLocalRing (B'.presheaf.stalk b)) ∧ ρ (genericPoint B') = genericPoint Z ∧
      ρ.residueDegree (genericPoint B') ≠ 0 := by
  intro H k _ Z _ r d h
  obtain ⟨Y, hY, ρ, h1, h2, h3, h4⟩ := H Z _ d (isArithVar_int h)
  refine ⟨Y, hY, ρ, isArithVar_of_int h.isDomain h.finite ?_, h2, h3, h4⟩
  rwa [Category.assoc]

end GlobalTheory.AlterationOrder
end

section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_integral_cover_same_dimension : RegularAlteration → ∀ (k : Type) [CommRing k] (Z : Scheme.{0}) [IsIntegral Z] (r : Z ⟶ Sp k) (d : ℕ),
    IsArithVar r d → ∃ (B' : Scheme.{0}) (_ : IsIntegral B') (ρ : B' ⟶ Z), IsArithVar (ρ ≫ r) d ∧
      (∀ b : B', IsRegularLocalRing (B'.presheaf.stalk b)) ∧ ρ (genericPoint B') = genericPoint Z ∧
      ρ.residueDegree (genericPoint B') ≠ 0 := by
  first | exact @GlobalTheory.AlterationOrder.regularAlteration_order | exact GlobalTheory.AlterationOrder.regularAlteration_order | (intros; apply GlobalTheory.AlterationOrder.regularAlteration_order <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_base_change_arith_variety : ∀ (k : Type) [CommRing k] (B Y B' : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsIntegral B']
    (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (_ : π ≫ q = p)
    (E : B.Modules), GlobalTheory.VB.IsVB E 2 → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ g : B' ⟶ B, IsArithVar (g ≫ q) d →
    g (genericPoint B') = genericPoint B → g.residueDegree (genericPoint B') ≠ 0 →
    ∃ (_ : IsIntegral (pullback π g : Scheme.{0})), IsArithVar (pullback.fst π g ≫ p) (d + 1) ∧
      pullback.fst π g (genericPoint (pullback π g : Scheme.{0})) = genericPoint Y ∧
      (pullback.fst π g).residueDegree (genericPoint (pullback π g : Scheme.{0})) ≠ 0 := by
  first | exact @GlobalTheory.LineBundleBaseChange.main | exact GlobalTheory.LineBundleBaseChange.main | (intros; apply GlobalTheory.LineBundleBaseChange.main <;> assumption)
end

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.CovTest.Reduce
open Limits

variable {k : Type} [CommRing k]

theorem isIsometry_pullbackCongr {X Y : Scheme.{0}} {q : Y ⟶ Sp k} {t : X ⟶ Sp k} {E : Y.Modules} {r : ℕ}
    (h : VMetric q E r) {f f' : X ⟶ Y} (e : f = f') (hf : f ≫ q = t) (hf' : f' ≫ q = t) :
    (h.pull f hf).IsIsometry (h.pull f' hf') ((Scheme.Modules.pullbackCongr e).app E) := by
  subst e
  intro σ V s s' y hy
  rfl

theorem isIsometry_bcIso {B Y B' : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
    (g : B' ⟶ B) {E : B.Modules} {r : ℕ} (h : VMetric q E r)
    (w' : pullback.snd π g ≫ g ≫ q = pullback.fst π g ≫ p) :
    ((h.pull π w).pull (pullback.fst π g) rfl).IsIsometry ((h.pull g rfl).pull (pullback.snd π g) w')
      (bcIso π g E) := by
  obtain ⟨-, hc⟩ := VMetric.isIsometry_pull_id_comp k B q E r h
  have e₁ : (pullback.fst π g ≫ π) ≫ q = pullback.fst π g ≫ p := by rw [Category.assoc, w]
  have e₂ : (pullback.snd π g ≫ g) ≫ q = pullback.fst π g ≫ p := by rw [Category.assoc, w']
  exact IsometryPullback.isIsometry_trans (hc Y _ p _ π (pullback.fst π g) w rfl e₁)
    (IsometryPullback.isIsometry_trans (isIsometry_pullbackCongr h pullback.condition e₁ e₂)
      (IsometryPullback.isIsometry_symm (hc B' _ (g ≫ q) _ g (pullback.snd π g) rfl w' e₂)))

theorem isometric_grLB_bcFlag {B Y B' : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
    (g : B' ⟶ B) {E : B.Modules} {r : ℕ} {h : VMetric q E r} (H : h.IsCInf)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r)
    (w' : pullback.snd π g ≫ g ≫ q = pullback.fst π g ≫ p) (i : Fin r) :
    (VMetric.grLB (bcFlag π g fl) i ((H.pull g rfl).pull (pullback.snd π g) w')).Isometric
      ((VMetric.grLB fl i (H.pull π w)).pull (pullback.fst π g) rfl) := by
  rw [bcFlag, VMetric.grLB_ofIso (isIsometry_bcIso π w g h w') ((H.pull π w).pull _ rfl)]
  exact VMetric.isometric_grLB_pull k Y _ p _ _ r (h.pull π w) (H.pull π w) fl (pullback.fst π g) rfl i

end GlobalTheory.CovTest.Reduce

namespace GlobalTheory.CovTest.Reduce
open Limits

theorem swap_of_section (hA : ArCalc) (hG : GdegPull) {G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ} (hS : SwapReg G)
    (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hp : IsArithVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)
    (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl))
    (A : HermLB q) (Φ Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ)
    (hΦ : IsArFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Φ)
    (hΨ : IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ)
    (a b : ℤ) (B' : Scheme.{0}) [IsIntegral B'] (g : B' ⟶ B) (s : B' ⟶ Y) (hs : s ≫ π = g)
    (hgq : IsArithVar (g ≫ q) d) (hreg : ∀ b : B', IsRegularLocalRing (B'.presheaf.stalk b))
    [IsIntegral (pullback π g : Scheme.{0})] (hY' : IsArithVar (pullback.fst π g ≫ p) (d + 1))
    (hfg : pullback.fst π g (genericPoint (pullback π g : Scheme.{0})) = genericPoint Y)
    (hfd : (pullback.fst π g).residueDegree (genericPoint (pullback π g : Scheme.{0})) ≠ 0) :
    Φ (lin ![(a : ℝ), b, 1] ^ (d + 2)) + Φ (lin ![(b : ℝ), a, 1] ^ (d + 2)) = Ψ (G (d + 1) a b) := by
  set ρ := pullback.fst π g
  set π' := pullback.snd π g
  set δ := ρ.residueDegree (genericPoint (pullback π g : Scheme.{0}))
  have w' : π' ≫ g ≫ q = ρ ≫ p := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, w]
  set L : Fin 3 → HermLB p := ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w]
  set L' : Fin 3 → HermLB (ρ ≫ p) := ![VMetric.grLB (bcFlag π g fl) 0 ((H.pull g rfl).pull π' w'),
    VMetric.grLB (bcFlag π g fl) 1 ((H.pull g rfl).pull π' w'), (A.pull g rfl).pull π' w']
  have iso : ∀ j, ((L j).pull ρ rfl).Isometric (L' j) := by
    intro j
    fin_cases j
    · exact (isometric_grLB_bcFlag π w g H fl w' 0).symm
    · exact (isometric_grLB_bcFlag π w g H fl w' 1).symm
    · have e₁ : (ρ ≫ π) ≫ q = ρ ≫ p := by rw [Category.assoc, w]
      have e₂ : (π' ≫ g) ≫ q = ρ ≫ p := by rw [Category.assoc, w']
      exact (HermLB.isometric_of_refines (HermLB.refines_pull_pull A π w ρ rfl e₁)).trans
        ((HermLB.isometric_pull_of_eq A pullback.condition e₁ e₂).trans
          (HermLB.isometric_of_refines (HermLB.refines_pull_comp A g rfl π' w' e₂)))
  have hΦ' : IsArFun L' (d + 1) ((δ : ℝ) • Φ) :=
    (((hA.arIso) k _ (ρ ≫ p) (d + 1) hY').2 (Fin 3) _ _
      (((hA.arProj) k Y _ p (ρ ≫ p) (d + 1) hp hY' ρ rfl hfg hfd).2 (Fin 3) L Φ hΦ)).2.1 L' iso
  have hΨ' : IsGeoFun L' (d + 1) ((δ : ℝ) • Ψ) := by
    refine ⟨fun n => ?_, fun P e he hP => ?_⟩
    · rw [LinearMap.smul_apply, hΨ.1 n, smul_eq_mul,
        ← hG k Y _ p (ρ ≫ p) (d + 1) hp hY' ρ rfl hfg hfd (comb L n)]
      exact ((isometric_comb_pull L n ρ rfl).symm.trans (isometric_comb_congr iso n)).gdeg_eq _
    · rw [LinearMap.smul_apply, hΨ.2 P e he hP, smul_zero]
  have hflat : Nonempty (Vert.Flag ((Scheme.Modules.pullback g).obj E) 2) :=
    ⟨(fl.pull s).ofIso ((Scheme.Modules.pullbackComp s π).app E ≪≫ (Scheme.Modules.pullbackCongr hs).app E)⟩
  have key := hS k B' _ (g ≫ q) (ρ ≫ p) d hgq hY' hreg π' w' _ (h.pull g rfl) (H.pull g rfl) hflat
    (bcFlag π g fl) (GlobalTheory.T.flag_bundle_pullback_base_change B Y B' π g Unit (fun _ => E) (fun _ => 2) (fun _ => fl) hfl)
    (A.pull g rfl) ((δ : ℝ) • Φ) ((δ : ℝ) • Ψ) hΦ' hΨ' a b
  simp only [LinearMap.smul_apply, smul_eq_mul, ← mul_add] at key
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hfd) key

end GlobalTheory.CovTest.Reduce

namespace GlobalTheory.CovTest

open Limits in

theorem swap2_of_swapRegular : ArCalc → RegularAlteration → GdegPull →
    ∀ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, SwapReg G → Swap2 G := by
  intro hA hR hG G hS k _ B Y _ _ q p d hq hp π w E h H fl hfl A Φ Ψ hΦ hΨ a b
  obtain ⟨Z, _, i, hZ, hZg, hZd⟩ := GlobalTheory.T.rank_two_flag_bundle_section k B Y q p d hq hp π w E h.isVB fl hfl
  obtain ⟨B', _, ρ₀, hB', hreg, hρg, hρd⟩ := GlobalTheory.T.exists_regular_integral_cover_same_dimension hR k Z (i ≫ p) d hZ
  have hgq : IsArithVar ((ρ₀ ≫ i ≫ π) ≫ q) d := by
    rwa [Category.assoc, Category.assoc, w]
  have hgg : (ρ₀ ≫ i ≫ π) (genericPoint B') = genericPoint B := by
    rw [Scheme.Hom.comp_apply, hρg, hZg]
  have hgd : (ρ₀ ≫ i ≫ π).residueDegree (genericPoint B') ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp, hρg]
    exact mul_ne_zero hZd hρd
  obtain ⟨_, hY', hfg, hfd⟩ := GlobalTheory.T.flag_bundle_base_change_arith_variety k B Y B' q p d hq hp π w E h.isVB fl hfl _ hgq hgg hgd
  exact Reduce.swap_of_section hA hG hS k B Y q p d hp π w E h H fl hfl A Φ Ψ hΦ hΨ a b B' _ (ρ₀ ≫ i)
    (Category.assoc _ _ _) hgq hreg hY' hfg hfd

end GlobalTheory.CovTest

end
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_identity_from_regular_base : ArCalc → RegularAlteration → GdegPull → ∀ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, SwapReg G → Swap2 G := by
  first | exact @GlobalTheory.CovTest.swap2_of_swapRegular | exact GlobalTheory.CovTest.swap2_of_swapRegular | (intros; apply GlobalTheory.CovTest.swap2_of_swapRegular <;> assumption)
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_pullback_formula : GdegPull := by
  first | exact @GlobalTheory.CovTest.gdegPull | exact GlobalTheory.CovTest.gdegPull | (intros; apply GlobalTheory.CovTest.gdegPull <;> assumption)
end

section
open GlobalTheory.Published GlobalTheory.CovTest

theorem GlobalTheory.CovTest.homog_swap_exists_of_ar_calc : ArCalc → RegularAlteration → ∃ G, Homog G ∧ Swap2 G := fun hC hR =>
  let ⟨G, hG, hS⟩ := GlobalTheory.T.exists_homogeneous_swap_regular hC
  ⟨G, hG, GlobalTheory.T.swap_identity_from_regular_base hC hR GlobalTheory.T.generic_degree_pullback_formula G hS⟩
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.GeoSwap

open HermLB

section Shift

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem isometric_pull_shift (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ)
    (π : Y ⟶ X) (hπ : π ≫ p = q) : ((L.shift t ht).pull π hπ).Isometric ((L.pull π hπ).shift t ht) :=
  isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t σ) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t σ) π hπ a y).symm

theorem isometric_shift_of_isometric {L M : HermLB p} (h : L.Isometric M) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) : (L.shift t ht).Isometric (M.shift t ht) := by
  obtain ⟨w, hw, h⟩ := h
  refine ⟨w, hw, fun σ a b y ha hb => ?_⟩
  have e := h σ a b y ha hb
  exact (congrArg (· + 2 * t σ) e).trans (add_right_comm _ _ _)

theorem isometric_tens_shift_left (L M : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) :
    ((L.shift t ht).tens M).Isometric ((L.tens M).shift t ht) :=
  isometric_of_eqOn fun σ a y _ => by
    show ((L.φ σ).φ a.1 y + (M.φ σ).φ a.2 y) + 2 * t σ = ((L.φ σ).φ a.1 y + 2 * t σ) + (M.φ σ).φ a.2 y
    ring

variable (p) in

def constB (t : ℝ) : HermLB p := (triv p).shift (fun _ => t) fun _ => rfl

theorem icls_shift_const (L : HermLB p) (t : ℝ) :
    (L.shift (fun _ => t) fun _ => rfl).icls = L.icls + (constB p t).icls := by
  rw [add_comm, constB, ← icls_tens, icls_eq_iff]
  exact (isometric_shift_of_isometric (isometric_triv_tens L).symm _ _).trans
    (isometric_tens_shift_left _ _ _ _).symm

theorem icls_constB_add (s t : ℝ) : (constB p (s + t)).icls = (constB p s).icls + (constB p t).icls := by
  rw [← icls_shift_const, icls_eq_iff]
  exact isometric_of_eqOn fun σ a y _ => by
    show ((0 : ℝ) + 2 * s) + 2 * t = (0 : ℝ) + 2 * (s + t)
    ring

variable (p) in

def constHom : ℝ →+ IsomClass p := AddMonoidHom.mk' (fun t => (constB p t).icls) icls_constB_add

theorem gdeg_shift_const (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (D : ℕ) :
    gdeg (L.shift t ht) D = gdeg L D := by
  simp only [gdeg, chInt, HermLB.shift, Weight.chernInt, Weight.chernPart_addFn_const]

theorem isometric_comb_three_shift (S Q A A' : HermLB p)
    (hA : A'.Isometric (A.shift (fun _ => 1) fun _ => rfl)) (m : Fin 3 → ℤ) (c : ℝ) (hc : ((m 2 : ℤ) : ℝ) = c) :
    (comb ![S, Q, A'] m).Isometric ((comb ![S, Q, A] m).shift (fun _ => c) fun _ => rfl) := by
  subst hc
  refine icls_eq_iff.1 ?_
  rw [icls_shift_const, icls_comb, icls_comb, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [icls_eq_iff.2 hA, icls_shift_const]
  have e : (constB p ((m 2 : ℤ) : ℝ)).icls = m 2 • (constB p 1).icls := by
    have := map_zsmul (constHom p) (m 2) 1
    simpa [constHom] using this
  rw [e, smul_add]
  abel

end Shift

theorem rename_lin_swap {κ : Type} [Fintype κ] [DecidableEq κ] (x y : κ) (c : κ → ℝ) :
    rename (Equiv.swap x y) (lin c) = lin fun z => c (Equiv.swap x y z) := by
  simp only [lin, map_sum, map_mul, rename_C, rename_X]
  exact Fintype.sum_equiv (Equiv.swap x y) _ _ fun z => by simp [Equiv.swap_apply_self]

theorem cast_triple (u v : ℤ) : (fun j => (((![u, v, 1] : Fin 3 → ℤ) j : ℤ) : ℝ)) = ![(u : ℝ), v, 1] := by
  funext j
  fin_cases j <;> simp

theorem geo_swap : ArCalc → RegularAlteration → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ Ψ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ, IsGeoFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Ψ → ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 → ∀ P : MvPolynomial (Σ a, Fin (r a)) ℝ, Ψ (rename (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩) P) = -Ψ P := by
  intro hC hR k _ B Y _ _ q p d D hq hp π w ι _ E r h H fl hfl Ψ hΨ a i i' hi
  obtain ⟨G, -, hS⟩ := GlobalTheory.CovTest.homog_swap_exists_of_ar_calc hC hR
  obtain ⟨Y₁, q₁, d₁, ρ, wρ, E₁, h₁, H₁, fl₁, M, rfl, hY₁, hfl₁, hS0, hS1, hM⟩ :=
    GlobalTheory.SwapBundle.swapFl_bundle k B Y q p d D hq hp π w ι E r h H fl hfl a i i' hi
  haveI := hY₁.isIntegral
  set x : Σ a, Fin (r a) := ⟨a, i⟩ with hx
  set y : Σ a, Fin (r a) := ⟨a, i'⟩ with hy
  have hxy : x ≠ y := by
    intro e
    rw [hx, hy, Sigma.mk.inj_iff] at e
    have := congrArg Fin.val (eq_of_heq e.2)
    omega
  set L : (Σ a, Fin (r a)) → HermLB p := fun z => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w) with hL
  have key : ∀ n : (Σ a, Fin (r a)) → ℤ,
      Ψ (lin (fun z => (n z : ℝ)) ^ (d₁ + 1)) + Ψ (lin (fun z => (n (Equiv.swap x y z) : ℝ)) ^ (d₁ + 1)) = 0 := by
    intro n
    set n' : (Σ a, Fin (r a)) → ℤ := fun z => if z = x ∨ z = y then 0 else n z with hn'
    set A₀ : HermLB q₁ := comb M n' with hA₀
    set A₁ : HermLB q₁ := A₀.shift (fun _ => 1) fun _ => rfl with hA₁
    set S := VMetric.grLB fl₁ 0 (H₁.pull ρ wρ) with hSd
    set Q := VMetric.grLB fl₁ 1 (H₁.pull ρ wρ) with hQd
    set Mf : Fin 3 → HermLB p := ![S, Q, A₀.pull ρ wρ] with hMf
    set Mf' : Fin 3 → HermLB p := ![S, Q, A₁.pull ρ wρ] with hMf'
    set Am : Fin 3 → (Σ a, Fin (r a)) → ℤ := ![Pi.single x 1, Pi.single y 1, n'] with hAm
    have hiso : ∀ j, (comb L (Am j)).Isometric (Mf j) := by
      intro j
      fin_cases j
      · exact (isometric_comb_single L x).trans hS0.symm
      · exact (isometric_comb_single L y).trans hS1.symm
      · exact SwapFlProof.comb_isometric_pullback L M ρ wρ n' (fun z => z = x ∨ z = y) (fun z hz => if_pos hz)
          (fun z hz => hM z (fun e => hz (Or.inl e)) (fun e => hz (Or.inr e)))
    set f : Fin 3 → MvPolynomial (Σ a, Fin (r a)) ℝ := fun j => lin fun z => (Am j z : ℝ) with hf
    set Ψ₃ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ := Ψ ∘ₗ (aeval f : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] _).toLinearMap with hΨ₃
    have hΨ' : IsGeoFun Mf (d₁ + 1) Ψ₃ := by
      refine ⟨fun m => ?_, fun P e he hP => ?_⟩
      · rw [hΨ₃, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, hf, aeval_lin]
        have h2 := hΨ.1 (fun z => ∑ j, m j * Am j z)
        simp only [Int.cast_sum, Int.cast_mul] at h2
        rw [h2]
        exact ((isometric_comb_comb L Am m).trans (isometric_comb_congr hiso m)).gdeg_eq _
      · rw [hΨ₃, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
        exact hΨ.2 _ e he (by simpa using hP.aeval _ fun j => isHomogeneous_lin _)
    have hA' : (A₁.pull ρ wρ).Isometric ((A₀.pull ρ wρ).shift (fun _ => 1) fun _ => rfl) :=
      isometric_pull_shift A₀ _ _ ρ wρ
    have hcomb : ∀ (m : Fin 3 → ℤ) (c : ℝ), ((m 2 : ℤ) : ℝ) = c →
        (comb Mf' m).Isometric ((comb Mf m).shift (fun _ => c) fun _ => rfl) :=
      fun m c hc => isometric_comb_three_shift S Q _ _ hA' m c hc
    have hΨ'' : IsGeoFun Mf' (d₁ + 1) Ψ₃ :=
      ⟨fun m => (hΨ'.1 m).trans (((hcomb m _ rfl).gdeg_eq _).trans (gdeg_shift_const _ _ _ _)).symm, hΨ'.2⟩
    obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p (d₁ + 1) hp).2 (Fin 3) Mf).1
    obtain ⟨Φ', hΦ'⟩ := ((hC.arExists k Y p (d₁ + 1) hp).2 (Fin 3) Mf').1
    have e1 := hS k Y₁ Y q₁ p d₁ hY₁ hp ρ wρ E₁ h₁ H₁ fl₁ hfl₁ A₀ Φ Ψ₃ hΦ hΨ' (n x) (n y)
    have e2 := hS k Y₁ Y q₁ p d₁ hY₁ hp ρ wρ E₁ h₁ H₁ fl₁ hfl₁ A₁ Φ' Ψ₃ hΦ' hΨ'' (n x) (n y)
    have hsh : ∀ u v : ℤ, Φ' (lin ![(u : ℝ), v, 1] ^ (d₁ + 2)) =
        Φ (lin ![(u : ℝ), v, 1] ^ (d₁ + 2)) + (((d₁ + 1 : ℕ) : ℝ) + 1) * 1 * Ψ₃ (lin ![(u : ℝ), v, 1] ^ (d₁ + 1)) := by
      intro u v
      have h1 := hΦ.1 ![u, v, 1]
      have h2 := hΦ'.1 ![u, v, 1]
      rw [cast_triple] at h1 h2
      have h3 := hC.arShift k Y p (d₁ + 1) hp (comb Mf ![u, v, 1]) _ 1 h1
      have h4 := (hcomb ![u, v, 1] 1 (by simp)).symm.isSelfInter hp h3
      rw [h2.unique hp h4, ← cast_triple u v, hΨ'.1 ![u, v, 1]]
    rw [hsh, hsh] at e2
    have e3 : (((d₁ + 1 : ℕ) : ℝ) + 1) * (Ψ₃ (lin ![(n x : ℝ), n y, 1] ^ (d₁ + 1)) +
        Ψ₃ (lin ![(n y : ℝ), n x, 1] ^ (d₁ + 1))) = 0 := by linarith
    have hpos : (((d₁ + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    have e4 := (mul_eq_zero.1 e3).resolve_left hpos
    have hx0 : n' x = 0 := if_pos (Or.inl rfl)
    have hy0 : n' y = 0 := if_pos (Or.inr rfl)
    have hne : ∀ z, z ≠ x → z ≠ y → n' z = n z := fun z h1 h2 => if_neg (by tauto)
    simp only [hΨ₃, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, hf, aeval_lin] at e4
    rw [hAm, SwapFlProof.lin_update_two_coords x y hxy n n' hx0 hy0 hne (n x) (n y),
      SwapFlProof.lin_update_two_coords x y hxy n n' hx0 hy0 hne (n y) (n x)] at e4
    convert e4 using 4
    · congr 1
      funext z
      rw [Function.update_eq_self, Function.update_eq_self]
    · congr 1
      funext z
      by_cases h1 : z = x
      · subst h1; simp [Function.update_apply, hxy, Equiv.swap_apply_left]
      · by_cases h2 : z = y
        · subst h2; simp [Function.update_apply, Equiv.swap_apply_right]
        · simp [Function.update_apply, h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hz := GlobalTheory.ArInt.Model.eq_zero_of_pow (d₁ + 1)
    (Ψ + Ψ ∘ₗ (rename (Equiv.swap x y) : MvPolynomial (Σ a, Fin (r a)) ℝ →ₐ[ℝ] _).toLinearMap)
    (fun n => by
      rw [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        map_pow (rename (Equiv.swap x y)), rename_lin_swap]
      exact key n)
    (fun P e he hP => by
      rw [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hΨ.2 P e he hP,
        hΨ.2 _ e he (hP.rename_isHomogeneous), add_zero])
  intro P
  have := LinearMap.congr_fun hz P
  rw [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply] at this
  linarith

end GlobalTheory.CovTest.GeoSwap

end
end
