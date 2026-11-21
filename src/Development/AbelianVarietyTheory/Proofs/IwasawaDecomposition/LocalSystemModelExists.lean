import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothBaseAndNormalCoordinateRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEmbeddingProjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentCombinationEigenAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesAgreeOnLieEmbeddingChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCells
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartCompatible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartGluingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SInfMulNormPlk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartGluing

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_base_and_normal_coordinate_ring : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (U : X.affineOpens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Smooth (cbase m U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (CR m U)) := by
  first | exact @GlobalTheory.FlagEmb.cell_smooth_normal | exact GlobalTheory.FlagEmb.cell_smooth_normal | (intros; apply GlobalTheory.FlagEmb.cell_smooth_normal <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_eigenframe_near_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), p.Prime → (p : ℂ) ∈ W.nonunits → IsOpen (Set.range Y.j) ∧ ∀ (x : Y.X) (U : Y.X.Opens), x ∈ U → x ∈ Set.range Y.j → ∃ (V : Y.X.affineOpens) (α : c.F →+* Γ(Y.X, V.1)) (e : Vecs Dw Y.t Γ(Y.X, V.1)) (n : ℕ) (en : Fin n ≃ Let Dw.mult), x ∈ V.1 ∧ V.1 ≤ U ∧ (V.1 : Set Y.X) ⊆ Set.range Y.j ∧ V.2.fromSpec ≫ Y.s = spMap (α.comp (c.V W).subtype) ∧ (∀ (R : Type) [CommRing R] (φ : Γ(Y.X, V.1) →+* R), IsFrame Y.t (φ.comp α) (spMap φ ≫ V.2.fromSpec) (e.bc φ)) ∧ ∀ w, IsTanAtG Y.t V.2.fromSpec w → ∃! a : Fin n → Γ(Y.X, V.1), IsCombAtG Y.t V.2.fromSpec (fun i => e (en i).1 (en i).2) a w := by
  first | exact @GlobalTheory.FlagEmb.EigSpread.exists_stable_eigFrame | exact GlobalTheory.FlagEmb.EigSpread.exists_stable_eigFrame | (intros; apply GlobalTheory.FlagEmb.EigSpread.exists_stable_eigFrame <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem LeftInv.change {S : Type} [CommRing S] {M n m : ℕ} {D C : Fin m → Fin M → S} (h : LeftInv D C)
    {U : Fin n → Fin M → S} (a : Fin m → Fin n → S) (b : Fin n → Fin m → S) (hU : ∀ z, U z = ∑ j, b z j • C j)
    (hab : ∀ z z', ∑ j, a j z * b z' j = if z = z' then 1 else 0) :
    LeftInv (fun z => ∑ j, a j z • D j) U := by
  intro z z'
  have e : ∑ r, (∑ j, a j z • D j) r * U z' r = ∑ j, ∑ j', a j z * b z' j' * ∑ r, D j r * C j' r := by
    simp only [hU z', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun r _ => by ring
  have h' : ∀ j j', ∑ r, D j r * C j' r = if j = j' then 1 else 0 := fun j j' => by convert h j j'
  rw [e]
  simp only [h', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  convert hab z z'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {L : FinLB X} {aff : ∀ i, IsAffineOpen (L.U i)} {M : ℕ} {crd : Crd t L M}

theorem IsLieEmb.exists_leftInv (h : IsLieEmb t L aff crd) (i : Fin L.n) {R : Type} [CommRing R]
    (φ : Γ(X, L.U i) →+* R) {x : Sp R ⟶ X} (hx : spMap φ ≫ (aff i).fromSpec = x) {n : ℕ} {u : Fin n → Tn t R}
    (hu : ∀ j, IsTanAtG t x (u j)) (hb : ∀ w, IsTanAtG t x w → ∃! a : Fin n → R, IsCombAtG t x u a w) :
    ∃ D : Fin n → Fin (M + 1) → R, LeftInv D fun z => crd i R φ (u z) := by
  obtain ⟨m, v, D, ⟨hv, hs⟩, hD⟩ := h.split i
  have hv' : ∀ j, IsTanAtG t x (spMap (dualMap φ) ≫ v j) := fun j => hx ▸ GlobalTheory.FactorDepth.isTanAtG_map t φ (hv j)
  have hC : ∀ j, crd i R φ (spMap (dualMap φ) ≫ v j) = φ ∘ crd i _ (RingHom.id _) (v j) := fun j =>
    h.nat i _ R (RingHom.id _) φ (v j) (by simpa [spMap] using hv j)
  choose a ha using fun j => (hb _ (hv' j)).exists
  choose b hb' using fun z => (hs R φ (u z) (hx ▸ hu z)).exists
  have ha' := fun j => (h.comb_iff i φ hx hu (hv' j) _).1 (ha j)
  have hb'' := fun z => (h.comb_iff i φ hx hv' (hu z) _).1 (hx ▸ hb' z)
  refine ⟨_, (hD.map φ).change a b (fun z => by simpa only [hC] using hb'' z) fun z z' => ?_⟩
  have e := (hb _ (hu z')).unique ((h.comb_iff i φ hx hu (hu z') fun z => ∑ j, a j z * b z' j).2 ?_)
    ((h.comb_iff i φ hx hu (hu z') fun z => if z = z' then 1 else 0).2 (by simp))
  · exact congrFun e z
  · rw [hb'' z']
    simp only [ha', Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem IsLieEmb.exists_leftInv_let (h : IsLieEmb t L aff crd) (i : Fin L.n) {R : Type} [CommRing R]
    (φ : Γ(X, L.U i) →+* R) {x : Sp R ⟶ X} (hx : spMap φ ≫ (aff i).fromSpec = x) {Dw : Datum H} {e : Vecs Dw t R}
    {n : ℕ} (en : Fin n ≃ Let Dw.mult) (hu : ∀ τ j, IsTanAtG t x (e τ j))
    (hb : ∀ w, IsTanAtG t x w → ∃! a : Fin n → R, IsCombAtG t x (fun i => e (en i).1 (en i).2) a w) :
    ∃ D : Let Dw.mult → Fin (M + 1) → R, LeftInv D fun z => crd i R φ (e z.1 z.2) := by
  obtain ⟨D, hD⟩ := h.exists_leftInv i φ hx (fun i => hu (en i).1 (en i).2) hb
  refine ⟨fun z => D (en.symm z), fun z z' => ?_⟩
  obtain ⟨y, rfl⟩ := en.surjective z
  obtain ⟨y', rfl⟩ := en.surjective z'
  have := hD y y'
  simp only [Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  convert this

theorem tan_of_frame {Dw : Datum H} {l : Level H} {c : Coeff l} {R : Type} [CommRing R] {α : c.F →+* R} {x : Sp R ⟶ X}
    {e : Vecs Dw t R} (he : GlobalTheory.LocM.IsFrame t ((RingHom.id R).comp α) (spMap (RingHom.id R) ≫ x) (e.bc (RingHom.id R))) (τ) (j) :
    IsTanAtG t x (e τ j) := by
  have h1 : dualMap (RingHom.id R) = RingHom.id _ := RingHom.ext fun y => TrivSqZeroExt.inl_fst_add_inr_snd_eq y
  simpa [Vecs.bc, h1, spMap] using (he.1 τ j).1

theorem IsLieEmb.inBlock (h : IsLieEmb t L aff crd) {Dw : Datum H} {l : Level H} {c : Coeff l} {k : Type} [Field k]
    {R R' : Type} [CommRing R] [CommRing R'] {i i' : Fin L.n} (ρ : Γ(X, L.U i) →+* R) (ρ' : Γ(X, L.U i') →+* R')
    {x : Sp R ⟶ X} {x' : Sp R' ⟶ X} (hx : spMap ρ ≫ (aff i).fromSpec = x) (hx' : spMap ρ' ≫ (aff i').fromSpec = x')
    {e : Vecs Dw t R} {e' : Vecs Dw t R'} (ht : ∀ τ j, IsTanAtG t x (e τ j)) (ht' : ∀ τ j, IsTanAtG t x' (e' τ j))
    (φ : R →+* k) (φ' : R' →+* k) (hφ : spMap φ ≫ x = spMap φ' ≫ x') {α : c.F →+* k}
    (he : GlobalTheory.LocM.IsFrame t α (spMap φ ≫ x) (e.bc φ)) (he' : GlobalTheory.LocM.IsFrame t α (spMap φ' ≫ x') (e'.bc φ')) :
    InBlock (m := Dw.mult) (fun z => φ ∘ crd i R ρ (e z.1 z.2)) (fun z => φ' ∘ crd i' R' ρ' (e' z.1 z.2)) := by
  rintro ⟨τ, j⟩
  subst hx hx'
  have e1 : spMap (φ.comp ρ) ≫ (aff i).fromSpec = spMap φ ≫ spMap ρ ≫ (aff i).fromSpec := by
    rw [spMap_comp, Category.assoc]
  have e2 : spMap (φ'.comp ρ') ≫ (aff i').fromSpec = spMap φ' ≫ spMap ρ' ≫ (aff i').fromSpec := by
    rw [spMap_comp, Category.assoc]
  have hw := (he'.1 τ j).1
  obtain ⟨a, ha, -⟩ := he.2 τ (e'.bc φ' τ j) (hφ ▸ hw) (he'.1 τ j).2
  have h1 := (h.comb_iff i (φ.comp ρ) e1 (fun j => (he.1 τ j).1) (hφ ▸ hw) a).1 ha
  have h2 := h.trans i' i k (φ'.comp ρ') (φ.comp ρ) (e'.bc φ' τ j) (by rw [e1, e2, hφ]) (e2 ▸ hw)
  have h3 := h.nat i' R' k ρ' φ' (e' τ j) (ht' τ j)
  have h4 := fun j => h.nat i R k ρ φ (e τ j) (ht τ j)
  show φ' ∘ crd i' R' ρ' (e' τ j) ∈ _
  rw [← h3]
  refine h2 ▸ Submodule.smul_mem _ _ ?_
  rw [h1]
  exact Submodule.sum_mem _ fun j' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j', (h4 j').symm⟩)

theorem noetherianSpace_model {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ}
    {W : ValuationSubring ℂ} (Y : Model Xo c (c.V W).subtype) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    TopologicalSpace.NoetherianSpace Y.X := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsDiscreteValuationRing (c.V W) := by
    refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp.ne_zero ?_).1
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    rcases hW with h | h
    · exact absurd (by exact_mod_cast h) hp.ne_zero
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  have := projProper _ _ _ Y.proj
  have := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : AlgebraicGeometry.IsNoetherian Y.X := {}
  infer_instance

theorem exists_isFrameCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (L : FinLB Y.X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd Y.t L M), IsLieEmb Y.t L aff crd → ∃ (n : ℕ) (V : Fin n → Y.X.affineOpens) (ι : Fin n → Fin L.n) (ρ : ∀ b, Γ(Y.X, L.U (ι b)) →+* Γ(Y.X, (V b).1)) (α : ∀ b, c.F →+* Γ(Y.X, (V b).1)) (e : ∀ b, Vecs Dw Y.t Γ(Y.X, (V b).1)) (D : ∀ b, Let Dw.mult → Fin (M + 1) → Γ(Y.X, (V b).1)), IsFrameCover Y L aff crd V ι ρ α e D := by
  intro E _ _ _ H Dw l Xo c p W Y hp hW L aff M crd h
  have := noetherianSpace_model Y hp hW
  obtain ⟨-, hloc⟩ := GlobalTheory.T.exists_affine_eigenframe_near_image E H Dw l Xo c p W Y hp hW
  have hcov : ∀ x : Y.X, ∃ i, x ∈ L.U i := fun x =>
    TopologicalSpace.Opens.mem_iSup.1 ((L.isLB.cover).symm ▸ (TopologicalSpace.Opens.mem_top x))
  choose ι hι using hcov
  choose V α e n en hxV hVU hVj hs hfr hbas using fun x : Set.range Y.j => hloc x.1 (L.U (ι x.1)) (hι x.1) x.2
  obtain ⟨T, hT⟩ := (TopologicalSpace.NoetherianSpace.isCompact (Set.range Y.j)).elim_finite_subcover
    (fun x => ((V x).1 : Set Y.X)) (fun x => (V x).1.2) fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV _⟩
  have hρ : ∀ x, ∃ ρ : Γ(Y.X, L.U (ι x.1)) →+* Γ(Y.X, (V x).1),
      spMap ρ ≫ (aff (ι x.1)).fromSpec = (V x).2.fromSpec := fun x =>
    ⟨(Y.X.presheaf.map (homOfLE (hVU x)).op).hom, (aff (ι x.1)).map_fromSpec (V x).2 _⟩
  choose ρ hρ using hρ
  have htan : ∀ x τ j, IsTanAtG Y.t (V x).2.fromSpec (e x τ j) := fun x => tan_of_frame (hfr x _ (RingHom.id _))
  have hD : ∀ x, ∃ D : Let Dw.mult → Fin (M + 1) → Γ(Y.X, (V x).1),
      LeftInv D fun z => crd (ι x.1) _ (ρ x) (e x z.1 z.2) := fun x =>
    h.exists_leftInv_let (ι x.1) (ρ x) (hρ x) (en x) (htan x) (hbas x)
  choose D hD using hD
  obtain ⟨f, hf⟩ : ∃ f : Fin T.card → Set.range Y.j, ∀ x ∈ T, ∃ b, f b = x :=
    ⟨fun b => (T.equivFin.symm b).1, fun x hx => ⟨T.equivFin ⟨x, hx⟩, by simp⟩⟩
  refine ⟨T.card, fun b => V (f b), fun b => ι (f b).1, fun b => ρ (f b), fun b => α (f b), fun b => e (f b),
    fun b => D (f b), ?_, fun b => hρ _, fun b => hfr _, fun b => hs _, fun b => hD _,
    fun k _ b b' φ φ' hφ => ?_⟩
  · refine (Set.iUnion_subset fun b => hVj _).antisymm fun y hy => ?_
    obtain ⟨x, hx, hy'⟩ := Set.mem_iUnion₂.1 (hT hy)
    obtain ⟨b, rfl⟩ := hf x hx
    exact Set.mem_iUnion.2 ⟨b, hy'⟩
  · have hα : φ.comp (α (f b)) = φ'.comp (α (f b')) := by
      have e1 : spMap (φ.comp ((α (f b)).comp (c.V W).subtype)) =
          spMap (φ'.comp ((α (f b')).comp (c.V W).subtype)) := by
        rw [spMap_comp _ φ, spMap_comp _ φ', ← hs, ← hs, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ Y.s) hφ
      have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
      exact IsLocalization.ringHom_ext (nonZeroDivisors (c.V W)) e2
    exact h.inBlock (ρ _) (ρ _) (hρ _) (hρ _) (htan _) (htan _) φ φ' hφ (hfr _ k φ) (hα ▸ hfr _ k φ')

end GlobalTheory.FlagEmb
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_refinement_lie_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (L : FinLB Y.X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd Y.t L M), IsLieEmb Y.t L aff crd → ∃ (n : ℕ) (V : Fin n → Y.X.affineOpens) (ι : Fin n → Fin L.n) (ρ : ∀ b, Γ(Y.X, L.U (ι b)) →+* Γ(Y.X, (V b).1)) (α : ∀ b, c.F →+* Γ(Y.X, (V b).1)) (e : ∀ b, Vecs Dw Y.t Γ(Y.X, (V b).1)) (D : ∀ b, Let Dw.mult → Fin (M + 1) → Γ(Y.X, (V b).1)), IsFrameCover Y L aff crd V ι ρ α e D := by
  atlas_forward_decl GlobalTheory.FlagEmb.exists_isFrameCover
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_combination_eigen_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X), (∀ (n : ℕ) (u : Fin n → Tn t R) (cf : Fin n → R) (w : Tn t R) (a : 𝓞 E) (r : R), (∀ j, IsTanAtG t x (u j) ∧ u j ≫ (t.act.act a).left = spMap (epsMul r) ≫ u j) → IsCombAtG t x u cf w → w ≫ (t.act.act a).left = spMap (epsMul r) ≫ w) ∧ ∀ (f : c.F →+* R) (e u : Vecs Dw t R) (w : Pm Dw.mult) (y : CellVar Dw.mult → R), IsFrame t f x e → (∀ τ j, IsCombAtG t x (fun i => e τ (w τ i)) (fun i => cell y τ i j) (u τ j)) → IsFrame t f x u := by
  first | exact @GlobalTheory.FlagEmb.eig_comb_and_frame_cell | exact GlobalTheory.FlagEmb.eig_comb_and_frame_cell | (intros; apply GlobalTheory.FlagEmb.eig_comb_and_frame_cell <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.Proof.exists_descending_letter_chain

theorem down_prefix {T : Type} {m : T → ℕ} {n : ℕ} {u : Fin n → Let m} (hi : Function.Injective u)
    (h : ∀ (l : Fin n) (j : Fin (m (u l).1)), j < (u l).2 → ∃ l' ≤ l, u l' = ⟨(u l).1, j⟩) {k : ℕ} (hk : k ≤ n) :
    Down (u ∘ Fin.castLE hk) := by
  refine ⟨hi.comp (Fin.castLE_injective hk), fun l j hj => ?_⟩
  obtain ⟨l', hl, e⟩ := h (Fin.castLE hk l) j hj
  exact ⟨⟨l'.1, lt_of_le_of_lt (Fin.le_def.1 hl) l.2⟩, e⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem pairwise_letters : (letters Dw).Pairwise fun a b => a.1 = b.1 → (a.2 : ℕ) ≤ (b.2 : ℕ) := by
  refine List.pairwise_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ (List.pairwise_le_finRange _)
    exact fun h _ => Fin.le_def.1 h
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab x hx y hy h => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, rfl⟩ := List.mem_map.1 hy
    exact absurd ((Fintype.equivFin (E →+* ℂ)).symm.injective h) hab

theorem earlier (l : Fin (letters Dw).length) (j : Fin (Dw.mult ((letters Dw).get l).1))
    (hj : j < ((letters Dw).get l).2) : ∃ l' ≤ l, (letters Dw).get l' = ⟨((letters Dw).get l).1, j⟩ := by
  obtain ⟨l', e⟩ := List.get_of_mem (GlobalTheory.Proof.LetterConjugation.mem_letters Dw ⟨((letters Dw).get l).1, j⟩)
  refine ⟨l', not_lt.1 fun hl => ?_, e⟩
  have h := List.pairwise_iff_get.1 (pairwise_letters Dw) l l' hl
  rw [e] at h
  exact absurd (h rfl) (not_le.2 hj)

theorem step_position : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw), letterOf Dw st = some x → ∃ (n : ℕ) (u : Fin n → Let Dw.mult) (k : Fin n), Down u ∧ Down (u ∘ Fin.castLE k.2.le) ∧ Down (u ∘ Fin.castLE (Nat.succ_le_of_lt k.2)) ∧ u k = x ∧ ∀ (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (y : Sp C ⟶ X) (fr : Vecs Dw t C) (p : ℕ), lnStep t y fr p false st = Real.log (grNorm t y (latDR t y) (fun i => fr (u i).1 (u i).2) k) := by
  intro E _ _ _ H Dw st x hx
  rcases st with ⟨τ, k⟩ | k
  · by_cases h : k < Dw.mult τ
    · simp only [letterOf, dif_pos h, Option.some.injEq] at hx
      have hi : Function.Injective fun i : Fin (Dw.mult τ) => (⟨τ, i⟩ : Let Dw.mult) :=
        fun i i' h => eq_of_heq (Sigma.mk.inj h).2
      have hd : ∀ (l : Fin (Dw.mult τ)) (j : Fin (Dw.mult τ)), j < l →
          ∃ l' ≤ l, (⟨τ, l'⟩ : Let Dw.mult) = ⟨τ, j⟩ := fun l j hj => ⟨j, hj.le, rfl⟩
      refine ⟨Dw.mult τ, fun i => ⟨τ, i⟩, ⟨k, h⟩, down_prefix hi hd le_rfl, down_prefix hi hd _, down_prefix hi hd _, hx,
        fun X t C _ _ y fr p => ?_⟩
      simp [lnStep, h, lat]
    · simp [letterOf, h] at hx
  · obtain ⟨h, hx⟩ := List.getElem?_eq_some_iff.1 (show (letters Dw)[k]? = some x from hx)
    have hi : Function.Injective (letters Dw).get := List.nodup_iff_injective_get.1 (GlobalTheory.Proof.LetterConjugation.nodup_letters Dw)
    refine ⟨_, (letters Dw).get, ⟨k, h⟩, down_prefix hi (earlier Dw) le_rfl, down_prefix hi (earlier Dw) _,
      down_prefix hi (earlier Dw) _, hx, fun X t C _ _ y fr p => ?_⟩
    simp only [lnStep, dif_pos h, lat]

end GlobalTheory.Proof.exists_descending_letter_chain
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descending_letter_chain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw), letterOf Dw st = some x → ∃ (n : ℕ) (u : Fin n → Let Dw.mult) (k : Fin n), Down u ∧ Down (u ∘ Fin.castLE k.2.le) ∧ Down (u ∘ Fin.castLE (Nat.succ_le_of_lt k.2)) ∧ u k = x ∧ ∀ (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (y : Sp C ⟶ X) (fr : Vecs Dw t C) (p : ℕ), lnStep t y fr p false st = Real.log (grNorm t y (latDR t y) (fun i => fr (u i).1 (u i).2) k) := by
  first | exact @GlobalTheory.Proof.exists_descending_letter_chain.step_position | exact GlobalTheory.Proof.exists_descending_letter_chain.step_position | (intros; apply GlobalTheory.Proof.exists_descending_letter_chain.step_position <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.NormClosure

theorem isLocalization_away {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  refine IsLocalization.Away.mk _ (IsUnit.mk0 _ (by simpa using hϖ.ne_zero)) (fun z => ?_) fun a b h =>
    ⟨0, by rw [IsFractionRing.injective O K h]⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, a * ↑u⁻¹, ?_⟩
  have h1 : algebraMap O K ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have h2 : algebraMap O K u ≠ 0 := by simp
  have h3 : algebraMap O K ↑u⁻¹ = (algebraMap O K u)⁻¹ := by simp
  rw [map_mul, map_mul, map_pow, h3]
  field_simp

theorem exists_normal_closure : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field K] [Algebra O K] [IsFractionRing O K] (P F : Scheme.{0}) (sP : P ⟶ Sp O) (f : F ⟶ P), IsProjOver sP → IsImmersion f → CompactSpace F → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme F → Set.range (f ≫ sP) ⊆ Set.range (spMap (algebraMap O K)) → ∃ (n : ℕ) (I : (PSpace O n).IdealSheafData) (ν : I.subscheme ⟶ P) (j : F ⟶ I.subscheme), ν ≫ sP = I.subschemeι ≫ PSpace.str O n ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme I.subscheme ∧ Flat (ν ≫ sP) ∧ IsOpenImmersion j ∧ j ≫ ν = f ∧ Dense (Set.range j) := by
  intro O K _ _ _ _ _ _ _ P F sP f hP hf hF hn hr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := isLocalization_away (K := K) hϖ
  have : IsOpenImmersion (spMap (algebraMap O K)) := IsOpenImmersion.of_isLocalization ϖ
  let q : F ⟶ Sp K := IsOpenImmersion.lift (spMap (algebraMap O K)) (f ≫ sP) hr
  have hq : q ≫ spMap (algebraMap O K) = f ≫ sP := IsOpenImmersion.lift_fac _ _ _
  have : IsProper sP := by
    obtain ⟨N, i, hi, rfl⟩ := hP
    infer_instance
  have : LocallyOfFiniteType (q ≫ spMap (algebraMap O K)) := by rw [hq]; infer_instance
  have : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q (spMap (algebraMap O K))
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian F := {}
  have : QuasiCompact f := inferInstance
  have : GlobalTheory.IsNormalScheme F := .of_pred hn
  have hfin : IsFinite f.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of O) f sP K q hq.symm
  have hfl : Flat (f.fromNormalization ≫ sP) := GlobalTheory.flat_fromNormalization_comp f K sP q hq.symm
  obtain ⟨n, e, he, hes⟩ := GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hP
  have hN : GlobalTheory.IsNormalScheme e.image := .of_isIso e.toImage
  refine ⟨n, e.ker, inv e.toImage ≫ f.fromNormalization, f.toNormalization ≫ e.toImage, ?_,
    GlobalTheory.IsNormalScheme.pred e.image, ?_, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hes, IsIso.inv_comp_eq, ← Category.assoc]
    exact congrArg (· ≫ _) e.toImage_imageι.symm
  · rw [Category.assoc]; infer_instance
  · simp
  · exact (f.toNormalization ≫ e.toImage).denseRange

end GlobalTheory.NormClosure
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagModel

theorem exists_flagModel : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field K] [Algebra O K] [IsFractionRing O K] (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (algebraMap O K) s V α c D → ∃ (n : ℕ) (I : (PSpace O n).IdealSheafData) (π : I.subscheme ⟶ X) (g : ∀ en : En m, I.subscheme ⟶ PSpace O (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ I.subscheme)), π ≫ s = I.subschemeι ≫ PSpace.str O n ∧ IsFlagModel (algebraMap O K) s V α c π g κ := by
  intro O K _ _ _ _ _ _ _ X s T _ m M B _ V α c D hP hN hC
  obtain ⟨P, p0, p, h, hPlk⟩ := GlobalTheory.T.exists_pluckerFlagEmbedding_of_projective_base O K _ X s T m M B V α c D hP hC
  obtain ⟨F, f, i, hf, hi, hif, hcov⟩ := GlobalTheory.T.flagCells_glue_locallyClosed_pluckerProduct O K _ X s T m M B V α c D P p0 p h hP hN hC hPlk
  have hXn : IsLocallyNoetherian X := by
    obtain ⟨N, ι, _, rfl⟩ := hP
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str O N)
  obtain ⟨hFc, hFn, hFnoe⟩ := GlobalTheory.T.compact_normal_noetherian_of_flagCell_cover X T m B V F i hN hi hcov
  have hbase : ∀ b w, i b w ≫ f ≫ p0 ≫ s = spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp ((α b).comp (algebraMap O K))) := by
    intro b w
    rw [← Category.assoc, hif, ← Category.assoc, hPlk.base, cbase, Category.assoc, hC.ovr, ← Spec.map_comp]
    rfl
  have hrange : Set.range (f ≫ (p0 ≫ s)) ⊆ Set.range (spMap (algebraMap O K)) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨b, w, y, rfl⟩ := hcov x
    refine ⟨spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp (α b)) y, ?_⟩
    have e := congrArg (fun φ => φ y) (hbase b w)
    have e2 : spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp ((α b).comp (algebraMap O K))) =
        spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp (α b)) ≫ spMap (algebraMap O K) := by rw [← Spec.map_comp]; rfl
    rw [e2] at e
    simp only [Scheme.Hom.comp_apply] at e ⊢
    exact e.symm
  obtain ⟨n, I, ν, j, hν, hIn, hIf, hj, hjν, hdense⟩ :=
    GlobalTheory.NormClosure.exists_normal_closure O K P F (p0 ≫ s) f hPlk.proj hf hFc hFn hrange
  have hsep : IsSeparated (ν ≫ p0) := by
    have : IsProper (PSpace.str O n) := isProper_str O n
    have : IsProper ((ν ≫ p0) ≫ s) := by rw [Category.assoc, hν]; infer_instance
    exact IsSeparated.of_comp (ν ≫ p0) s
  have hcover := GlobalTheory.T.preimage_iUnion_opens_eq_range_flagCells O K _ X s T m M B V α c D P p0 p h hC hPlk F I.subscheme f i j ν hf hi hif
    hcov hj hjν hdense hFnoe hsep
  refine ⟨n, I, ν ≫ p0, fun en => ν ≫ p en, fun b w => i b w ≫ j, by rw [Category.assoc, hν], ?_⟩
  have hflat : Flat ((ν ≫ p0) ≫ s) := by rw [Category.assoc]; exact hIf
  have hdense' : Dense ((ν ≫ p0) ⁻¹' ⋃ b, ((V b).1 : Set X)) := by rw [hcover]; exact hdense
  refine ⟨⟨?_, ?_⟩, hIn, hflat, ?_, ?_, hdense', ?_⟩
  · intro b w
    rw [Category.assoc, ← Category.assoc j, hjν, ← Category.assoc, hif, hPlk.base]
  · intro b w en
    obtain ⟨hu, e⟩ := hPlk.plk b w en
    exact ⟨hu, by rw [Category.assoc, ← Category.assoc j, hjν, ← Category.assoc, hif, e]⟩
  · intro b w
    have := hi b w
    infer_instance
  · rw [hcover]
    ext z
    simp only [Set.mem_iUnion, Set.mem_range, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨b, w, y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨b, w, y, rfl⟩ := hcov x
      exact ⟨b, w, y, rfl⟩
  · intro k _ z z' hz e1 e2
    have hr : ∀ y, (ν ≫ p0) (z y) ∈ ⋃ b, ((V b).1 : Set X) := fun y =>
      hz ⟨y, (Scheme.Hom.comp_apply _ _ _)⟩
    have hz1 : Set.range z ⊆ Set.range j := by
      rintro _ ⟨y, rfl⟩
      rw [← hcover]
      exact hr y
    have hz2 : Set.range z' ⊆ Set.range j := by
      rintro _ ⟨y, rfl⟩
      rw [← hcover]
      have e := congrArg (fun φ => φ y) e1
      simp only [Scheme.Hom.comp_apply] at e
      show (ν ≫ p0) (z' y) ∈ ⋃ b, ((V b).1 : Set X)
      simp only [Scheme.Hom.comp_apply] at hr ⊢
      rw [← e]
      exact hr y
    let z₀ := IsOpenImmersion.lift j z hz1
    let z₀' := IsOpenImmersion.lift j z' hz2
    have f₀ : z₀ ≫ j = z := IsOpenImmersion.lift_fac _ _ _
    have f₀' : z₀' ≫ j = z' := IsOpenImmersion.lift_fac _ _ _
    have key : z₀ ≫ f = z₀' ≫ f := by
      refine hPlk.ext _ _ _ ?_ fun en => ?_
      · rw [← hjν, ← Category.assoc, ← Category.assoc, f₀, f₀', Category.assoc, Category.assoc]
        exact e1
      · rw [← hjν, ← Category.assoc, ← Category.assoc, f₀, f₀', Category.assoc, Category.assoc]
        exact e2 en
    have := hf
    rw [← f₀, ← f₀', (cancel_mono f).1 key]

end GlobalTheory.FlagModel
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCover_normal_projective_charts : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field K] [Algebra O K] [IsFractionRing O K] (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (algebraMap O K) s V α c D → ∃ (n : ℕ) (I : (PSpace O n).IdealSheafData) (π : I.subscheme ⟶ X) (g : ∀ en : En m, I.subscheme ⟶ PSpace O (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ I.subscheme)), π ≫ s = I.subschemeι ≫ PSpace.str O n ∧ IsFlagModel (algebraMap O K) s V α c π g κ := by
  atlas_forward_decl GlobalTheory.FlagModel.exists_flagModel
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem tri_diag_ne_zero : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (ι : Type) (c c' : Let m → ι → K)
    (d : Let m → K), (∀ τ, LinearIndependent K fun j : Fin (m τ) => c' ⟨τ, j⟩) → Tri c c' d → ∀ z, d z ≠ 0 := by
  classical
  intro T m K _ ι c c' d hli htri z hz
  obtain ⟨τ, i⟩ := z
  set f : Fin (m τ) → ι → K := fun j => c ⟨τ, j⟩ with hf
  let w : Finset (ι → K) := (Finset.Iio i).image f
  have hsub : ∀ j : Fin (m τ), j ≤ i → c' ⟨τ, j⟩ ∈ Submodule.span K (w : Set (ι → K)) := by
    have hspan : ∀ j : Fin (m τ), j ≤ i →
        Submodule.span K (f '' {j' | j' < j}) ≤ Submodule.span K (w : Set (ι → K)) := by
      intro j hj
      refine Submodule.span_mono ?_
      rintro _ ⟨j', hj', rfl⟩
      simp only [w, Finset.coe_image, Finset.coe_Iio]
      exact ⟨j', lt_of_lt_of_le hj' hj, rfl⟩
    intro j hj
    have ht := htri ⟨τ, j⟩
    rcases lt_or_eq_of_le hj with hlt | heq
    · have h1 : c' ⟨τ, j⟩ - d ⟨τ, j⟩ • c ⟨τ, j⟩ ∈ Submodule.span K (w : Set (ι → K)) := hspan j hj ht
      have h2 : c ⟨τ, j⟩ ∈ Submodule.span K (w : Set (ι → K)) := by
        refine Submodule.subset_span ?_
        simp only [w, Finset.coe_image, Finset.coe_Iio]
        exact ⟨j, hlt, rfl⟩
      have := Submodule.add_mem _ h1 (Submodule.smul_mem _ (d ⟨τ, j⟩) h2)
      simpa using this
    · subst heq
      have h1 := hspan j le_rfl ht
      simpa [hz] using h1
  let v : (Finset.Iic i) → ι → K := fun j => c' ⟨τ, j.1⟩
  have hv : LinearIndependent K v := (hli τ).comp (fun j : Finset.Iic i => j.1) Subtype.val_injective
  have hle := linearIndependent_le_span_aux' v hv (w : Set (ι → K)) (by
    rintro _ ⟨j, rfl⟩
    exact hsub j.1 (Finset.mem_Iic.1 j.2))
  have hw : Fintype.card (w : Set (ι → K)) ≤ (i : ℕ) := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    exact (Finset.card_image_le).trans (by simp)
  have hv' : Fintype.card (Finset.Iic i) = (i : ℕ) + 1 := by
    rw [Fintype.card_coe]; simp
  omega

end GlobalTheory.FlagEmb
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diag_ne_zero_of_triangular_independent : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (ι : Type) (c c' : Let m → ι → K) (d : Let m → K), (∀ τ, LinearIndependent K fun j : Fin (m τ) => c' ⟨τ, j⟩) → Tri c c' d → ∀ z, d z ≠ 0 := by
  atlas_forward_decl GlobalTheory.FlagEmb.tri_diag_ne_zero
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Uniq

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem pt_congr {R A : Type} [CommRing R] [CommRing A] {N : ℕ} {c c' : R →+* A} (h : c = c') (v : Fin (N + 1) → A)
    (hv hv' : Ideal.span (Set.range v) = ⊤) : pt c v hv = pt c' v hv' := by
  subst h
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Pre Y i₀} {L : FinLB (Y Z.i).X} {aff : ∀ i, IsAffineOpen (L.U i)} {M : ℕ} {crd : Crd (Y Z.i).t L M}
  {ι : Fin Z.m → Fin L.n} {ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)}
  {g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)}

theorem plk_adapted (h : Comparison₂ Z L aff crd ι ρ g) {k : Type} [Field k] (a : Fin Z.m) (i : Fin L.n)
    (φ : Γ(Z.X, (Z.U a).1) →+* k) (ψ : Γ((Y Z.i).X, L.U i) →+* k) (u : Vecs Dw (Y Z.i).t k)
    (hψ : spMap ψ ≫ (aff i).fromSpec = (spMap φ ≫ Z.chart a) ≫ Z.π)
    (hf : IsFrame (Y Z.i).t (φ.comp (Z.alg a)) ((spMap φ ≫ Z.chart a) ≫ Z.π) u)
    (hs : SameFlag Z.ty (Y Z.i).t ((spMap φ ≫ Z.chart a) ≫ Z.π) ((Z.fr a).bc φ) u) (en : En Dw.mult) :
    ∃ hu, (spMap φ ≫ Z.chart a) ≫ g en = pt (φ.comp ((Z.alg a).comp (Z.i.c.V W).subtype))
      (plk (fun z : Let Dw.mult => crd i k ψ (u z.1 z.2)) en.2.1) hu := by
  rw [Category.assoc] at hψ hf hs
  rw [h.ty] at hs
  obtain ⟨hu, e⟩ := GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g h k a i φ ψ hψ en
  have hfr := h.frame a k φ
  obtain ⟨d, hd⟩ := (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd h.emb i k ψ _ _ _ _ _ hψ hfr hf).1.1 hs
  have hli := (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd h.emb i k ψ _ _ _ _ _ hψ hf hf).2.1
  have hne := GlobalTheory.T.diag_ne_zero_of_triangular_independent _ _ k _ _ _ d hli hd
  have hp := GlobalTheory.FlagEmb.plk_tri _ _ k M _ _ d _ _ hd en.2.2
  have h0 : (∏ l, d (en.2.1 l)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hne _
  have hp' : plk (fun z : Let Dw.mult => crd i k ψ (u z.1 z.2)) en.2.1 = Units.mk0 _ h0 • _ := hp
  refine ⟨hp' ▸ span_range_units_smul hu _, ?_⟩
  rw [Category.assoc, e]
  exact (pt_eq_pt_iff _ _ _).2 ⟨_, hp'⟩

theorem spMap_alg (h : Comparison₂ Z L aff crd ι ρ g) {k : Type} [Field k] (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k) :
    spMap (φ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) = ((spMap φ ≫ Z.chart a) ≫ Z.π) ≫ (Y Z.i).s := by
  rw [spMap_comp_eq, ← h.alg_s a]
  simp only [Category.assoc]

end GlobalTheory.FlagEmb.Uniq

namespace GlobalTheory.FlagEmb

open Uniq in

theorem flagAt_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] (w w' : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k), w ≫ Z.π = w' ≫ Z.π → Z.FlagAt w u → Z.FlagAt w' u → w = w' := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g h k _ w w' u hπ ⟨a, φ, hw, hf, hs⟩ ⟨a', φ', hw', hf', hs'⟩
  subst hw hw'
  have hψ : spMap (φ.comp (ρ a)) ≫ (aff (ι a)).fromSpec = (spMap φ ≫ Z.chart a) ≫ Z.π := by
    rw [spMap_comp_eq, Category.assoc, h.res, Category.assoc]
  refine h.inj k _ _ ?_ hπ fun en => ?_
  · rintro _ ⟨y, rfl⟩
    rw [← h.cover]
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    rw [← (Z.U a).2.range_fromSpec]
    exact ⟨spMap φ y, by simp [Pre.chart]⟩
  · obtain ⟨hu, e⟩ := plk_adapted h a _ φ _ u hψ hf hs en
    obtain ⟨hu', e'⟩ := plk_adapted h a' _ φ' _ u (hψ.trans hπ) hf' hs' en
    rw [e, e']
    refine pt_congr (spMap_injective ?_) _ _ _
    rw [spMap_alg h, spMap_alg h, hπ]

end GlobalTheory.FlagEmb
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pre_model_chart_transition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] (w w' : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k), w ≫ Z.π = w' ≫ Z.π → Z.FlagAt w u → Z.FlagAt w' u → w = w' := by
  atlas_forward_decl GlobalTheory.FlagEmb.flagAt_unique
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pre_model_chart_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ en₀ en₁ : En Dw.mult, en₁.1 = en₀.1 + 1 → ∃ (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M en₀.1 + 1)) (q₁ : Fin L'.n → Fin (plN M en₁.1 + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g en₀ en₁ L' ix q₀ q₁ r := by
  first | exact @GlobalTheory.FlagEmb.QuotLine.exists_isLine | exact GlobalTheory.FlagEmb.QuotLine.exists_isLine | (intros; apply GlobalTheory.FlagEmb.QuotLine.exists_isLine <;> assumption)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.LChart

theorem diag_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V] {n : ℕ} (c : Fin n → V)
    (hc : LinearIndependent k c) (j : Fin n) (cf : Fin n → k) (d : k) (hcf : ∀ m, j < m → cf m = 0)
    (h : (∑ m, cf m • c m) - d • c j ∈ Submodule.span k (c '' {m | m < j})) : d = cf j := by
  have h1 : (∑ m, cf m • c m) - cf j • c j ∈ Submodule.span k (c '' {m | m < j}) := by
    rw [← Finset.sum_erase_eq_sub (Finset.mem_univ j)]
    refine Submodule.sum_mem _ fun m hm => ?_
    rcases lt_trichotomy m j with hlt | heq | hgt
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hlt, rfl⟩)
    · exact absurd heq (Finset.ne_of_mem_erase hm)
    · rw [hcf m hgt, zero_smul]
      exact Submodule.zero_mem _
  have h2 := Submodule.sub_mem _ h1 h
  rw [sub_sub_sub_cancel_left, ← sub_smul] at h2
  by_contra hne
  have h3 := (Submodule.smul_mem_iff _ (sub_ne_zero.2 hne)).1 h2
  exact hc.notMem_span_image (s := {m | m < j}) (x := j) (lt_irrefl j) h3

theorem exists_ringHom {k : Type} [Field k] {X : Scheme.{0}} (f : Sp k ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ f ⁻¹ᵁ U) : ∃ ψ : Γ(X, U) →+* k, spMap ψ ≫ hU.fromSpec = f := by
  have hr : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact h (Set.mem_univ x)
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hU.fromSpec f hr)).hom, ?_⟩
  have : spMap (Spec.preimage (IsOpenImmersion.lift hU.fromSpec f hr)).hom =
      IsOpenImmersion.lift hU.fromSpec f hr := Spec.map_preimage _
  rw [this, IsOpenImmersion.lift_fac]

theorem ne_zero_of_chart {R k : Type} [CommRing R] [Field k] {N : ℕ} (c : R →+* k) (v : Fin (N + 1) → k)
    (hv : Ideal.span (Set.range v) = ⊤) (i : Fin (N + 1)) (h : ⊤ ≤ pt c v hv ⁻¹ᵁ chart R N i) : v i ≠ 0 := by
  intro h0
  rw [pt_preimage_chart, h0] at h
  have h1 := h (Set.mem_univ (IsLocalRing.closedPoint k))
  exact h1 (Ideal.zero_mem _)

theorem gen_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (n : ℕ) (u : Fin n → Let Dw.mult) (kk : Fin n) (h₀ : Down (u ∘ Fin.castLE kk.2.le)) (h₁ : Down (u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2))) (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M kk + 1)) (q₁ : Fin L'.n → Fin (plN M (kk + 1) + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g ⟨kk, _, h₀⟩ ⟨kk + 1, _, h₁⟩ L' ix q₀ q₁ r → ∀ (k : Type) [Field k] a a' i (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k) (cf : Fin (Dw.mult (u kk).1) → k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' → ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ L'.U i → (∀ m, (u kk).2 < m → cf m = 0) → IsCombAtG (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ (u kk).1) cf ((Z.fr a').bc φ' (u kk).1 (u kk).2) → valF (spMap φ ≫ Z.chart a) _ (r a i).val = valF (spMap φ ≫ Z.chart a) _ (r a' i).val * cf (u kk).2 := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T n u kk h₀ h₁ L' ix q₀ q₁ r hL k _ a a' i φ φ' cf hφ hi hcf hcomb
  have hle := (spMap φ ≫ Z.chart a).preimage_mono (hL.le i)
  have hle1 := hi.trans hle
  have hU : ⊤ ≤ (spMap φ ≫ Z.chart a ≫ Z.π) ⁻¹ᵁ L.U (ix i) := fun x hx => (hle1 hx).1
  have hφπ : spMap φ ≫ Z.chart a ≫ Z.π = spMap φ' ≫ Z.chart a' ≫ Z.π := by
    rw [← Category.assoc, hφ, Category.assoc]
  obtain ⟨ψ, hψ⟩ := exists_ringHom _ (aff (ix i)) hU
  have fa := T.frame a k φ
  have fa' := T.frame a' k φ'
  rw [← hφπ] at fa'
  have sf := GlobalTheory.T.pre_model_chart_compatible E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a a' φ φ' hφ
  rw [T.ty] at sf
  obtain ⟨t1, t2, -⟩ := GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd T.emb (ix i) k ψ _ _ _ _ _ hψ fa fa'
  obtain ⟨d, hd⟩ := t1.1 sf
  have hc := (T.emb.comb_iff (ix i) ψ hψ (fun j => (fa.1 (u kk).1 j).1) (fa'.1 (u kk).1 (u kk).2).1 cf).1 hcomb
  have hdc : d (u kk) = cf (u kk).2 := by
    refine diag_eq _ (t2 (u kk).1) (u kk).2 cf _ hcf ?_
    have := hd (u kk)
    simp only [hc] at this
    exact this
  have P0 := congrFun (plk_tri _ _ _ _ _ _ d _ _ hd h₀) (q₀ i)
  have P1 := congrFun (plk_tri _ _ _ _ _ _ d _ _ hd h₁) (q₁ i)
  have v := hL.val k a i φ ψ hψ hi
  have v' := hL.val k a' i φ' ψ (hψ.trans hφπ) (hφ ▸ hi)
  obtain ⟨hu, hp⟩ := GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a' (ix i) φ' ψ (hψ.trans hφπ)
    ⟨kk + 1, _, h₁⟩
  have hne := ne_zero_of_chart _ _ hu (q₁ i) (by
    rw [← hp, ← Category.assoc, ← hφ]
    exact fun x hx => (hle1 hx).2.2)
  rw [← hφ] at v'
  have hprod : ∏ l : Fin (kk + 1), d ((u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2)) l) =
      (∏ l : Fin kk, d ((u ∘ Fin.castLE kk.2.le) l)) * d (u kk) := by
    rw [Fin.prod_univ_castSucc]
    rfl
  rw [hprod, hdc] at P1
  simp only [Pi.smul_apply, smul_eq_mul] at P0 P1
  dsimp only at v v' hne
  rw [P1] at hne
  rw [P0, P1, ← v] at v'
  have hD := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hP := right_ne_zero_of_mul hne
  apply mul_right_cancel₀ (mul_ne_zero hD hP)
  linear_combination -v'

end GlobalTheory.FlagEmb.LChart
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pre_model_chart_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (n : ℕ) (u : Fin n → Let Dw.mult) (kk : Fin n) (h₀ : Down (u ∘ Fin.castLE kk.2.le)) (h₁ : Down (u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2))) (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M kk + 1)) (q₁ : Fin L'.n → Fin (plN M (kk + 1) + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g ⟨kk, _, h₀⟩ ⟨kk + 1, _, h₁⟩ L' ix q₀ q₁ r → ∀ (k : Type) [Field k] a a' i (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k) (cf : Fin (Dw.mult (u kk).1) → k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' → ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ L'.U i → (∀ m, (u kk).2 < m → cf m = 0) → IsCombAtG (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ (u kk).1) cf ((Z.fr a').bc φ' (u kk).1 (u kk).2) → valF (spMap φ ≫ Z.chart a) _ (r a i).val = valF (spMap φ ≫ Z.chart a) _ (r a' i).val * cf (u kk).2 := by
  atlas_forward_decl GlobalTheory.FlagEmb.LChart.gen_change
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.LatDRCrd

theorem isDominant_spMap_of_injective {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (h : Function.Injective φ) : IsDominant (spMap φ) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot φ).1 h]; exact bot_le)⟩

theorem dualMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

theorem mem_latDR_iff_crd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [X.IsSeparated] (t : SAB H X) (L : FinLB X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd t L M), IsLieEmb t L aff crd → ∀ (i : Fin L.n) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (φ : Γ(X, L.U i) →+* ↥(intO C)) (x : Sp C ⟶ X) (w : Tn t C), spMap ((intO C).subtype.comp φ) ≫ (aff i).fromSpec = x → IsTanAtG t x w → (w ∈ latDR t x ↔ ∀ r, ‖crd i C ((intO C).subtype.comp φ) w r‖ ≤ 1) := by
  intro E _ _ _ H X _ t L aff M crd h i C _ _ φ x w hx hw
  have hx' : spMap (intO C).subtype ≫ (spMap φ ≫ (aff i).fromSpec) = x := by
    rw [← Category.assoc, spMap_comp', hx]
  constructor
  · rintro ⟨xO, hxO, vO, hv, rfl⟩ r
    have := isDominant_spMap_of_injective (intO C).subtype Subtype.val_injective
    obtain rfl : xO = spMap φ ≫ (aff i).fromSpec :=
      ext_of_isDominant (spMap (intO C).subtype) (hxO.trans hx'.symm)
    rw [h.nat i _ C φ (intO C).subtype vO hv]
    exact (crd i _ φ vO r).2
  · intro hr
    subst hx
    obtain ⟨n, v, D, ⟨hv, hb⟩, hD⟩ := h.split i
    obtain ⟨a, ha, -⟩ := hb C _ w hw
    have hvC := fun j => isTanAtG_map t ((intO C).subtype.comp φ) (hv j)
    have hvO := fun j => isTanAtG_map t φ (hv j)
    have h1 : spMap (RingHom.id Γ(X, L.U i)) = 𝟙 _ := Spec.map_id _
    have hc := h.comb i C _ n _ a w hvC ha
    have hn : ∀ j, crd i C ((intO C).subtype.comp φ) (spMap (dualMap ((intO C).subtype.comp φ)) ≫ v j) =
        ((intO C).subtype.comp φ) ∘ crd i _ (RingHom.id _) (v j) := fun j =>
      h.nat i _ C (RingHom.id _) ((intO C).subtype.comp φ) (v j) (by rw [h1, Category.id_comp]; exact hv j)
    have hD' := hD.map ((intO C).subtype.comp φ)
    have hmem : ∀ j, a j ∈ intO C := fun j => by
      have e : a j = ∑ r, ((intO C).subtype.comp φ) (D j r) * crd i C ((intO C).subtype.comp φ) w r := by
        rw [hc]
        simp only [hn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        have : ∀ j', ∑ r, ((intO C).subtype.comp φ) (D j r) *
            (a j' * (((intO C).subtype.comp φ) ∘ crd i _ (RingHom.id _) (v j')) r) =
            if j = j' then a j' else 0 := fun j' => by
          have e := hD' j j'
          simp only [mul_left_comm _ (a j'), ← Finset.mul_sum]
          refine (congrArg (a j' * ·) e).trans ?_
          split_ifs <;> simp
        simp only [this]
        simp
      rw [e]
      exact Subring.sum_mem _ fun r _ => Subring.mul_mem _ (φ (D j r)).2 (hr r)
    obtain ⟨wO, hwO, hcO⟩ := exists_comb t hvO fun j => (⟨a j, hmem j⟩ : ↥(intO C))
    refine ⟨_, hx', wO, hwO, ?_⟩
    have hb := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [← Category.assoc, spMap_comp', dualMap_comp'] at hb
    exact comb_unique t hvC hb ha

end GlobalTheory.LatDRCrd
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.LineNorm

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ β : A →+* B, f = spMap β :=
  ⟨(Spec.preimage f).hom, (Spec.map_preimage f).symm⟩

theorem exists_fromSpec {A : Type} [CommRing A] {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : Sp A ⟶ X)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ∃ φ : Γ(X, U) →+* A, spMap φ ≫ hU.fromSpec = x := by
  have hr : Set.range x ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact h (Set.mem_univ y)
  obtain ⟨φ, hφ⟩ := exists_spMap' (A := Γ(X, U)) (IsOpenImmersion.lift hU.fromSpec x hr)
  exact ⟨φ, hφ ▸ IsOpenImmersion.lift_fac _ _ hr⟩

theorem max_of_chart {R : Type} [CommRing R] {N : ℕ} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (f : Sp ↥(intO C) ⟶ PSpace R N) (q : Fin (N + 1)) (hq : ⊤ ≤ f ⁻¹ᵁ chart R N q) (c : R →+* C)
    (w : Fin (N + 1) → C) (hw : Ideal.span (Set.range w) = ⊤) (h : spMap (intO C).subtype ≫ f = pt c w hw) :
    (∀ q', ‖w q'‖ ≤ ‖w q‖) ∧ w q ≠ 0 := by
  have := GlobalTheory.LatDRFree.intO_isLocalRing C
  obtain ⟨b, hb⟩ := exists_spMap' (f ≫ PSpace.str R N)
  obtain ⟨v, hv, rfl⟩ := exists_eq_pt b f hb
  rw [pt_preimage_chart] at hq
  have hu : IsUnit (v q) := by
    have h1 : IsLocalRing.closedPoint ↥(intO C) ∈ spOpen (v q) := hq (Set.mem_univ _)
    by_contra hn
    exact mem_spOpen.1 h1 hn
  rw [GlobalTheory.ProjSpace.spMap_pt] at h
  have hc : (intO C).subtype.comp b = c := by
    have h1 := congrArg (· ≫ PSpace.str R N) h
    simp only [pt_str] at h1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hc
  obtain ⟨s, rfl⟩ := (pt_eq_pt_iff _ _ _).1 h
  have h1 : ‖(v q : C)‖ = 1 := by
    obtain ⟨a, ha⟩ := hu.exists_right_inv
    have h2 : ‖(v q : C)‖ * ‖(a : C)‖ = 1 := by
      rw [← norm_mul, ← norm_one (α := C)]
      exact congrArg (fun x : ↥(intO C) => ‖(x : C)‖) ha
    have h3 : ‖(v q : C)‖ ≤ 1 := (v q).2
    have h4 : ‖(a : C)‖ ≤ 1 := a.2
    nlinarith [norm_nonneg (v q : C), norm_nonneg (a : C)]
  have e : ∀ q', (s • ((intO C).subtype ∘ v)) q' = s.val * (v q' : C) := fun _ => rfl
  refine ⟨fun q' => ?_, ?_⟩
  · rw [e, e, norm_mul, norm_mul, h1]
    exact mul_le_mul_of_nonneg_left (v q').2 (norm_nonneg _)
  · rw [e]
    exact mul_ne_zero s.ne_zero (fun h0 => by simp [h0] at h1)

theorem log_norm_add_log_grNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (n : ℕ) (u : Fin n → Let Dw.mult) (kk : Fin n) (h₀ : Down (u ∘ Fin.castLE kk.2.le)) (h₁ : Down (u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2))) (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M kk + 1)) (q₁ : Fin L'.n → Fin (plN M (kk + 1) + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g ⟨kk, _, h₀⟩ ⟨kk + 1, _, h₁⟩ L' ix q₀ q₁ r → Down u → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (z : Sp ↥(intO C) ⟶ Z.X) a i (φ : Γ(Z.X, (Z.U a).1) →+* C), spMap φ ≫ Z.chart a = spMap (intO C).subtype ≫ z → ⊤ ≤ z ⁻¹ᵁ L'.U i → Real.log ‖valF (spMap (intO C).subtype ≫ z) _ (r a i).val‖ + Real.log (grNorm (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π) (latDR (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π)) (fun j => (Z.fr a).bc φ (u j).1 (u j).2) kk) = 0 := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T n u kk h₀ h₁ L' ix q₀ q₁ r hL hu C _ _ z a i φ hφ hz
  have : (Y Z.i).X.IsSeparated := by
    have hp : IsProper (Y Z.i).s := projProper _ _ _ (Y Z.i).proj
    constructor
    rw [← terminal.comp_from (Y Z.i).s]
    infer_instance
  have hle := hz.trans (z.preimage_mono (hL.le i))
  have hU : ⊤ ≤ (z ≫ Z.π) ⁻¹ᵁ L.U (ix i) := fun y hy => (hle hy).1
  have hq₀ : ⊤ ≤ (z ≫ g ⟨kk, _, h₀⟩) ⁻¹ᵁ chart _ _ (q₀ i) := fun y hy => (hle hy).2.1
  have hq₁ : ⊤ ≤ (z ≫ g ⟨kk + 1, _, h₁⟩) ⁻¹ᵁ chart _ _ (q₁ i) := fun y hy => (hle hy).2.2
  obtain ⟨φO, hO⟩ := exists_fromSpec (aff (ix i)) _ hU
  have hx : spMap ((intO C).subtype.comp φO) ≫ (aff (ix i)).fromSpec = (spMap (intO C).subtype ≫ z) ≫ Z.π := by
    rw [Category.assoc, ← hO, ← Category.assoc]
    congr 1
    exact Spec.map_comp (CommRingCat.ofHom φO) (CommRingCat.ofHom (intO C).subtype)
  have hx' : spMap φ ≫ Z.chart a ≫ Z.π = (spMap (intO C).subtype ≫ z) ≫ Z.π := by rw [← hφ, Category.assoc]
  have P := GlobalTheory.FlagEmb.PlkPt.plk_pt E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T C a (ix i) φ _ (hx.trans hx'.symm)
  have hg : ∀ en, spMap (intO C).subtype ≫ z ≫ g en = spMap φ ≫ Z.chart a ≫ g en := fun en => by
    rw [← Category.assoc, ← hφ, Category.assoc]
  obtain ⟨hu₀, e₀⟩ := P ⟨kk, _, h₀⟩
  obtain ⟨hu₁, e₁⟩ := P ⟨kk + 1, _, h₁⟩
  obtain ⟨hun, -⟩ := P ⟨n, u, hu⟩
  obtain ⟨m₀, n₀⟩ := max_of_chart _ _ hq₀ _ _ _ ((hg _).trans e₀)
  obtain ⟨m₁, n₁⟩ := max_of_chart _ _ hq₁ _ _ _ ((hg _).trans e₁)
  have hv := hL.val C a i φ _ (hx.trans hx'.symm) (by
    rw [hφ]
    exact (spMap (intO C).subtype).preimage_mono hz)
  have key := GlobalTheory.FlagEmb.GradedNorm.sInf_mul_norm_plk C M n
    (fun j => crd (ix i) C ((intO C).subtype.comp φO) ((Z.fr a).bc φ (u j).1 (u j).2)) kk (q₀ i) (q₁ i)
    (span_range_eq_top_iff_ne_zero.1 hun) m₀ m₁
  have tan : ∀ j, IsTanAtG (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π) ((Z.fr a).bc φ (u j).1 (u j).2) :=
    fun j => hx' ▸ ((T.frame a C φ).1 (u j).1 (u j).2).1
  have lat := fun w => GlobalTheory.LatDRCrd.mem_latDR_iff_crd E H _ (Y Z.i).t L aff M crd T.emb (ix i) C φO _ w hx
  have hS : grNorm (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π)
      (latDR (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π)) (fun j => (Z.fr a).bc φ (u j).1 (u j).2) kk =
      sInf {s : ℝ | ∃ cf : Fin n → C, cf kk ≠ 0 ∧ (∀ k, kk < k → cf k = 0) ∧ (∀ s, ‖(∑ j, cf j •
        crd (ix i) C ((intO C).subtype.comp φO) ((Z.fr a).bc φ (u j).1 (u j).2)) s‖ ≤ 1) ∧ s = ‖cf kk‖⁻¹} := by
    refine congrArg sInf (Set.ext fun s => exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_left fun _ => ⟨?_, fun hb => ?_⟩)
    · rintro ⟨w, hw, hc⟩
      have ht := comb_tan _ tan hc
      rw [← (T.emb.comb_iff _ _ hx tan ht cf).1 hc]
      exact (lat w ht).1 hw
    · obtain ⟨w, ht, hc⟩ := exists_comb _ tan cf
      refine ⟨w, (lat w ht).2 ?_, hc⟩
      rw [(T.emb.comb_iff _ _ hx tan ht cf).1 hc]
      exact hb
  rw [hS, ← hφ]
  have aux : ∀ (x A B : C) (s : ℝ), x * B = A → s * ‖A‖ = ‖B‖ → B ≠ 0 → Real.log ‖x‖ + Real.log s = 0 := by
    intro x A B s h1 h2 h3
    have h4 : ‖x‖ * s = 1 := by
      refine mul_right_cancel₀ (norm_ne_zero_iff.2 h3) ?_
      rw [← h1, norm_mul] at h2
      rw [one_mul]
      linear_combination h2
    rw [← Real.log_mul (left_ne_zero_of_mul_eq_one h4) (right_ne_zero_of_mul_eq_one h4), h4, Real.log_one]
  exact aux _ _ _ _ hv key n₁

end GlobalTheory.FlagEmb.LineNorm
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pre_model_chart_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (n : ℕ) (u : Fin n → Let Dw.mult) (kk : Fin n) (h₀ : Down (u ∘ Fin.castLE kk.2.le)) (h₁ : Down (u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2))) (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M kk + 1)) (q₁ : Fin L'.n → Fin (plN M (kk + 1) + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g ⟨kk, _, h₀⟩ ⟨kk + 1, _, h₁⟩ L' ix q₀ q₁ r → Down u → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (z : Sp ↥(intO C) ⟶ Z.X) a i (φ : Γ(Z.X, (Z.U a).1) →+* C), spMap φ ≫ Z.chart a = spMap (intO C).subtype ≫ z → ⊤ ≤ z ⁻¹ᵁ L'.U i → Real.log ‖valF (spMap (intO C).subtype ≫ z) _ (r a i).val‖ + Real.log (grNorm (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π) (latDR (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π)) (fun j => (Z.fr a).bc φ (u j).1 (u j).2) kk) = 0 := by
  first | exact @GlobalTheory.FlagEmb.LineNorm.log_norm_add_log_grNorm | exact GlobalTheory.FlagEmb.LineNorm.log_norm_add_log_grNorm | (intros; apply GlobalTheory.FlagEmb.LineNorm.log_norm_add_log_grNorm <;> assumption)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.DR

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_comp_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    {Z : Scheme.{0}} (h : Sp A ⟶ Z) : spMap g ≫ spMap f ≫ h = spMap (g.comp f) ≫ h := by
  rw [← Category.assoc, sp_comp]

theorem sp_id {A : Type} [CommRing A] {Z : Scheme.{0}} (h : Sp A ⟶ Z) : spMap (RingHom.id A) ≫ h = h :=
  (congrArg (· ≫ h) (Spec.map_id _)).trans (Category.id_comp _)

theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

theorem dual_id {A : Type} [CommRing A] : dualMap (RingHom.id A) = RingHom.id _ := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

theorem pt_congr {R A : Type} [CommRing R] [CommRing A] {N : ℕ} {c c' : R →+* A} {v v' : Fin (N + 1) → A} {h h'}
    (e : c = c') (e' : v = v') : pt c v h = pt c' v' h' := by
  subst e e'
  rfl

theorem exists_ringEquiv {A : Type} [CommRing A] {Z : Scheme.{0}} (κ : Sp A ⟶ Z) [IsOpenImmersion κ] :
    ∃ θ : A ≃+* Γ(Z, κ.opensRange), spMap θ.toRingHom ≫ κ = (isAffineOpen_opensRange κ).fromSpec := by
  let e := IsOpenImmersion.isoOfRangeEq (isAffineOpen_opensRange κ).fromSpec κ
    (isAffineOpen_opensRange κ).range_fromSpec
  let e' : CommRingCat.of A ≅ Γ(Z, κ.opensRange) := (Scheme.Spec.preimageIso (X := .op _) (Y := .op _) e).unop
  refine ⟨e'.commRingCatIsoToRingEquiv, ?_⟩
  have : spMap e'.commRingCatIsoToRingEquiv.toRingHom = e.hom := Scheme.Spec.map_preimage e.hom
  rw [this]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem exists_factor {k : Type} [Field k] {X : Scheme.{0}} (x : Sp k ⟶ X) (U : X.affineOpens)
    (h : x (IsLocalRing.closedPoint k) ∈ U.1) : ∃ ψ : Γ(X, U.1) →+* k, spMap ψ ≫ U.2.fromSpec = x := by
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hr : Set.range x ⊆ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q (IsLocalRing.closedPoint k)]
  refine ⟨(Spec.preimage (IsOpenImmersion.lift U.2.fromSpec x hr)).hom, ?_⟩
  exact (congrArg (· ≫ _) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac U.2.fromSpec x hr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem bc_bc {X : Scheme.{0}} {t : SAB H X} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) (u : Vecs Dw t A) : (u.bc f).bc g = u.bc (g.comp f) := by
  funext τ i
  simp only [Vecs.bc]
  rw [sp_comp_assoc, dual_comp]

theorem bc_id {X : Scheme.{0}} {t : SAB H X} {A : Type} [CommRing A] (u : Vecs Dw t A) : u.bc (RingHom.id A) = u := by
  funext τ i
  simp only [Vecs.bc]
  rw [dual_id, sp_id]

theorem map_cell {T : Type} {m : T → ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (x : CellVar m → S)
    (τ : T) (i j : Fin (m τ)) : φ (cell x τ i j) = cell (φ ∘ x) τ i j := by
  unfold cell
  split_ifs <;> simp

section Cover

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {L : FinLB Y.X} {aff : ∀ i, IsAffineOpen (L.U i)} {M : ℕ} {crd : Crd Y.t L M} {B : Type}
  {V : B → Y.X.affineOpens} {ι : B → Fin L.n} {ρ : ∀ b, Γ(Y.X, L.U (ι b)) →+* Γ(Y.X, (V b).1)}
  {α : ∀ b, c.F →+* Γ(Y.X, (V b).1)} {e : ∀ b, Vecs Dw Y.t Γ(Y.X, (V b).1)}
  {D : ∀ b, Let Dw.mult → Fin (M + 1) → Γ(Y.X, (V b).1)}

theorem crd_bc (hE : IsLieEmb Y.t L aff crd) (hF : IsFrameCover Y L aff crd V ι ρ α e D) (b : B) {R : Type} [CommRing R]
    (φ : Γ(Y.X, (V b).1) →+* R) (z : Let Dw.mult) :
    crd (ι b) R (φ.comp (ρ b)) ((e b).bc φ z.1 z.2) = φ ∘ crd (ι b) _ (ρ b) (e b z.1 z.2) := by
  refine hE.nat _ _ _ _ _ _ ?_
  have := ((hF.frame b _ (RingHom.id _)).1 z.1 z.2).1
  rwa [bc_id, sp_id, ← hF.res b] at this

theorem exists_cellFrame (hE : IsLieEmb Y.t L aff crd) (hF : IsFrameCover Y L aff crd V ι ρ α e D) (b : B)
    (w : Pm Dw.mult) {R₀ : Type} [CommRing R₀] (φ₀ : Γ(Y.X, (V b).1) →+* R₀) (x : CellVar Dw.mult → R₀) :
    ∃ u : Vecs Dw Y.t R₀, ∀ (R : Type) [CommRing R] (φ : R₀ →+* R),
      IsFrame Y.t (φ.comp (φ₀.comp (α b))) (spMap φ ≫ spMap φ₀ ≫ (V b).2.fromSpec) (u.bc φ) ∧
      ∀ z : Let Dw.mult, crd (ι b) R (φ.comp (φ₀.comp (ρ b))) (u.bc φ z.1 z.2) =
        cellVec (fun z => (φ.comp φ₀) ∘ crd (ι b) _ (ρ b) (e b z.1 z.2)) w (φ ∘ x) z := by
  choose u hu hu' using fun τ j => exists_comb Y.t (fun i => ((hF.frame b R₀ φ₀).1 τ (w τ i)).1) fun i => cell x τ i j
  refine ⟨u, fun R _ φ => ?_⟩
  have hc : ∀ τ j, IsCombAtG Y.t (spMap (φ.comp φ₀) ≫ (V b).2.fromSpec) (fun i => (e b).bc (φ.comp φ₀) τ (w τ i))
      (fun i => cell (φ ∘ x) τ i j) (Vecs.bc φ u τ j) := fun τ j => by
    have := GlobalTheory.LatDRFree.comb_map Y.t φ (hu' τ j)
    rw [sp_comp_assoc] at this
    simp only [map_cell] at this
    rw [← bc_bc]
    exact this
  have hf := hF.frame b R (φ.comp φ₀)
  refine ⟨?_, fun z => ?_⟩
  · rw [sp_comp_assoc]
    exact (GlobalTheory.T.tangent_combination_eigen_action E H Dw l c Y.X Y.t R _).2 _ _ _ w _ hf hc
  · have hx : spMap ((φ.comp φ₀).comp (ρ b)) ≫ (aff (ι b)).fromSpec = spMap (φ.comp φ₀) ≫ (V b).2.fromSpec := by
      rw [← sp_comp_assoc, hF.res]
    have ht := fun i => (hf.1 z.1 (w z.1 i)).1
    refine ((hE.comb_iff _ _ hx ht (comb_tan Y.t ht (hc z.1 z.2)) _).1 (hc z.1 z.2)).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg _ (crd_bc hE hF b (φ.comp φ₀) ⟨z.1, w z.1 i⟩)

theorem exists_cell [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (hβ : β = algebraMap O c.F)
    (hE : IsLieEmb Y.t L aff crd) (hF : IsFrameCover Y L aff crd V ι ρ α e D)
    {k : Type} [Field k] (f : c.F →+* k) (y : Sp k ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap f)
    (u : Vecs Dw Y.t k) (hu : IsFrame Y.t f (y ≫ Y.j) u) :
    ∃ (b : B) (w : Pm Dw.mult) (ψ : Γ(Y.X, (V b).1) →+* k) (x : CellVar Dw.mult → k) (d : Let Dw.mult → k),
      spMap ψ ≫ (V b).2.fromSpec = y ≫ Y.j ∧ ψ.comp (α b) = f ∧
      Tri (cellVec (fun z => ψ ∘ crd (ι b) _ (ρ b) (e b z.1 z.2)) w x)
        (fun z => crd (ι b) k (ψ.comp (ρ b)) (u z.1 z.2)) d := by
  have h1 : (y ≫ Y.j) (IsLocalRing.closedPoint k) ∈ ⋃ b, ((V b).1 : Set Y.X) := by
    rw [hF.cover]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 h1
  obtain ⟨ψ, hψ⟩ := exists_factor (y ≫ Y.j) (V b) hb
  have h2 : ψ.comp (α b) = f := by
    have e1 : spMap ((ψ.comp (α b)).comp β) = spMap (f.comp β) := by
      rw [RingHom.comp_assoc, ← sp_comp, ← hF.isCover.ovr b, ← Category.assoc, hψ, ← sp_comp, ← hy, Model.j]
      simp only [Category.assoc]
      rw [pullback.condition, ← Y.jQ_over]
      simp only [Category.assoc]
    have e2 : (ψ.comp (α b)).comp β = f.comp β := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) ?_
    rw [← hβ]
    exact e2
  have hx : spMap (ψ.comp (ρ b)) ≫ (aff (ι b)).fromSpec = y ≫ Y.j := by rw [← sp_comp_assoc, hF.res, hψ]
  have hf := hF.frame b k ψ
  rw [hψ] at hf
  have t1 := (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw l c Y.X Y.t L aff M crd hE (ι b) k _ _ _ _ _ _ hx hf hu).2.2 h2
  have t2 := (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw l c Y.X Y.t L aff M crd hE (ι b) k _ _ _ _ _ _ hx hu hu).2.1
  simp only [crd_bc hE hF b ψ] at t1
  obtain ⟨w, x, d, -, -, h⟩ := GlobalTheory.T.exists_integral_flagCell_of_valuedField _ _ k ⊤ M _ _ t1 t2
  exact ⟨b, w, ψ, x, d, hψ, h2, h⟩

end Cover

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem dvr_place {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    IsDiscreteValuationRing (c.V W) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

set_option maxHeartbeats 800000 in

theorem exists_tied (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (i : Idx H p) (hd : i₀.l.Dvd i.l)
    (hle : i₀.c.F ≤ i.c.F) :
    ∃ (Z : Mdl Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M)
      (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1))
      (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Z.i = i ∧ Comparison₂ Z.toPre L aff crd ι ρ g := by
  classical
  have := dvr_place i.c hp.ne_zero hW
  have : IsProper (Y i).s := projProper _ _ _ (Y i).proj
  have : IsLocallyNoetherian (Y i).X := LocallyOfFiniteType.isLocallyNoetherian (Y i).s
  have : IsReduced (Y i).X := by
    have : ∀ x : (Y i).X, _root_.IsReduced ((Y i).X.presheaf.stalk x) := fun x => by
      have := ((Y i).normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨L, aff, M, crd, hE⟩ := GlobalTheory.T.exists_lie_embedding_projective E H _ _ (Y i).s (Y i).t (Y i).proj
  obtain ⟨n, V, ι, ρ, α, e, D, hF⟩ := GlobalTheory.T.exists_affine_refinement_lie_embedding E H Dw _ _ _ p W (Y i) hp hW L aff M crd hE
  obtain ⟨N, I, π, g, κ, hπ, hM⟩ := GlobalTheory.T.isCover_normal_projective_charts (i.c.V W) i.c.F _ (Y i).s _ Dw.mult M _ V α _ D (Y i).proj (Y i).normal
    hF.isCover
  have hop := hM.opn
  let eqv := (Fintype.equivFin (Fin n × Pm Dw.mult)).symm
  choose θ hθ using fun a => exists_ringEquiv (κ (eqv a).1 (eqv a).2)
  let φ₀ : ∀ a, Γ((Y i).X, (V (eqv a).1).1) →+* Γ(I.subscheme, (κ (eqv a).1 (eqv a).2).opensRange) :=
    fun a => (θ a).toRingHom.comp MvPolynomial.C
  choose fr hfr using fun a => exists_cellFrame hE hF (eqv a).1 (eqv a).2 (φ₀ a) fun v => θ a (MvPolynomial.X v)
  let Z : Pre Y i₀ := ⟨i, hd, hle, N, I, π, fun τ => Finset.range (Dw.mult τ + 1), _,
    fun a => ⟨(κ (eqv a).1 (eqv a).2).opensRange, isAffineOpen_opensRange _⟩, fun a => (φ₀ a).comp (α _), fr⟩
  have hch : ∀ a, Z.chart a = spMap (θ a).toRingHom ≫ κ (eqv a).1 (eqv a).2 := fun a => (hθ a).symm
  have hb : ∀ a, Z.chart a ≫ Z.π = spMap (φ₀ a) ≫ (V (eqv a).1).2.fromSpec := fun a => by
    rw [hch, Category.assoc]
    erw [hM.base]
    exact sp_comp_assoc _ _ _
  have hopn : Z.opn = π ⁻¹' ⋃ b, ((V b).1 : Set (Y i).X) := by rw [hF.cover]; rfl
  have hcov : ⋃ a, ((Z.U a).1 : Set Z.X) = Z.opn := by
    rw [hopn, ← hM.cover]
    ext z
    simp only [Set.mem_iUnion]
    refine ⟨fun ⟨a, h⟩ => ⟨_, _, h⟩, fun ⟨b, w, h⟩ => ?_⟩
    obtain ⟨a, ha⟩ := eqv.surjective (b, w)
    obtain rfl : b = (eqv a).1 := by rw [ha]
    obtain rfl : w = (eqv a).2 := by rw [ha]
    exact ⟨a, h⟩
  have halg : ∀ a, Z.chart a ≫ Z.π ≫ (Y Z.i).s = spMap ((Z.alg a).comp (Z.i.c.V W).subtype) := fun a => by
    rw [← Category.assoc, hb, Category.assoc]
    erw [hF.isCover.ovr]
    exact sp_comp _ _
  have hfr' : ∀ a (R : Type) [CommRing R] (φ : Γ(Z.X, (Z.U a).1) →+* R),
      IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ) := fun a R _ φ => by
    rw [hb]
    exact (hfr a R φ).1
  have hres : ∀ a, spMap ((φ₀ a).comp (ρ (eqv a).1)) ≫ (aff (ι (eqv a).1)).fromSpec = Z.chart a ≫ Z.π := fun a => by
    rw [hb, ← sp_comp_assoc, hF.res]
  have hT : Comparison₂ Z L aff crd (fun a => ι (eqv a).1) (fun a => (φ₀ a).comp (ρ _)) g := by
    refine ⟨hE, rfl, hres, hcov, halg, hfr', fun a en => ?_, fun k _ z z' hz => hM.inj k z z' ?_⟩
    · obtain ⟨hu, h⟩ := hM.plk (eqv a).1 (eqv a).2 en
      have e1 : (θ a).toRingHom ∘ plk (uvec (fun z => crd (ι (eqv a).1) _ (ρ _) (e (eqv a).1 z.1 z.2)) (eqv a).2) en.2.1 =
          plk (fun z : Let Dw.mult => crd (ι (eqv a).1) _ ((φ₀ a).comp (ρ _)) (fr a z.1 z.2)) en.2.1 := by
        rw [map_plk]
        congr 1
        funext z
        have := (hfr a _ (RingHom.id _)).2 z
        rw [bc_id] at this
        exact (map_cellVec _ _ _ _ _).trans this.symm
      refine ⟨e1 ▸ span_range_comp_eq_top _ hu _, ?_⟩
      rw [hch, Category.assoc]
      exact (congrArg (spMap (θ a).toRingHom ≫ ·) h).trans ((spMap_pt _ _ _ _).trans (pt_congr rfl e1))
    · rintro _ ⟨q, rfl⟩
      have := hz ⟨q, rfl⟩
      rw [hopn] at this
      rw [Scheme.Hom.comp_apply]
      exact this
  refine ⟨⟨Z, hπ, GlobalTheory.IsNormalScheme.of_pred hM.normal, (congrArg (fun f => Flat f) hπ).mp hM.flat, hopn ▸ hM.dense, hcov, fun a => ?_, fun a => ?_, fun a => ?_,
    GlobalTheory.T.pre_model_chart_compatible E H Dw Xo p W Y i₀ Z L aff M crd _ _ g hT, fun k _ f y hy u hu => ?_⟩, L, aff, M, crd, _, _, g, rfl, hT⟩
  · exact (congrArg (Z.chart a ≫ ·) hπ.symm).trans (halg a)
  · have := (GlobalTheory.T.smooth_base_and_normal_coordinate_ring (Y i).X _ Dw.mult (V (eqv a).1) (Y i).normal).1
    have : IsIso (spMap (θ a).toRingHom) := inferInstanceAs (IsIso (Spec.map (θ a).toCommRingCatIso.hom))
    have e1 : Z.chart a ≫ π = spMap (θ a).toRingHom ≫ cbase Dw.mult (V (eqv a).1) := by
      rw [hch, Category.assoc]
      erw [hM.base]
    rw [e1]
    infer_instance
  · have := hfr' a _ (RingHom.id _)
    rwa [bc_id, sp_id] at this
  · refine existsUnique_of_exists_of_unique ?_ fun w w' h h' =>
      GlobalTheory.T.pre_model_chart_transition E H Dw Xo p W Y i₀ Z L aff M crd _ _ g hT k w w' u (h.1.trans h'.1.symm) h.2 h'.2
    obtain ⟨b, w, ψ, x, d, hψ, hf, htri⟩ := exists_cell rfl hE hF f y hy u hu
    obtain ⟨a, ha⟩ := eqv.surjective (b, w)
    obtain rfl : b = (eqv a).1 := by rw [ha]
    obtain rfl : w = (eqv a).2 := by rw [ha]
    let φ : Γ(Z.X, (Z.U a).1) →+* k := (MvPolynomial.eval₂Hom ψ x).comp (θ a).symm.toRingHom
    have h0 : φ.comp (φ₀ a) = ψ := RingHom.ext fun r =>
      (congrArg (MvPolynomial.eval₂Hom ψ x) ((θ a).symm_apply_apply _)).trans (MvPolynomial.eval₂Hom_C _ _ _)
    have h1 : (φ ∘ fun v => θ a (MvPolynomial.X v)) = x := funext fun v =>
      (congrArg (MvPolynomial.eval₂Hom ψ x) ((θ a).symm_apply_apply _)).trans (MvPolynomial.eval₂Hom_X' _ _ _)
    have h2 : (spMap φ ≫ Z.chart a) ≫ Z.π = y ≫ (Y i).j := by
      rw [Category.assoc, hb]
      exact (sp_comp_assoc _ _ _).trans ((congrArg (spMap · ≫ _) h0).trans hψ)
    have h3 : φ.comp (Z.alg a) = f := by rw [← hf, ← h0]; rfl
    have h4 := hfr' a k φ
    rw [← Category.assoc, h2] at h4
    refine ⟨spMap φ ≫ Z.chart a, h2, a, φ, rfl, ?_, ?_⟩
    · rw [h2, h3]
      exact hu
    · rw [h2]
      have hx : spMap (ψ.comp (ρ _)) ≫ (aff (ι (eqv a).1)).fromSpec = y ≫ (Y i).j := by
        rw [← sp_comp_assoc, hF.res]
        exact hψ
      refine (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd hE _ k _ _ _ _ _ _ hx h4 hu).1.2 ⟨d, ?_⟩
      have h5 := funext (hfr a k φ).2
      rw [h1, ← RingHom.comp_assoc, h0] at h5
      rw [← h5] at htri
      exact htri

end GlobalTheory.FlagEmb.DR

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Cartier in

theorem GlobalTheory.FlagEmb.DR.exists_lineModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ i : Idx H p, i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → ∀ st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧ (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z false st x) := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW _ i hd hle st x hx
  obtain ⟨Z, L, aff, M, crd, ι, ρ, g, hi, hT⟩ := GlobalTheory.FlagEmb.DR.exists_tied (Y := Y) hp hW i hd hle
  obtain ⟨n, u, k, hu, h₀, h₁, rfl, hln⟩ := GlobalTheory.T.exists_descending_letter_chain E H Dw st x hx
  obtain ⟨L', ix, q₀, q₁, r, hL⟩ := GlobalTheory.T.pre_model_chart_frame E H Dw Xo p W Y i₀ Z.toPre L aff M crd ι ρ g hT ⟨k, _, h₀⟩ ⟨k + 1, _, h₁⟩ rfl
  refine ⟨Z, hi, hT.ty, ⟨L', r, hL.trans,
    GlobalTheory.T.pre_model_chart_section E H Dw Xo p W Y i₀ Z.toPre L aff M crd ι ρ g hT n u k h₀ h₁ L' ix q₀ q₁ r hL, fun y a j φ h h' => ?_⟩⟩
  rw [hln]
  exact GlobalTheory.T.pre_model_chart_values E H Dw Xo p W Y i₀ Z.toPre L aff M crd ι ρ g hT n u k h₀ h₁ L' ix q₀ q₁ r hL hu _ y.z a j φ h h'
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_system_model_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ i : Idx H p, i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → ∀ st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧ (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z false st x) := by
  atlas_forward_decl GlobalTheory.FlagEmb.DR.exists_lineModel
end
