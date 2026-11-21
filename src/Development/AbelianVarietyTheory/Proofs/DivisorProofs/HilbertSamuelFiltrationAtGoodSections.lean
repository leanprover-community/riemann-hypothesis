import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedSectionChartCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelSectionShiftCommSingleMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelDegreeZeroResiduesRangeEqTop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDataOfPositivity

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.SplitField

theorem exists_algHom_factor (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] :
    ∃ p : Polynomial E, ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [Algebra p.SplittingField Ω]
      [IsScalarTower E p.SplittingField Ω] (φ : A →ₐ[E] Ω),
      ∃ φ₀ : A →ₐ[E] p.SplittingField, ∀ a, φ a = algebraMap p.SplittingField Ω (φ₀ a) := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := E) (M := A)
  obtain ⟨p, hp⟩ : ∃ p : Polynomial E, p = ∏ a ∈ t, minpoly E a := ⟨_, rfl⟩
  refine ⟨p, fun Ω _ _ _ _ φ => ?_⟩
  have hp0 : p ≠ 0 := hp ▸ Finset.prod_ne_zero_iff.2 fun a _ => minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)
  let j : p.SplittingField →ₐ[E] Ω := IsScalarTower.toAlgHom E p.SplittingField Ω
  have hj : Function.Injective j := j.toRingHom.injective
  have hgen : ∀ a ∈ t, φ a ∈ j.range := fun a ha => by
    have h0 : Polynomial.aeval (φ a) p = 0 := by
      rw [Polynomial.aeval_algHom_apply, hp, map_prod, Finset.prod_eq_zero ha (minpoly.aeval E a), map_zero]
    have hs := Polynomial.SplittingField.splits p
    have hr : φ a ∈ ((p.map (algebraMap E p.SplittingField)).map (algebraMap p.SplittingField Ω)).roots := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.mem_roots (Polynomial.map_ne_zero hp0),
        Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      exact h0
    rw [hs.roots_map] at hr
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 hr
    exact ⟨b, hb⟩
  have hall : ∀ a, φ a ∈ j.range := fun a => by
    have ha : a ∈ Submodule.span E (t : Set A) := ht ▸ trivial
    induction ha using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Subalgebra.smul_mem _ hx c
  refine ⟨(AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (φ.codRestrict j.range hall), fun a => ?_⟩
  exact (congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply ⟨φ a, hall a⟩)).symm

theorem exists_point_factor (E : Type) [Field E] {Z : Scheme.{0}} (f : Z ⟶ Sp E) [IsFinite f] :
    ∃ p : Polynomial E, ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [Algebra p.SplittingField Ω]
      [IsScalarTower E p.SplittingField Ω] (z : Sp Ω ⟶ Z), z ≫ f = spMap (algebraMap E Ω) →
      ∃ z₀ : Sp p.SplittingField ⟶ Z, z₀ ≫ f = spMap (algebraMap E p.SplittingField) ∧
        z = spMap (algebraMap p.SplittingField Ω) ≫ z₀ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  obtain ⟨g, hg⟩ := Spec.map_surjective (R := CommRingCat.of E) (Z.isoSpec.inv ≫ f)
  have hfin : g.hom.Finite := (IsFinite.SpecMap_iff g).1 (hg ▸ inferInstance)
  letI : Algebra E Γ(Z, ⊤) := g.hom.toAlgebra
  have : Module.Finite E Γ(Z, ⊤) := hfin
  obtain ⟨p, hp⟩ := exists_algHom_factor E Γ(Z, ⊤)
  refine ⟨p, fun Ω _ _ _ _ z hz => ?_⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (S := CommRingCat.of Ω) (z ≫ Z.isoSpec.hom)
  have hc : g ≫ ψ = CommRingCat.ofHom (algebraMap E Ω) := Spec.map_injective (by
    rw [Spec.map_comp, hg, hψ, Category.assoc, Iso.hom_inv_id_assoc, hz])
  obtain ⟨φ₀, h₀⟩ := hp Ω { ψ.hom with commutes' := fun a => congrArg (fun q => q.hom a) hc }
  refine ⟨Spec.map (CommRingCat.ofHom φ₀.toRingHom) ≫ Z.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => φ₀.commutes a))
  · rw [← Category.assoc, Iso.eq_comp_inv, ← hψ, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => h₀ a))

theorem mem_subPts_iff_of_toBase_eq {F : Type} [Field F] (S : LinSys F) (E E' : Type) [Field E] [Field E'] [Algebra F E]
    [Algebra F E'] [Algebra E E'] {ι : Type} (s : ι → Fin S.N → E)
    {Ω : Type} [Field Ω] [Algebra E Ω] [Algebra E' Ω] [Algebra F Ω] [IsScalarTower F E Ω] [IsScalarTower F E' Ω]
    [IsScalarTower E E' Ω] (x : (S.baseChange E).Pt Ω) (x' : (S.baseChange E').Pt Ω)
    (h : LinSys.toBase x = LinSys.toBase x') :
    x ∈ (S.baseChange E).subPts ((S.baseChange E).cut s) Ω ↔
      x' ∈ (S.baseChange E').subPts ((S.baseChange E').cut fun i k => algebraMap E E' (s i k)) Ω := by
  refine (S.mem_subPts_cut_baseChange_iff E s x).trans
    (Iff.trans ?_ (S.mem_subPts_cut_baseChange_iff E' (fun i k => algebraMap E E' (s i k)) x').symm)
  rw [h]
  simp only [← IsScalarTower.algebraMap_apply]

end GlobalTheory.HSCore.SplitField

namespace GlobalTheory.HSCore

open SplitField in

theorem exists_split : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin T.D → Fin T.N → E), T.IsGoodSection E s → ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : Algebra F E') (_ : Algebra E E') (_ : IsScalarTower F E E'), Split T E' fun i k => algebraMap E E' (s i k) := by
  intro F _ _ T E _ _ _ s hs
  have hfin : IsFinite ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str) := hs.finiteEtale.finite
  obtain ⟨p, hp⟩ := exists_point_factor E ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
  refine ⟨p.SplittingField, inferInstance, NumberField.of_module_finite E _, inferInstance, inferInstance,
    inferInstance, fun x hx => ?_⟩
  let x' : (T.toLinSys.baseChange p.SplittingField).Pt (AlgebraicClosure p.SplittingField) :=
    ⟨x ≫ Scheme.IdealSheafData.subschemeι _, (Category.assoc _ _ _).trans hx⟩
  obtain ⟨y, hy⟩ := (T.toLinSys.toBase_bijective E (AlgebraicClosure p.SplittingField)).2 (LinSys.toBase x')
  obtain ⟨z, hz⟩ := (mem_subPts_iff_of_toBase_eq T.toLinSys E p.SplittingField s y x' hy).2 ⟨x, rfl⟩
  obtain ⟨z₀, h₀, h₁⟩ := hp (AlgebraicClosure p.SplittingField) z (by
    rw [← Category.assoc]; exact (congrArg (· ≫ _) hz).trans y.2)
  let y₀ : (T.toLinSys.baseChange E).Pt p.SplittingField :=
    ⟨z₀ ≫ Scheme.IdealSheafData.subschemeι _, (Category.assoc _ _ _).trans h₀⟩
  obtain ⟨x₁, hx₁⟩ := (T.toLinSys.toBase_bijective p.SplittingField p.SplittingField).2 (LinSys.toBase y₀)
  obtain ⟨x₀, hx₀⟩ := (mem_subPts_iff_of_toBase_eq T.toLinSys E p.SplittingField s y₀ x₁ hx₁.symm).1 ⟨z₀, rfl⟩
  refine ⟨x₀, ?_⟩
  refine (cancel_mono (Scheme.IdealSheafData.subschemeι _)).1 ?_
  refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hx₀)).symm
  refine (T.toLinSys.isPullback_baseChange p.SplittingField).hom_ext ?_ ?_
  · have e₁ : x₁.1 ≫ T.toLinSys.bcFst _ = y₀.1 ≫ T.toLinSys.bcFst _ := congrArg Subtype.val hx₁
    have e₂ : y.1 ≫ T.toLinSys.bcFst _ = x'.1 ≫ T.toLinSys.bcFst _ := congrArg Subtype.val hy
    refine e₂.symm.trans ?_
    rw [Category.assoc, e₁, ← hz, h₁, Category.assoc, Category.assoc]
    rfl
  · refine x'.2.trans ?_
    rw [Category.assoc, x₁.2, ← Spec.map_comp]
    rfl

end GlobalTheory.HSCore
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem nef_big_baseChange : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (E : Type) [Field E] [NumberField E] [Algebra F E], IsNef F X.LA → IsBig F X.LA → IsNef E (X.baseChange E).LA ∧ IsBig E (X.baseChange E).LA := by
  intro F _ _ X E _ _ _ hn hb
  exact ⟨GlobalTheory.HilbertSamuel.Geo.isNef_baseChange X.toGeo E hn, GlobalTheory.HilbertSamuel.Geo.isBig_baseChange X.toGeo E hb⟩

end GlobalTheory.HSCore
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore

theorem mulPow_mulVar {K : Type} [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K) {a j l : ℕ}
    (h : j + (a + 1) = l) (h' : (j + 1) + a = l) (α : MonoDeg (Fin G.D) a) (i : Fin G.D) (m : G.Sec j) :
    mulPow G s h (MonoDeg.mulVar i α) m = mulPow G s h' α (G.mulW j (s i) m) := by
  rw [G.mulW_apply]
  unfold mulPow
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, monoVal_mulVar, mul_comm (secGer _ _ _ _ _), mul_assoc]

theorem filMono_of_kerRes : KerRes → FilMono := by
  intro H K _ _ G hnef hbig s hs a
  induction a with
  | zero =>
    intro j l h _ f hf
    obtain rfl : j = l := h
    have : Subsingleton (MonoDeg (Fin G.D) 0) := ⟨fun α β => Subtype.ext
      (((Finsupp.degree_eq_zero_iff _).1 α.2).trans ((Finsupp.degree_eq_zero_iff _).1 β.2).symm)⟩
    refine ⟨fun _ => f, fun _ => hf.1, ?_⟩
    rw [Fintype.sum_subsingleton _ (⟨0, rfl⟩ : MonoDeg (Fin G.D) 0)]
    exact (mulMono_zero _ _ _ _ _ f).symm
  | succ a ih =>
    classical
    intro j l h hj f hf
    have h' : (j + 1) + a = l := by omega
    have hfa : f ∈ Fil (G.ideal s) a (G.global l) := Fil_anti (Nat.le_succ a) hf
    obtain ⟨m, hm, e⟩ := ih (j + 1) l h' (by omega) f hfa
    have h0 : hs.sym h' (G.global l) ⟨f, hfa⟩ = 0 := (sym_eq_zero_iff _ _ _ _ _ _ _ _ _ _ _).2 hf
    have h1 : hs.sym h' (G.global l) ⟨f, hfa⟩ = fun α => hs.res (j + 1) (m α) :=
      sym_sum _ _ _ _ _ _ _ _ _ _ m _ e
    have hv : ∀ α, m α ∈ Fil (G.ideal s) 1 (G.global (j + 1)) := fun α =>
      ⟨hm α, (Res_eq_zero_iff _ _ _ _ _ _ _ _ _ _).1 (congrFun (h1.symm.trans h0) α)⟩
    choose m' hm' e' using fun α => H K G hnef hbig s hs j (by omega) (m α) (hv α)
    refine ⟨fun γ => ∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ),
      m' p.1 p.2, fun γ => sum_mem fun p _ => hm' _ _, ?_⟩
    have key : ∀ γ : MonoDeg (Fin G.D) (a + 1), mulPow G s h γ
        (∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ), m' p.1 p.2) =
        ∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ),
          mulPow G s h' p.1 (G.mulW j (s p.2) (m' p.1 p.2)) := fun γ => by
      rw [map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← (Finset.mem_filter.1 hp).2, mulPow_mulVar G s h h']
    rw [Finset.sum_congr rfl fun γ _ => key γ, Finset.sum_fiberwise, Fintype.sum_prod_type, e]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [e' α, map_sum]

end GlobalTheory.HSCore
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem nef_big_second_baseChange : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (E : Type) [Field E] [NumberField E] [Algebra F E], IsNef F X.L₂ → IsBig F X.L₂ → IsNef E (X.baseChange E).L₂ ∧ IsBig E (X.baseChange E).L₂ := by
  intro F _ _ X E _ _ _ hn hb
  exact ⟨PosBaseChange.isNef_baseChange (X.toGeo.isPullback_fst E) X.geom.alg.variety.proj hn,
    PosBaseChange.isBig_baseChange (X.toGeo.isPullback_fst E) X.geom.alg.variety.proj hb⟩

end GlobalTheory.HSShort
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.SplitCoord

theorem map_spec {F E K : Type} [CommRing F] [CommRing E] [CommRing K] [Algebra F E] [Algebra E K] [Algebra F K]
    [IsScalarTower F E K] {D N : ℕ} (s : Fin D → Fin N → E) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    map (algebraMap E K) (spec s f) = spec (fun i j => algebraMap E K (s i j)) f := by
  unfold spec
  induction f using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X]
    congr 1
    obtain ⟨a, b⟩ := i
    refine Fin.lastCases ?_ (fun a => ?_) a <;> simp [join]

theorem map_lin_smul {E K : Type} [CommRing E] [CommRing K] (φ : E →+* K) {N : ℕ} (c : E) (y : Fin N → E) :
    map φ (lin (c • y)) = C (φ c) * lin fun j => φ (y j) := by
  simp only [lin, map_sum, map_mul, map_X, map_C, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_eq_C_mul {E K σ : Type} [Field E] [Field K] (φ : E →+* K) {P Q : MvPolynomial σ E} (hP : P ≠ 0) {c : K}
    (hc : c ≠ 0) (h : map φ Q = C c * map φ P) : ∃ c₀ : E, c₀ ≠ 0 ∧ Q = C c₀ * P := by
  obtain ⟨m, hm⟩ := ne_zero_iff.1 hP
  have e : φ (coeff m Q) = c * φ (coeff m P) := by
    simpa only [coeff_map, coeff_C_mul] using congrArg (coeff m) h
  have e' : φ (coeff m Q / coeff m P) = c := by
    rw [map_div₀, e, mul_div_cancel_right₀ _ ((map_ne_zero φ).2 hm)]
  refine ⟨coeff m Q / coeff m P, fun h0 => hc (by rw [← e', h0, map_zero]), map_injective φ φ.injective ?_⟩
  rw [map_mul, map_C, e', h]

theorem exists_eq_C_mul_prod {E K ι : Type} [Field E] [Field K] [Fintype ι] (φ : E →+* K) {N : ℕ}
    {Q : MvPolynomial (Fin 1 × Fin N) E} {y v : ι → Fin N → E} {z : ι → Fin N → K} {a : ι → E} (hy : ∀ p, y p ≠ 0)
    (ha : ∀ p, a p ≠ 0) (ea : ∀ p, y p = a p • v p) (hz : ∀ p, z p = fun j => φ (v p j)) {c : K} (hc : c ≠ 0)
    (h : map φ Q = C c * ∏ p, lin (z p)) : ∃ c₀ : E, c₀ ≠ 0 ∧ Q = C c₀ * ∏ p, lin (y p) := by
  have hA : (∏ p, φ (a p)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => (map_ne_zero _).2 (ha p)
  refine exists_eq_C_mul φ (Finset.prod_ne_zero_iff.2 fun p _ => Check.lin_ne (hy p)) (div_ne_zero hc hA) ?_
  rw [h, map_prod]
  simp only [ea, hz, map_lin_smul]
  rw [Finset.prod_mul_distrib, ← map_prod C, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hA]

theorem exists_coord_spec_eq : ∀ (F : Type) [Field F] [NumberField F] (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin G.D → Fin G.N → E) (hs : (G.baseChange E).IsGood s) (δ : ℕ) (f : MvPolynomial (Fin (G.D + 1) × Fin G.N) F), Split G.toTuple E s → SimpleAt G.toTuple δ f E s → ∃ (Co : Coord (G.baseChange E) hs δ) (c : E), c ≠ 0 ∧ spec s f = C c * ∏ p, lin (Co.y p) := by
  intro F _ _ G E _ _ _ s hs δ f h hS
  obtain rfl := hS.card
  obtain ⟨x, Co, hCo, -⟩ := h.exists_coord hs
  obtain ⟨c, hc, e⟩ := hS.fac
  choose a ha ea using fun p => G.exists_coords_baseChange E (x p).pt.1
  have h₅ (p) : G.coords (LinSys.toBase (RatPt.geomPt G E s (x p))).1 =
      fun j => algebraMap E (AlgebraicClosure E) (G.coords ((x p).pt.1 ≫ G.bcFst E) j) := by
    rw [← LinSys.coords_spMap_comp]
    exact congrArg G.coords ((congrArg (· ≫ G.bcFst E) (Category.assoc _ _ _)).trans (Category.assoc _ _ _))
  have h₇ : ∏ᶠ z ∈ G.geomPts E (G.linSection E s), lin (G.coords (LinSys.toBase z : G.Pt (AlgebraicClosure E)).1) =
      ∏ p, lin (G.coords (LinSys.toBase (RatPt.geomPt G E s (x p)) : G.Pt (AlgebraicClosure E)).1) := by
    refine (finprod_mem_congr h.geomPts_eq fun _ _ => rfl).trans ?_
    rw [finprod_mem_range (RatPt.geomPt_injective hs), ← finprod_comp_equiv x, finprod_eq_prod_of_fintype]
  obtain ⟨c₀, h₀, e₀⟩ := exists_eq_C_mul_prod (N := G.N) (algebraMap E (AlgebraicClosure E)) (Q := spec s f) (y := Co.y)
    (fun p h0 => (G.baseChange E).geom.alg.bpf.coords_ne_zero _ ((hCo p).2.1.symm.trans h0)) ha
    (fun p => (hCo p).2.1.trans (ea p)) h₅ hc ((map_spec s f).trans (e.trans (congrArg (C c * ·) h₇)))
  exact ⟨Co, c₀, h₀, e₀⟩

end GlobalTheory.HSShort.SplitCoord
end
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinates_specialisedForm_prod_linearForms : ∀ (F : Type) [Field F] [NumberField F] (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin G.D → Fin G.N → E) (hs : (G.baseChange E).IsGood s) (δ : ℕ) (f : MvPolynomial (Fin (G.D + 1) × Fin G.N) F), Split G.toTuple E s → SimpleAt G.toTuple δ f E s → ∃ (Co : Coord (G.baseChange E) hs δ) (c : E), c ≠ 0 ∧ spec s f = C c * ∏ p, lin (Co.y p) := by
  atlas_forward_decl GlobalTheory.HSShort.SplitCoord.exists_coord_spec_eq
end

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort

section Lemmas

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem shift_apply_zero (u : Fin G.N → F) (x : Tot G) : shift G u x 0 = 0 := rfl

theorem shift_apply_succ (u : Fin G.N → F) (x : Tot G) (j : ℕ) : shift G u x (j + 1) = G.mulW j u (x j) := rfl

variable (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem totExt_apply (x : Tot G) (j : ℕ) : totExt G E x j = G.toExt E j (x j) := rfl

theorem totExt_single (j : ℕ) (s : G.Sec j) :
    totExt G E (Pi.single j s) = Pi.single j (G.toExt E j s) := by
  funext k
  rw [totExt_apply]
  by_cases h : k = j
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem shift_totExt (u : Fin G.N → F) (x : Tot G) :
    shift (G.baseChange E) (fun k => algebraMap F E (u k)) (totExt G E x) = totExt G E (shift G u x) := by
  funext j
  cases j with
  | zero => rw [shift_apply_zero, totExt_apply, shift_apply_zero, map_zero]
  | succ j =>
    rw [shift_apply_succ, totExt_apply, totExt_apply, shift_apply_succ, Geo.toExt_mulW]
    rfl

end Lemmas

theorem totExt_props : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ) (E : Type) [Field E] [NumberField E] [Algebra F E], (∀ (m : ℕ) (v : Fin m → (sysOf X Λ₀).V X.T), LinearIndependent F v → LinearIndependent E fun i => totExt X.toGeo E (v i)) ∧ (∀ u x, shift (X.toGeo.baseChange E) (fun k => algebraMap F E (u k)) (totExt X.toGeo E x) = totExt X.toGeo E (shift X.toGeo u x)) ∧ ∀ j, Submodule.span E (totExt X.toGeo E '' (sysOf X Λ₀).V j) = LinearMap.range (incl (X.baseChange E) j) := by
  intro F _ _ X Λ₀ E _ _ _
  refine ⟨?_, fun u x => shift_totExt X.toGeo E u x, ?_⟩
  · intro m v hv
    have hv' := hv.map' ((sysOf X Λ₀).V X.T).subtype (Submodule.ker_subtype _)
    have hform : ∀ i, ∃ y : X.toGeo.Sec X.T, (v i : Tot X.toGeo) = Pi.single X.T y := by
      intro i
      obtain ⟨y, hy⟩ := (v i).2
      exact ⟨y, hy.symm⟩
    choose f hf using hform
    have h1 : LinearIndependent F (LinearMap.single F (fun k => X.toGeo.Sec k) X.T ∘ f) := by
      have e : (LinearMap.single F (fun k => X.toGeo.Sec k) X.T ∘ f) = ((sysOf X Λ₀).V X.T).subtype ∘ v :=
        funext fun i => (hf i).symm
      rw [e]
      exact hv'
    have h2 := X.toGeo.linearIndependent_toExt E X.T m f h1.of_comp
    have h3 := h2.map' (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) X.T)
      (LinearMap.ker_eq_bot.2 (Pi.single_injective _))
    have e2 : (fun i => totExt X.toGeo E (v i)) =
        (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) X.T ∘ fun i => X.toGeo.toExt E X.T (f i)) := by
      funext i
      rw [hf i, totExt_single]
      rfl
    rw [e2]
    exact h3
  · intro j
    have hset : (totExt X.toGeo E '' ((sysOf X Λ₀).V j : Set (Tot X.toGeo))) =
        (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) j) ''
          (X.toGeo.toExt E j '' (X.V j : Set (X.toGeo.Sec j))) := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨_, ⟨y, y.2, rfl⟩, (totExt_single X.toGeo E j y).symm⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, totExt_single X.toGeo E j y⟩
    rw [hset, ← Submodule.map_span]
    refine Eq.trans ?_ (LinearMap.range_comp ((X.baseChange E).V j).subtype (LinearMap.single E _ j)).symm
    rw [Submodule.range_subtype]
    rfl

end GlobalTheory.HSShort
end
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuelSectionBaseChange_properties : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ) (E : Type) [Field E] [NumberField E] [Algebra F E], (∀ (m : ℕ) (v : Fin m → (sysOf X Λ₀).V X.T), LinearIndependent F v → LinearIndependent E fun i => totExt X.toGeo E (v i)) ∧ (∀ u x, shift (X.toGeo.baseChange E) (fun k => algebraMap F E (u k)) (totExt X.toGeo E x) = totExt X.toGeo E (shift X.toGeo u x)) ∧ ∀ j, Submodule.span E (totExt X.toGeo E '' (sysOf X Λ₀).V j) = LinearMap.range (incl (X.baseChange E) j) := by
  atlas_forward_decl GlobalTheory.HSShort.totExt_props
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem filV_symV_ker : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), ∀ a < X.T - X.D, filV X s (a + 1) ≤ filV X s a ∧ ∀ x : filV X s a, symV Co a x = 0 ↔ x.1 ∈ filV X s (a + 1) := by
  intro K _ _ X s hs δ Co a ha
  have haT : a ≤ X.T := by omega
  refine ⟨Submodule.comap_mono (Vanishing.Fil_anti (Nat.le_succ a)), fun x => ?_⟩
  have key : symV Co a x = 0 ↔ hs.sym (Nat.sub_add_cancel haT) (spaceV X s)
      ((X.V X.T).subtype.restrict (fun _ hx => hx) x) = 0 := by
    unfold symV
    rw [dif_pos haT]
    constructor
    · intro h
      funext α
      apply (Co.ev (X.T - a)).injective
      funext p
      have := congrFun h (α, p)
      simpa using this
    · intro h
      funext q
      simp [h]
  rw [key]
  exact Vanishing.sym_eq_zero_iff _ _ _ _ _ _ _ _ _ _ _

end GlobalTheory.HSCore
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem totFil_totSym_ker : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), ∀ a < X.T - X.D, totFil X s (a + 1) ≤ totFil X s a ∧ ∀ x : totFil X s a, totSym Co a x = 0 ↔ x.1 ∈ totFil X s (a + 1) := by
  intro K _ _ X s hs δ Co a ha
  obtain ⟨hle, hker⟩ := GlobalTheory.HSCore.filV_symV_ker K X s hs δ Co a ha
  refine ⟨Submodule.map_mono hle, fun x => ?_⟩
  let e := Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a)
  let y : filV X s a := e.symm x
  have hxy : e y = x := e.apply_symm_apply x
  have hx1 : x.1 = incl X X.T y.1 := by rw [← hxy]; rfl
  have : totSym Co a x = symV Co a y := rfl
  rw [this, hker y, hx1]
  constructor
  · intro h
    exact ⟨y.1, h, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [← incl_injective X X.T hzy]

end GlobalTheory.HSShort
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore.IntLift

variable {K : Type} [Field K] [NumberField K]

theorem mulPow_mem_global (G : Geo K) (s : Fin G.D → Fin G.N → K) {a j l : ℕ} (h : j + a = l)
    (α : MonoDeg (Fin G.D) a) {m : G.Sec j} (hm : m ∈ G.global j) : mulPow G s h α m ∈ G.global l := by
  obtain ⟨F, rfl⟩ := hm
  refine ⟨(Vanishing.powChart (isLB_tens G.K.isLB G.isLBA) G.isLB ((Nat.cast_add j a).symm.trans (congrArg _ h))).mul
    (H0.ofSec G.str ⊤ (monoSec (G.sec s) α)) F, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec]
  rfl

end GlobalTheory.HSCore.IntLift

namespace GlobalTheory.HSCore

end GlobalTheory.HSCore
end

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

namespace GlobalTheory.HSShort.GlobWord

theorem shift_single {K : Type} [Field K] [NumberField K] (G : Geo K) (j : ℕ) (u : Fin G.N → K) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext i
  cases i with
  | zero => rw [Pi.single_eq_of_ne (Nat.succ_ne_zero j).symm]; rfl
  | succ i =>
    show G.mulW i u ((Pi.single j m : Tot G) i) = _
    by_cases h : i = j
    · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun h' => h (Nat.succ_injective h')), map_zero]

theorem word_global : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (t j : ℕ) (u : Fin t → Fin G.N → K), ∀ x ∈ G.global j, ∃ x' ∈ G.global (j + t), word (shift G) u (Pi.single j x) = Pi.single (j + t) x' ∧ ∀ (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s) (δ : ℕ) (Co : Coord G hs δ) (p : Fin δ), Co.ev (j + t) (hs.res (j + t) x') p = (∏ q, ∑ k, u q k * Co.y p k) * Co.ev j (hs.res j x) p := by
  intro K _ _ G t j
  induction t with
  | zero =>
    intro u x hx
    exact ⟨x, hx, by simp [word], fun s hs δ Co p => by simp⟩
  | succ t ih =>
    intro u x hx
    obtain ⟨x', hx', hw, hr⟩ := ih (fun q => u q.succ) x hx
    refine ⟨G.mulW (j + t) (u 0) x', GlobalTheory.HilbertSamuel.Model.mulW_mem_global G (j + t) _ hx', ?_, fun s hs δ Co p => ?_⟩
    · unfold word at hw ⊢
      rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, hw]
      exact shift_single G (j + t) (u 0) x'
    · show Co.ev (j + t + 1) (hs.res (j + t + 1) (G.mulW (j + t) (u 0) x')) p = _
      rw [hs.res_mulW, Co.mul]
      beta_reduce
      rw [hr, Fin.prod_univ_succ, mul_assoc]

end GlobalTheory.HSShort.GlobWord
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productOfVectorMultiplications_global_residues : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (t j : ℕ) (u : Fin t → Fin G.N → K), ∀ x ∈ G.global j, ∃ x' ∈ G.global (j + t), word (shift G) u (Pi.single j x) = Pi.single (j + t) x' ∧ ∀ (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s) (δ : ℕ) (Co : Coord G hs δ) (p : Fin δ), Co.ev (j + t) (hs.res (j + t) x') p = (∏ q, ∑ k, u q k * Co.y p k) * Co.ev j (hs.res j x) p := by
  atlas_forward_decl GlobalTheory.HSShort.GlobWord.word_global
end

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

namespace GlobalTheory.HSShort

theorem exists_filV_mulPow {K : Type} [Field K] [NumberField K] (X : Data K) {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s}
    {δ : ℕ} (Co : Coord X.toGeo hs δ) {a : ℕ} (haT : a ≤ X.T) (α : MonoDeg (Fin X.D) a)
    (m : X.Sec (X.T - a)) (hg : m ∈ X.global (X.T - a)) :
    ∃ f : filV X s a, (f.1 : X.Sec X.T) = mulPow X.toGeo s (Nat.sub_add_cancel haT) α m ∧
      ∀ α' p, symV Co a f (α', p) = if α'.1 = α.1 then Co.ev (X.T - a) (hs.res (X.T - a) m) p else 0 := by
  have hh : X.T - a + a = X.T := Nat.sub_add_cancel haT
  have hgl := GlobalTheory.HSCore.IntLift.mulPow_mem_global X.toGeo s hh α hg
  obtain ⟨f, hfeq⟩ : ∃ f : X.V X.T, (f : X.Sec X.T) = mulPow X.toGeo s hh α m := ⟨⟨_, X.global_le _ le_rfl hgl⟩, rfl⟩
  have hfF : (f : X.Sec X.T) ∈ Fil (X.ideal s) a (spaceV X s) := by
    refine (mem_Fil).2 ⟨Submodule.mem_sup_left ?_, ?_⟩
    · rw [hfeq]; exact hgl
    · rw [hfeq]; exact vanishesTo_mulMono _ _ _ _ _ _
  refine ⟨⟨f, hfF⟩, hfeq, fun α' p => ?_⟩
  have key : hs.sym hh (spaceV X s) ((X.V X.T).subtype.restrict (p := filV X s a) (q := Fil (X.ideal s) a (spaceV X s))
      (fun _ hx => hx) ⟨f, hfF⟩) = Pi.single α (hs.res (X.T - a) m) :=
    Vanishing.sym_mulMono _ _ _ _ _ _ _ _ _ _ α (m : X.Sec (X.T - a)) _ hfeq
  unfold symV
  rw [dif_pos haT]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, LinearEquiv.coe_coe, LinearMap.coe_proj,
    Function.eval]
  rw [key]
  by_cases hα : α' = α
  · subst hα; simp
  · rw [if_neg (fun h => hα (Subtype.ext h)), Pi.single_eq_of_ne hα, map_zero]; rfl

theorem totSym_incl {K : Type} [Field K] [NumberField K] {X : Data K} {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s}
    {δ : ℕ} (Co : Coord X.toGeo hs δ) (a : ℕ) (f : filV X s a) (y : totFil X s a) (h : y.1 = incl X X.T f.1) :
    totSym Co a y = symV Co a f := by
  have : y = Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a) f := Subtype.ext h
  rw [this]
  exact congrArg (symV Co a) (LinearEquiv.symm_apply_apply _ f)

theorem totSym_mono : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), X.MulStable → ∀ a < X.T - X.D, ∀ (α : MonoDeg (Fin X.D) a) (l : Fin (X.T - a) → Fin X.N → K), ∀ m ∈ LinearMap.range (incl X 0), ∃ h : pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l m) ∈ totFil X s a, ∀ α' p, totSym Co a ⟨_, h⟩ (α', p) = if α'.1 = α.1 then (∏ q, ∑ k, l q k * Co.y p k) * totRes Co m p else 0 := by
  intro K _ _ X s hs δ Co _ a ha α l m hm
  obtain ⟨m₀, rfl⟩ := hm
  have haT : a ≤ X.T := by omega
  have hm₀ : (m₀ : X.Sec 0) ∈ X.global 0 := (SetLike.ext_iff.1 X.V_zero _).1 m₀.2
  have H : ∀ (t k : ℕ) (_ : 0 + t = k) (u : Fin t → Fin X.N → K), ∃ x' ∈ X.global k,
      word (shift X.toGeo) u (Pi.single 0 (m₀ : X.Sec 0)) = Pi.single k x' ∧ ∀ p,
        Co.ev k (hs.res k x') p = (∏ q, ∑ j, u q j * Co.y p j) * Co.ev 0 (hs.res 0 m₀) p := by
    intro t k h u
    subst h
    obtain ⟨x', h1, h2, h3⟩ := GlobalTheory.T.productOfVectorMultiplications_global_residues K X.toGeo t 0 u _ hm₀
    exact ⟨x', h1, h2, h3 s hs δ Co⟩
  obtain ⟨x', h1, h2, h3⟩ := H _ _ (Nat.zero_add _) l
  obtain ⟨f, hf, hsym⟩ := exists_filV_mulPow X Co haT α x' h1
  have e : pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l (incl X 0 m₀)) = incl X X.T f.1 := by
    change pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l (Pi.single 0 (m₀ : X.Sec 0))) =
      Pi.single X.T (f.1 : X.Sec X.T)
    rw [h2, hf]
    exact (GlobalTheory.T.hilbertSamuelSectionShift_comm_single_monomial K X.toGeo).2.2 s a _ _ _ α x'
  refine ⟨⟨f.1, f.2, e.symm⟩, fun α' p => ?_⟩
  rw [totSym_incl Co a f _ e, hsym, h3]
  have : totRes Co (incl X 0 m₀) = Co.ev 0 (hs.res 0 m₀) := by simp [totRes, incl]
  rw [this]

end GlobalTheory.HSShort
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuelFiltrationSymbol_monomial_product : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), X.MulStable → ∀ a < X.T - X.D, ∀ (α : MonoDeg (Fin X.D) a) (l : Fin (X.T - a) → Fin X.N → K), ∀ m ∈ LinearMap.range (incl X 0), ∃ h : pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l m) ∈ totFil X s a, ∀ α' p, totSym Co a ⟨_, h⟩ (α', p) = if α'.1 = α.1 then (∏ q, ∑ k, l q k * Co.y p k) * totRes Co m p else 0 := by
  atlas_forward_decl GlobalTheory.HSShort.totSym_mono
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore

theorem spaceP_le_filTop {K : Type} [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) :
    spaceP X s ≤ filTop X.str (X.adj X.T) X.U (X.ideal s) (X.T - X.D) := by
  unfold spaceP
  refine iSup_le fun α => ?_
  rintro _ ⟨m, -, rfl⟩
  exact vanishesTo_mulMono _ _ _ α _ m

theorem fil_spaceV_eq_spaceP (hF : FilMono) (K : Type) [Field K] [NumberField K] (X : Data K)
    (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (hn : IsNef K X.LA) (hb : IsBig K X.LA) :
    Fil (X.ideal s) (X.T - X.D) (spaceV X s) = spaceP X s := by
  apply le_antisymm
  · rintro f ⟨hfV, hfv⟩
    obtain ⟨g, hg, p, hp, rfl⟩ := Submodule.mem_sup.1 hfV
    have hpv : VanishesTo (X.ideal s) (X.T - X.D) p := spaceP_le_filTop X s hp
    have hgv : VanishesTo (X.ideal s) (X.T - X.D) g := by
      have : g = (g + p) - p := by abel
      rw [this]
      exact (filTop X.str (X.adj X.T) X.U (X.ideal s) (X.T - X.D)).sub_mem hfv hpv
    obtain ⟨m, hm, hgm⟩ := hF K X.toGeo hn hb s hs (X.T - X.D) X.D X.T (add_sub_D X) (Nat.le_refl _) g ⟨hg, hgv⟩
    refine (spaceP X s).add_mem ?_ hp
    rw [hgm]
    refine Submodule.sum_mem _ fun α _ => ?_
    unfold spaceP
    exact Submodule.mem_iSup_of_mem α ⟨m α, X.global_le X.D (by have := X.le_T; omega) (hm α), rfl⟩
  · intro f hf
    exact ⟨Submodule.mem_sup_right hf, spaceP_le_filTop X s hf⟩

theorem filP : FilMono → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K),
    X.IsGood s → IsNef K X.LA → IsBig K X.LA → Fil (X.ideal s) (X.T - X.D) (spaceV X s) = spaceP X s :=
  fun hF K _ _ X s hs hn hb => fil_spaceV_eq_spaceP hF K X s hs hn hb

end GlobalTheory.HSCore
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

variable {K : Type} [Field K] [NumberField K]

theorem monoDeg_succ_split {ι : Type} [Fintype ι] {a : ℕ} (β : MonoDeg ι (a + 1)) :
    ∃ (i : ι) (α : MonoDeg ι a), β.1 = α.1 + Finsupp.single i 1 := by
  have hne : β.1 ≠ 0 := fun h0 => by
    have := β.2
    rw [h0, Finsupp.degree_eq_sum] at this
    simp at this
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hne
  have hle : Finsupp.single i 1 ≤ β.1 := by
    rw [Finsupp.single_le_iff]
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
    omega
  have e : β.1 = (β.1 - Finsupp.single i 1) + Finsupp.single i 1 := (tsub_add_cancel_of_le hle).symm
  refine ⟨i, ⟨β.1 - Finsupp.single i 1, ?_⟩, e⟩
  have h2 := β.2
  rw [e, Finsupp.degree_eq_sum, Finset.sum_congr rfl (fun x _ => Finsupp.add_apply _ _ x),
    Finset.sum_add_distrib, ← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, Finsupp.degree_single] at h2
  omega

theorem mulPow_mem (X : Data K) (s : Fin X.D → Fin X.N → K) (hX : X.MulStable) :
    ∀ (a j l : ℕ) (h : j + a = l), l ≤ X.T → ∀ (α : MonoDeg (Fin X.D) a), ∀ m ∈ X.V j,
      mulPow X.toGeo s h α m ∈ X.V l := by
  intro a
  induction a with
  | zero =>
    intro j l h _ α m hm
    subst h
    have : mulPow X.toGeo s (rfl : j + 0 = j + 0) α m = m := by
      unfold mulPow
      exact mulMono_zero _ _ _ _ _ _
    rw [this]
    exact hm
  | succ a ih =>
    intro j l h hl β m hm
    subst h
    obtain ⟨i, α, e⟩ := monoDeg_succ_split β
    have hk : j + a < X.T := by omega
    have key : mulPow X.toGeo s (rfl : j + (a + 1) = j + (a + 1)) β m =
        X.mulW (j + a) (s i) (mulPow X.toGeo s (rfl : j + a = j + a) α m) := by
      unfold mulPow
      rw [Geo.mulW_apply]
      exact mulMono_succ _ _ _ α β i e _ _ _ m
    rw [key]
    exact hX.mem hk (s i) ⟨_, ih j (j + a) rfl (by omega) α m hm⟩

theorem mulPow_mem_and_spaceV_le : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K),
    X.MulStable → (∀ (a j l : ℕ) (h : j + a = l), l ≤ X.T → ∀ (α : MonoDeg (Fin X.D) a), ∀ m ∈ X.V j,
      mulPow X.toGeo s h α m ∈ X.V l) ∧ spaceV X s ≤ X.V X.T := by
  intro K _ _ X s hX
  refine ⟨mulPow_mem X s hX, ?_⟩
  refine sup_le (X.global_le X.T le_rfl) (iSup_le fun α => ?_)
  rintro _ ⟨m, hm, rfl⟩
  exact mulPow_mem X s hX _ _ _ _ le_rfl α m hm

end GlobalTheory.HSCore
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem totFil_deepest : FilMono → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K), X.IsGood s → IsNef K X.LA → IsBig K X.LA → X.MulStable → totFil X s (X.T - X.D) = ⨆ α : MonoDeg (Fin X.D) (X.T - X.D), (LinearMap.range (incl X X.D)).map (pw (shift X.toGeo) s α.1) := by
  intro hF K _ _ X s hs hn hb hm
  have hP := filP hF K X s hs hn hb
  have hVT : spaceP X s ≤ X.V X.T := le_sup_right.trans (mulPow_mem_and_spaceV_le K X s hm).2
  have hL : totFil X s (X.T - X.D) = (spaceP X s).map (LinearMap.single K (fun j => X.Sec j) X.T) := by
    show ((Fil (X.ideal s) (X.T - X.D) (spaceV X s)).comap (X.V X.T).subtype).map
        (LinearMap.single K _ X.T ∘ₗ (X.V X.T).subtype) = _
    rw [hP, Submodule.map_comp, Submodule.map_comap_subtype, inf_of_le_right hVT]
  have hR : ∀ α : MonoDeg (Fin X.D) (X.T - X.D),
      (LinearMap.range (incl X X.D)).map (pw (shift X.toGeo) s α.1) =
        ((X.V X.D).map (mulPow X.toGeo s (add_sub_D X) α)).map (LinearMap.single K (fun j => X.Sec j) X.T) := by
    intro α
    have he : pw (shift X.toGeo) s α.1 ∘ₗ LinearMap.single K (fun j => X.Sec j) X.D =
        LinearMap.single K (fun j => X.Sec j) X.T ∘ₗ mulPow X.toGeo s (add_sub_D X) α := by
      refine LinearMap.ext fun m => ?_
      simp only [LinearMap.comp_apply, LinearMap.coe_single]
      exact (GlobalTheory.T.hilbertSamuelSectionShift_comm_single_monomial K X.toGeo).2.2 s (X.T - X.D) X.D X.T (add_sub_D X) α m
    rw [show incl X X.D = LinearMap.single K (fun j => X.Sec j) X.D ∘ₗ (X.V X.D).subtype from rfl,
      LinearMap.range_comp, Submodule.range_subtype, ← Submodule.map_comp, he, Submodule.map_comp]
  rw [hL, iSup_congr hR, ← Submodule.map_iSup]
  rfl

end GlobalTheory.HSShort
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuelVanishingFiltration_deepest_step_span : FilMono → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K), X.IsGood s → IsNef K X.LA → IsBig K X.LA → X.MulStable → totFil X s (X.T - X.D) = ⨆ α : MonoDeg (Fin X.D) (X.T - X.D), (LinearMap.range (incl X X.D)).map (pw (shift X.toGeo) s α.1) := by
  atlas_forward_decl GlobalTheory.HSShort.totFil_deepest
end

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem flatAt_of_simpleAt : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ →
    ∀ (δ : ℕ) (f : MvPolynomial (Fin (X.D + 1) × Fin X.N) F) (Q : MvPolynomial (Fin X.D × Fin X.N) F),
      (∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E),
        aeval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → SimpleAt X.toTuple δ f E s) →
      ∀ s : Fin X.D → Fin X.N → F, eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → (sysOf X Λ₀).FlatAt δ f s := by
  intro hQ F _ _ X Λ₀ hX δ f Q hS s hs
  have hF : SimpleAt X.toTuple δ f F s := hS F s (by simpa [MvPolynomial.coe_aeval_eq_eval] using hs)
  obtain ⟨E, iE, nE, iFE, iEE, htow, hsp⟩ := GlobalTheory.HSCore.exists_split F X.toTuple F s hF.good
  have heq : (fun i k => @algebraMap F E _ _ iEE (s i k)) = fun i k => @algebraMap F E _ _ iFE (s i k) := by
    funext i k
    rw [@IsScalarTower.algebraMap_apply F F E _ _ _ _ iEE iFE htow (s i k)]
    rfl
  rw [heq] at hsp
  clear heq htow iEE
  have hval : aeval (fun p : Fin X.D × Fin X.N => algebraMap F E (s p.1 p.2)) Q =
      algebraMap F E (eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q) := by
    exact (MvPolynomial.eval₂_comp_left (algebraMap F E) (RingHom.id F) _ Q).symm
  have hSE : SimpleAt X.toTuple δ f E (fun i k => algebraMap F E (s i k)) :=
    hS E _ (by rw [hval]; exact (map_ne_zero _).2 hs)
  have hgood : (X.baseChange E).IsGood (fun i k => algebraMap F E (s i k)) := Geo.isGood_baseChange_iff.2 hSE.good
  obtain ⟨Co, c, hc, hspec⟩ := GlobalTheory.T.exists_coordinates_specialisedForm_prod_linearForms F X.toGeo E _ hgood δ f hsp hSE
  have hnef₂ := nef_big_second_baseChange F X E hX.nef₂ hX.big₂
  have hnefA := GlobalTheory.HSCore.nef_big_baseChange F X E hX.nef hX.big
  have hms : (X.baseChange E).MulStable :=
    (GlobalTheory.HilbertSamuel.Data.complexify_statement F X (fun _ => X.beta) hX.totallyComplex
      (fun _ => one_pos.trans_le X.one_le_beta) hX.mulStable hX.mulBound).2 E
  have hFM : FilMono := GlobalTheory.HSCore.filMono_of_kerRes (GlobalTheory.HSKerRes.kerRes hQ)
  obtain ⟨hind, hmul, hspan⟩ := GlobalTheory.T.hilbertSamuelSectionBaseChange_properties F X Λ₀ E
  obtain ⟨hcomm, -, -⟩ := GlobalTheory.T.hilbertSamuelSectionShift_comm_single_monomial E (X.toGeo.baseChange E)
  have honto := GlobalTheory.T.hilbertSamuelDegreeZeroResidues_range_eq_top hQ E (X.baseChange E) _ hgood δ Co hnef₂.1 hnef₂.2
  have hker := totFil_totSym_ker E (X.baseChange E) _ hgood δ Co
  have hmono := GlobalTheory.T.hilbertSamuelFiltrationSymbol_monomial_product E (X.baseChange E) _ hgood δ Co hms
  have hdiv := GlobalTheory.T.hilbertSamuelVanishingFiltration_deepest_step_span hFM E (X.baseChange E) _ hgood hnefA.1 hnefA.2 hms
  let Φ : (sysOf X Λ₀).Flat E (Tot (X.toGeo.baseChange E)) (fun i k => algebraMap F E (s i k)) δ :=
    { ι := totExt X.toGeo E
      indep := hind
      mul := shift (X.toGeo.baseChange E)
      comm := hcomm
      mul_ι := hmul
      y := Co.y
      y_ne := Co.y_ne
      res := totRes (X := X.baseChange E) Co
      onto := by rw [hspan 0]; exact honto
      U := totFil (X.baseChange E) (fun i k => algebraMap F E (s i k))
      sym := totSym (X := X.baseChange E) Co
      le := fun a ha => (hker a ha).1
      ker := fun a ha => (hker a ha).2
      mono := fun a ha α l m hm => hmono a ha α l m (by rw [hspan 0] at hm; exact hm)
      div := by rw [hspan]; exact hdiv }
  exact ⟨E, Tot (X.toGeo.baseChange E), inferInstance, inferInstance, inferInstance, inferInstance, Φ, c, hc, hspec⟩

end GlobalTheory.HSShort
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuel_filtration_at_good_sections : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ → ∀ (δ : ℕ) (f : MvPolynomial (Fin (X.D + 1) × Fin X.N) F) (Q : MvPolynomial (Fin X.D × Fin X.N) F), (∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E), aeval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → SimpleAt X.toTuple δ f E s) → ∀ s : Fin X.D → Fin X.N → F, eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → (sysOf X Λ₀).FlatAt δ f s := by
  atlas_forward_decl GlobalTheory.HSShort.flatAt_of_simpleAt
end
