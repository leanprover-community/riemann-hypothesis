import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.ChartCompat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def liftF {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over, spMap_comp_ring]; rfl)

theorem liftF_fst {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _

theorem liftF_snd {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _

theorem liftF_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) : liftF z = spMap φ.toRingHom ≫ liftF y := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftF_fst, liftF_fst, h.1]
  · rw [Category.assoc, liftF_snd, liftF_snd, spMap_comp_ring]
    congr 1
    ext a
    simp

theorem liftF_bor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ}
    {y z : FrPt Xo c S} (h : FrBor t y z) : liftF z = liftF y := by
  apply pullback.hom_ext
  · rw [liftF_fst, liftF_fst, h.1]
  · rw [liftF_snd, liftF_snd]

theorem liftF_gen (h : GenFrEx Xo c) (Z : Comp Xo c) :
    liftF (genFr h Z) = spMap (algebraMap (kap Z) (Om Z)) ≫ genSp Z := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftF_fst, (isGenFr_genFr h Z).1]; rfl
  · rw [Category.assoc, liftF_snd, IsScalarTower.algebraMap_eq c.F (kap Z) (Om Z), ← spMap_comp_ring]
    congr 1
    exact Spec.map_preimage (genSp Z ≫ strK)

theorem liftF_gen_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (p : Sp (Om Z)) :
    (liftF (genFr h Z)) p = genPt Z := by
  rw [liftF_gen, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

theorem closure_genPt' (Z : Comp Xo c) : closure {genPt Z} = (Z : Set (Xo.XF c)) :=
  (IsIrreducible.genericPoint_closure_eq (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c)))).trans
    (isClosed_of_mem_irreducibleComponents _ Z.2).closure_eq

theorem chart_mem {h : GenFrEx Xo c} (C : FChart h) (p : Sp C.R) : (liftF C.y) p ∈ (C.Z : Set (Xo.XF c)) := by
  have hcl : IsClosed ((liftF C.y) ⁻¹' (C.Z : Set (Xo.XF c))) :=
    (isClosed_of_mem_irreducibleComponents _ C.Z.2).preimage (liftF C.y).continuous
  let q : Sp (Om C.Z) := (⊥ : PrimeSpectrum (Om C.Z))
  have h1 : (liftF C.y) (spMap C.R.val.toRingHom q) = genPt C.Z := by
    rw [← Scheme.Hom.comp_apply, ← liftF_map C.gen, liftF_bor C.bor, liftF_gen_apply]
  have h2 : spMap C.R.val.toRingHom q ∈ (liftF C.y) ⁻¹' (C.Z : Set (Xo.XF c)) := by
    show (liftF C.y) (spMap C.R.val.toRingHom q) ∈ (C.Z : Set (Xo.XF c))
    rw [h1, ← closure_genPt']
    exact subset_closure rfl
  have h3 : spMap C.R.val.toRingHom q ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro a ha
    have ha' : C.R.val a = 0 := ha
    have : a = 0 := Subtype.ext ha'
    rw [this]
    exact Ideal.zero_mem _
  exact h3.mem_closed hcl h2

theorem comp_eq {h : GenFrEx Xo c} (C C' : FChart h) (ψ : C'.R →ₐ[c.F] Om C.Z) (z : FrPt Xo c (Om C.Z))
    (t : Ix Dw → (Om C.Z)ˣ) (hz : FrMap ψ C'.y z) (hb : FrBor t z C.yg) : C.Z = C'.Z := by
  let q : Sp (Om C.Z) := (⊥ : PrimeSpectrum (Om C.Z))
  have h1 : genPt C.Z ∈ (C'.Z : Set (Xo.XF c)) := by
    rw [← liftF_gen_apply h C.Z q, ← liftF_bor C.bor, liftF_bor hb, liftF_map hz, Scheme.Hom.comp_apply]
    exact chart_mem C' _
  have h2 : (C.Z : Set (Xo.XF c)) ⊆ (C'.Z : Set (Xo.XF c)) := by
    rw [← closure_genPt']
    exact closure_minimal (Set.singleton_subset_iff.2 h1) (isClosed_of_mem_irreducibleComponents _ C'.Z.2)
  exact Subtype.ext (Set.Subset.antisymm h2 (C.Z.2.2 C'.Z.2.1 h2))

theorem wchar_mul {J S : Type} [Fintype J] [CommRing S] (e : J → ℕ) (t t' : J → Sˣ) :
    wchar e (t * t') = wchar e t * wchar e t' := by
  simp [wchar, mul_pow, Finset.prod_mul_distrib]

theorem wchar_map {J K S T : Type} [Fintype J] [Field K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (φ : S →ₐ[K] T) (e : J → ℕ) (t : J → Sˣ) :
    wchar e (fun i => Units.map (φ : S →* T) (t i)) = φ (wchar e t) := by
  simp [wchar]

theorem away_lift {K R T : Type} [Field K] [CommRing R] [Algebra K R] [Field T] [Algebra K T] (g : R)
    (φ : R →ₐ[K] T) (hφ : φ g ≠ 0) :
    ∃ m : Localization.Away g →ₐ[K] T, m.comp (IsScalarTower.toAlgHom K R (Localization.Away g)) = φ := by
  have hu : ∀ m : Submonoid.powers g, IsUnit (φ m) := by
    rintro ⟨_, n, rfl⟩
    simpa using Ne.isUnit (pow_ne_zero n hφ)
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers g) hu, ?_⟩
  ext a
  simp

theorem away_inj {K R T : Type} [Field K] [CommRing R] [Algebra K R] [CommRing T] [Algebra K T] (g : R)
    (m : Localization.Away g →ₐ[K] T)
    (h : Function.Injective (m.comp (IsScalarTower.toAlgHom K R (Localization.Away g)))) : Function.Injective m := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨⟨a, n⟩, hm⟩ := IsLocalization.surj (Submonoid.powers g) s
  have h1 : m (algebraMap R _ a) = 0 := by
    rw [← hm, map_mul, hs, zero_mul]
  have h3 : a = 0 := (injective_iff_map_eq_zero _).1 h a h1
  dsimp only at hm
  rw [h3, map_zero] at hm
  exact (IsLocalization.map_units _ n).mul_left_eq_zero.1 hm

end GlobalTheory.Reg.ChartCompat

namespace GlobalTheory.Reg
open ChartCompat

set_option maxHeartbeats 1000000 in
theorem FChart.compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∀ (C C' : FChart h) (L : Type) [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) (ψ' : C'.R →ₐ[c.F] L) (z z' : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrMap ψ' C'.y z' → FrBor t z z' → C.Z = C'.Z ∧ ∀ (e : Ix Dw → ℕ) (b : ∀ Z : Comp Xo c, Om Z) (hb : wchar e C.t * b C.Z ∈ C.R) (hb' : wchar e C'.t * b C'.Z ∈ C'.R), ψ' ⟨_, hb'⟩ = wchar e t * ψ ⟨_, hb⟩ := by
  intro E _ _ _ H Dw l Xo c hev h C C' L _ _ ψ ψ' z z' t hz hz' hbor
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c
  have U := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c
  obtain ⟨g, hg, hopn⟩ := C'.opn C.R L ψ C.y z hz ⟨ψ', z', t⁻¹, hz', (G L).2.2.1 t z z' hbor⟩
  have hg0 : g ≠ 0 := fun e => hg (by rw [e, map_zero])
  have hg1 : C.R.val g ≠ 0 := fun e => hg0 (Subtype.ext e)
  have hZ : C.Z = C'.Z := by
    obtain ⟨ψ0, z0, t0, h1, h2⟩ := hopn (Om C.Z) C.R.val (Ne.isUnit hg1) C.yg C.gen
    exact comp_eq C C' ψ0 z0 t0 h1 h2
  refine ⟨hZ, ?_⟩
  obtain ⟨Z, R, sm, frac, y, yg, tC, gen, bor, mono, opn⟩ := C
  obtain ⟨Z', R', sm', frac', y', yg', tC', gen', bor', mono', opn'⟩ := C'
  dsimp only at *
  subst hZ
  intro e b hb hb'
  let S := Localization.Away g
  let lam : R →ₐ[c.F] S := IsScalarTower.toAlgHom c.F R S
  have hlam : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨mu, hmu⟩ : ∃ m : S →ₐ[c.F] Om Z, m.comp lam = R.val := away_lift g R.val hg1
  obtain ⟨nu, hnu⟩ : ∃ m : S →ₐ[c.F] L, m.comp lam = ψ := away_lift g ψ hg
  have hinj : Function.Injective mu := away_inj g mu (by rw [hmu]; exact Subtype.val_injective)
  obtain ⟨w, hw⟩ := hev.bc R S lam y
  obtain ⟨φ, v, s, hv, hs⟩ := hopn S lam hlam w hw

  obtain ⟨vmu, hvmu⟩ := hev.bc S (Om Z) mu v
  have m1 : FrMap mu w yg := frMap_cancel _ _ _ lam mu y w yg hw (by rw [hmu]; exact gen)
  have b1 := frBorBC _ _ mu s v w vmu yg hs hvmu m1
  have m2 : FrMap (mu.comp φ) y' vmu := frMap_trans _ _ _ φ mu y' v vmu hv hvmu
  have b2 := (G _).2.1 _ _ _ _ _ b1 ((G _).2.1 _ _ _ _ _ ((G _).2.2.1 _ _ _ bor) bor')
  have e1 : mu.comp φ = R'.val := mono' _ _ _ _ _ _ m2 gen' b2
  have e2 : vmu = yg' := (U _ _ R'.val y').1 _ _ (e1 ▸ m2) gen'
  subst e2
  have e3 : tC = tC' * fun i => Units.map (mu : S →* Om Z) (s i) :=
    (G _).2.2.2 _ _ _ _ bor ((G _).2.1 _ _ _ _ _ bor' b1)

  obtain ⟨vnu, hvnu⟩ := hev.bc S L nu v
  have m3 : FrMap nu w z := frMap_cancel _ _ _ lam nu y w z hw (by rw [hnu]; exact hz)
  have b3 := frBorBC _ _ nu s v w vnu z hs hvnu m3
  have m4 : FrMap (nu.comp φ) y' vnu := frMap_trans _ _ _ φ nu y' v vnu hv hvnu
  have b4 := (G _).2.1 _ _ _ _ _ b3 hbor
  have e4 : nu.comp φ = ψ' := mono' _ _ _ _ _ _ m4 hz' b4
  have e5 : vnu = z' := (U _ _ ψ' y').1 _ _ (e4 ▸ m4) hz'
  subst e5
  have e6 : (fun i => Units.map (nu : S →* L) (s i)) * t = 1 :=
    (G _).2.2.2 _ _ _ _ b4 ((G _).1 _)
  have e7 : lam ⟨_, hb⟩ = wchar e s * φ ⟨_, hb'⟩ := by
    apply hinj
    have a1 : mu (lam ⟨_, hb⟩) = wchar e tC * b Z := DFunLike.congr_fun hmu ⟨_, hb⟩
    have a2 : mu (φ ⟨_, hb'⟩) = wchar e tC' * b Z := DFunLike.congr_fun e1 ⟨_, hb'⟩
    have a0 : wchar e tC = wchar e tC' * mu (wchar e s) :=
      (congrArg (wchar e) e3).trans ((wchar_mul _ _ _).trans (congrArg _ (wchar_map mu e s)))
    rw [map_mul, a1, a2]
    linear_combination (b Z) * a0
  have a3 : ψ ⟨_, hb⟩ = nu (wchar e s) * ψ' ⟨_, hb'⟩ := by
    rw [← hnu, ← e4, AlgHom.comp_apply, AlgHom.comp_apply, e7, map_mul]
  have a4 : nu (wchar e s) * wchar e t = 1 := by
    rw [← wchar_map, ← wchar_mul, e6]
    simp [wchar]
  linear_combination (-(wchar e t)) * a3 - (ψ' ⟨_, hb'⟩) * a4

end GlobalTheory.Reg
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.values_eq_of_common_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∀ (C C' : FChart h) (L : Type) [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) (ψ' : C'.R →ₐ[c.F] L) (z z' : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrMap ψ' C'.y z' → FrBor t z z' → C.Z = C'.Z ∧ ∀ (e : Ix Dw → ℕ) (b : ∀ Z : Comp Xo c, Om Z) (hb : wchar e C.t * b C.Z ∈ C.R) (hb' : wchar e C'.t * b C'.Z ∈ C'.R), ψ' ⟨_, hb'⟩ = wchar e t * ψ ⟨_, hb⟩ := by
  first | exact @GlobalTheory.Reg.FChart.compat | exact GlobalTheory.Reg.FChart.compat | (intros; apply GlobalTheory.Reg.FChart.compat <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.Reg.SecGlue

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def liftF {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over, spMap_comp_ring]; rfl)

theorem liftF_fst {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = y.x :=
  pullback.lift_fst _ _ _

theorem liftF_snd {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = spMap (algebraMap c.F S) :=
  pullback.lift_snd _ _ _

theorem liftF_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) (h : z.x = spMap φ.toRingHom ≫ y.x) :
    liftF z = spMap φ.toRingHom ≫ liftF y := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftF_fst, liftF_fst, h]
  · rw [Category.assoc, liftF_snd, liftF_snd, spMap_comp_ring]
    congr 1
    exact RingHom.ext fun r => (φ.commutes r).symm

theorem liftF_congr {S : Type} [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S) (h : z.x = y.x) :
    liftF z = liftF y := by
  apply pullback.hom_ext
  · rw [liftF_fst, liftF_fst, h]
  · rw [liftF_snd, liftF_snd]

theorem liftF_gen (h : GenFrEx Xo c) (Z : Comp Xo c) :
    liftF (genFr h Z) = spMap (algebraMap (kap Z) (Om Z)) ≫ genSp Z := by
  have e : spMap (algebraMap c.F (kap Z)) = genSp Z ≫ strK := Spec.map_preimage _
  apply pullback.hom_ext
  · rw [liftF_fst, (isGenFr_genFr h Z).1, Category.assoc]; rfl
  · rw [liftF_snd, Category.assoc]
    erw [← e]
    rw [spMap_comp_ring]

theorem liftF_gen_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (p : Sp (Om Z)) :
    liftF (genFr h Z) p = genPt Z := by
  rw [liftF_gen, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

theorem closure_gen (Z : Comp Xo c) : closure {genPt Z} = (Z : Set (Xo.XF c)) :=
  ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents _ Z.2)).def

theorem chart_comp {h : GenFrEx Xo c} (Z : Comp Xo c) (C : FChart h) (ψ : C.R →ₐ[c.F] Om Z)
    (z : FrPt Xo c (Om Z)) (t : Ix Dw → (Om Z)ˣ) (h1 : FrMap ψ C.y z) (h2 : FrBor t z (genFr h Z)) : C.Z = Z := by
  have e1 : liftF (genFr h Z) = spMap ψ.toRingHom ≫ liftF C.y := by
    rw [liftF_congr _ _ h2.1, liftF_map ψ _ _ h1.1]
  have e2 : liftF (genFr h C.Z) = spMap C.R.val.toRingHom ≫ liftF C.y := by
    rw [← liftF_congr _ _ C.bor.1, liftF_map _ _ _ C.gen.1]
  let p : Sp (Om Z) := IsLocalRing.closedPoint (Om Z)
  let p' : Sp (Om C.Z) := IsLocalRing.closedPoint (Om C.Z)
  have f1 := liftF_gen_apply h Z p
  have f2 := liftF_gen_apply h C.Z p'
  rw [e1, Scheme.Hom.comp_apply] at f1
  rw [e2, Scheme.Hom.comp_apply] at f2
  have hs : (spMap C.R.val.toRingHom p' : Sp C.R) ⤳ spMap ψ.toRingHom p := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro x hx
    have hx' : (x : Om C.Z) ∈ IsLocalRing.maximalIdeal (Om C.Z) := hx
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hx'
    have : x = 0 := Subtype.ext hx'
    rw [this]
    exact Ideal.zero_mem _
  have hs' := hs.map (liftF C.y).continuous
  rw [f1, f2] at hs'
  have hm : genPt Z ∈ (C.Z : Set (Xo.XF c)) := by
    rw [← closure_gen]; exact hs'.mem_closure
  have hsub : (Z : Set (Xo.XF c)) ⊆ C.Z := by
    rw [← closure_gen Z]
    exact closure_minimal (Set.singleton_subset_iff.2 hm) (isClosed_of_mem_irreducibleComponents _ C.Z.2)
  exact Subtype.ext (Set.Subset.antisymm (Z.2.2 C.Z.2.1 hsub) hsub)

theorem wchar_mul {S : Type} [CommRing S] (e : Ix Dw → ℕ) (t t' : Ix Dw → Sˣ) :
    wchar e (t * t') = wchar e t * wchar e t' := by
  simp only [wchar, Pi.mul_apply, Units.val_mul, mul_pow, Finset.prod_mul_distrib]

theorem wchar_one {S : Type} [CommRing S] (e : Ix Dw → ℕ) : wchar e (1 : Ix Dw → Sˣ) = 1 := by
  simp [wchar]

theorem wchar_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (e : Ix Dw → ℕ) (t : Ix Dw → Sˣ) :
    wchar e (fun i => Units.map (φ : S →* T) (t i)) = φ (wchar e t) := by
  simp [wchar]

theorem eq_of_fields {K S : Type} [Field K] [CommRing S] [IsReduced S] [Algebra K S] (s s' : S)
    (hs : ∀ (L : Type) [Field L] [Algebra K L] (χ : S →ₐ[K] L), χ s = χ s') : s = s' := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro P hP
  have := hs (FractionRing (S ⧸ P))
    ((IsScalarTower.toAlgHom K (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ K P))
  exact Ideal.Quotient.eq.1 (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P)) this)

section Val

variable {h : GenFrEx Xo c} {e : Ix Dw → ℕ} {b : ∀ Z : Comp Xo c, Om Z}
  (hb : ∀ C : FChart h, wchar e C.t * b C.Z ∈ C.R)

def Val {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (C : FChart h) (ψ : C.R →ₐ[c.F] S) (z : FrPt Xo c S) (t : Ix Dw → Sˣ),
    FrMap ψ C.y z ∧ FrBor t z y ∧ v = wchar e t * ψ ⟨_, hb C⟩

theorem val_unique (hl : EvLaws Xo c) {L : Type} [Field L] [Algebra c.F L] {y : FrPt Xo c L} {v v' : L}
    (h1 : Val hb y v) (h2 : Val hb y v') : v = v' := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨C', ψ', z', t', hz', ht', rfl⟩ := h2
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L
  have := (GlobalTheory.T.values_eq_of_common_point E H Dw l Xo c hl h C C' L ψ ψ' z z' _ hz hz'
    (hmul _ _ _ _ _ ht (hinv _ _ _ ht'))).2 e b (hb C) (hb C')
  rw [this, ← mul_assoc, ← wchar_mul, mul_comm t, mul_inv_cancel_left]

theorem val_map (hl : EvLaws Xo c) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {y' : FrPt Xo c T} (hy : FrMap φ y y') {v : S} (h1 : Val hb y v) :
    Val hb y' (φ v) := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨z', hz'⟩ := hl.bc S T φ z
  refine ⟨C, φ.comp ψ, z', _, frMap_trans _ _ _ ψ φ _ _ _ hz hz', frBorBC _ _ φ t z y z' y' ht hz' hy, ?_⟩
  rw [wchar_map, map_mul]; rfl

theorem val_bor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S}
    (hy : FrBor t y y') {v : S} (h1 : Val hb y v) : Val hb y' (wchar e t * v) := by
  obtain ⟨C, ψ, z, t₀, hz, ht, rfl⟩ := h1
  refine ⟨C, ψ, z, t₀ * t, hz, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c S).2.1 _ _ _ _ _ ht hy, ?_⟩
  rw [wchar_mul]; ring

theorem val_ex (hA : Atlas h) {L : Type} [Field L] [Algebra c.F L] (y : FrPt Xo c L) : ∃ v, Val hb y v := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA L y
  exact ⟨_, C, ψ, z, t, h1, h2, rfl⟩

theorem val_gen (hA : Atlas h) (Z : Comp Xo c) : Val hb (genFr h Z) (b Z) := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA _ (genFr h Z)
  obtain rfl := chart_comp Z C ψ z t h1 h2
  refine ⟨C, C.R.val, C.yg, C.t⁻¹, C.gen, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.2.1 _ _ _ C.bor, ?_⟩
  show b C.Z = wchar e C.t⁻¹ * (wchar e C.t * b C.Z)
  rw [← mul_assoc, ← wchar_mul, inv_mul_cancel, wchar_one, one_mul]

def Rep {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (g s : S) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (χ : S →ₐ[c.F] L) (w : FrPt Xo c L) (v : L),
    FrMap χ y w → Val hb w v → χ g * v = χ s

theorem exists_rep (hl : EvLaws Xo c) (hA : Atlas h) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ s, Rep hb y 1 s := by
  let I : Ideal S :=
    { carrier := {g | ∃ s, Rep hb y g s}
      zero_mem' := ⟨0, fun L _ _ χ w v _ _ => by simp⟩
      add_mem' := by
        rintro g g' ⟨s, hs⟩ ⟨s', hs'⟩
        exact ⟨s + s', fun L _ _ χ w v h1 h2 => by
          rw [map_add, map_add, add_mul, hs L χ w v h1 h2, hs' L χ w v h1 h2]⟩
      smul_mem' := by
        rintro r g ⟨s, hs⟩
        exact ⟨r * s, fun L _ _ χ w v h1 h2 => by
          rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hs L χ w v h1 h2]⟩ }
  by_contra hne
  have hI : I ≠ ⊤ := fun hI => hne ((Ideal.eq_top_iff_one I).1 hI)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  have := hP.isPrime
  let χ₀ : S →ₐ[c.F] FractionRing (S ⧸ P) :=
    (IsScalarTower.toAlgHom c.F (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ c.F P)
  obtain ⟨w₀, hw₀⟩ := hl.bc _ _ χ₀ y
  obtain ⟨C, ψ₀, z₀, t₀, h1, h2⟩ := hA _ w₀
  obtain ⟨g, hg, hloc⟩ := C.opn S _ χ₀ y w₀ hw₀ ⟨ψ₀, z₀, t₀, h1, h2⟩
  let lam : S →ₐ[c.F] Localization.Away g := IsScalarTower.toAlgHom c.F S _
  have hu : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨w', hw'⟩ := hl.bc _ _ lam y
  obtain ⟨ψ, z, t, h3, h4⟩ := hloc _ lam hu w' hw'
  have hv : Val hb w' (wchar e t * ψ ⟨_, hb C⟩) := ⟨C, ψ, z, t, h3, h4, rfl⟩
  generalize wchar e t * ψ ⟨_, hb C⟩ = u at hv
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g u
  have hmem : g ^ (n + 1) ∈ I := by
    refine ⟨g * a, fun L _ _ χ w v h5 h6 => ?_⟩
    by_cases hχ : χ g = 0
    · simp [hχ]
    · let mu : Localization.Away g →ₐ[c.F] L :=
        IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := χ) (by
          rintro ⟨_, k, rfl⟩
          simpa using (IsUnit.mk0 _ hχ).pow k)
      have hmu' : ∀ x, mu (algebraMap S _ x) = χ x := fun x => by
        simp [mu]
      have hmu : mu.comp lam = χ := AlgHom.ext hmu'
      have h7 : FrMap mu w' w := frMap_cancel _ _ _ lam mu y w' w hw' (by rw [hmu]; exact h5)
      have h8 := val_unique hb hl h6 (val_map hb hl mu h7 hv)
      have h9 := congrArg mu ha
      rw [map_mul, map_pow, hmu', hmu'] at h9
      rw [h8, map_mul, map_pow, ← h9]
      ring
  have hgP : g ∈ P := this.mem_of_pow_mem _ (hIP hmem)
  apply hg
  show algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P g) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hgP, map_zero]

end Val

theorem exists_sec_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, wchar (ex Dw a n) C.t * b C.Z ∈ C.R) → ∃ g ∈ sec Xo c a n, ∀ Z, evC h Z g = b Z := by
  intro E _ _ _ H Dw l Xo c hl h hA a n b hb
  have hred : ∀ p : TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  choose g hg using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_rep hb hl hA y
  have hg' : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (L : Type) [Field L] [Algebra c.F L] (χ : p.R →ₐ[c.F] L)
      (w : FrPt Xo c L) (v : L), FrMap χ y w → Val hb w v → χ (g p y) = v := by
    intro p y L _ _ χ w v h1 h2
    rw [← hg p y L χ w v h1 h2, map_one, one_mul]
  refine ⟨g, ⟨fun p q φ y z hz => ?_, fun p t y y' hy => ?_⟩, fun Z => ?_⟩
  · have := hred q
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ z
    obtain ⟨v, hv⟩ := val_ex hb hA w
    rw [hg' q z L χ w v hw hv]
    exact (hg' p y L (χ.comp φ) w v (frMap_trans _ _ _ φ χ y z w hz hw) hv).symm
  · have := hred p
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ y
    obtain ⟨w', hw'⟩ := hl.bc _ _ χ y'
    obtain ⟨v, hv⟩ := val_ex hb hA w
    have hv' := val_bor hb (frBorBC _ _ χ t y y' w w' hy hw hw') hv
    rw [hg' p y' L χ w' _ hw' hv', map_mul, hg' p y L χ w v hw hv, wchar_map]
  · have hh := hl.test _ (genFr h Z)
    unfold evC evR evalAt
    rw [dif_pos hh]
    exact hg' _ _ _ _ _ _ hh.choose_spec.choose_spec.choose_spec (val_gen hb hA Z)

end GlobalTheory.Reg.SecGlue
end
end
