module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties

@[expose] public section

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

attribute [local instance 1100] Subalgebra.algebra in
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

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
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
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
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
attribute [local instance 1100] Subalgebra.algebra OreLocalization.instAlgebra in

end GlobalTheory.Reg
