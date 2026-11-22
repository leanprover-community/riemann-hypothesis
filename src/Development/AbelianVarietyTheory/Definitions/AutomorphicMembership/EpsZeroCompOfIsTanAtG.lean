module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Pairing

variable {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X} {v : Sp (DualNumber k) ⟶ t.G.left}

theorem epsZero_comp_of_isTanAtG (hv : IsTanAtG t x v) : sec (epsZero k) ≫ v = x ≫ unitSec t.G :=
  hv.2

def tanForm (hv : IsTanAtG t x v) :
    (Scheme.Modules.pullback x).obj (omega t.G) ⟶ GlobalTheory.structureModule (Sp k) :=
  baseMap (π := t.G.hom) (φ := v) (f := x) (sec_hom (epsZero k)) hv.1 (epsZero_comp_of_isTanAtG t hv) ≫ (epsIso k).hom

def tanEv (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(omega t.G, V)) : k :=
  (Scheme.ΓSpecIso (.of k)).hom ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s))

theorem tanEv_add (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (s s' : Γ(omega t.G, V)) :
    tanEv t hv h (s + s') = tanEv t hv h s + tanEv t hv h s' := by
  simp only [tanEv, map_add (f := _)]
  exact map_add (Scheme.ΓSpecIso (.of k)).hom.hom _ _

theorem tanEv_smul (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, V)) (s : Γ(omega t.G, V)) :
    tanEv t hv h (a • s) = (Scheme.ΓSpecIso (.of k)).hom (x.appLE V ⊤ h a) * tanEv t hv h s := by
  have e2 : (tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h (a • s)) =
      x.appLE V ⊤ h a • (tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s) := by
    have e : pullbackSections x (omega t.G) h (a • s) = x.appLE V ⊤ h a • pullbackSections x (omega t.G) h s :=
      QCoh.pullbackSections_smul x (omega t.G) h a s
    rw [e]
    exact Scheme.Modules.Hom.app_smul _ _ _
  unfold tanEv
  rw [e2]
  exact map_mul (Scheme.ΓSpecIso (.of k)).hom.hom _ _

theorem tanEv_resM (hv : IsTanAtG t x v) {V V' : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V') (h' : V' ≤ V) (s : Γ(omega t.G, V)) :
    tanEv t hv h (resM _ h' s) = tanEv t hv (h.trans (x.preimage_mono h')) s := by
  unfold tanEv
  congr 2
  exact QCoh.pullbackSections_res x (omega t.G) h h' s

theorem tanEv_dUnit (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) {W : t.G.left.Opens}
    (hW : V ≤ unitSec t.G ⁻¹ᵁ W) (hv' : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(t.G.left, W)) :
    tanEv t hv h (dUnit t.G hW f) = ((Scheme.ΓSpecIso (.of (DualNumber k))).hom (v.appLE W ⊤ hv' f)).snd := by
  have h1 : (baseMap (π := t.G.hom) (φ := v) (f := x) (sec_hom (epsZero k)) hv.1 (epsZero_comp_of_isTanAtG t hv)).app ⊤
      (pullbackSections x (conormal (unitSec t.G)) h (d (sec_hom η[t.G]) hW f)) =
      d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) (v.appLE W ⊤ hv' f) :=
    baseMap_d (sec_hom η) (sec_hom (epsZero k)) hv.left (epsZero_comp_of_isTanAtG t hv) hW h
      (le_preimage_top (LieVB.sec (epsZero k)) ⊤) hv' f
  have h2 (P Q : Γ(Sp (DualNumber k), ⊤)) : d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) (P * Q) =
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤) P • d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) Q +
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤) Q • d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) P :=
    d_mul (sec_hom (epsZero k)) (le_preimage_top (LieVB.sec (epsZero k)) ⊤) P Q
  have h3 (a : Γ(Sp k, ⊤)) : d (sec_hom (epsZero k)) (le_preimage_top _ ⊤)
      ((specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) a) = 0 :=
    d_base (sec_hom (epsZero k)) (le_preimage_top (LieVB.sec (epsZero k)) ⊤)
      (le_preimage_top (specO k (DualNumber k)).hom ⊤) a
  have hB (c : k) : (specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k c) =
      (Scheme.ΓSpecIso (.of (DualNumber k))).inv (algebraMap k (DualNumber k) c) := by
    rw [appLE_top]
    have e := congrArg (fun g => g.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    exact e.symm
  have hP (a : Γ(Sp k, ⊤)) :
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤) ((specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) a) = a := by
    rw [appLE_top, appLE_top]
    have e := congrArg (fun g : Sp k ⟶ Sp k => g.appTop a) (sec_hom (epsZero k))
    simp at e
    exact e
  set F := v.appLE W ⊤ hv' f
  set D := (Scheme.ΓSpecIso (.of (DualNumber k))).hom F with hD
  have hdec : F = (specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k D.fst) +
      (specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k D.snd) * epsFn k := by
    rw [hB, hB, epsFn, ← map_mul, ← map_add (f := _)]
    have e : algebraMap k (DualNumber k) D.fst + algebraMap k (DualNumber k) D.snd * DualNumber.eps = D := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [e, hD, Iso.hom_inv_id_apply]
  have hdF : d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) F =
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤)
          ((specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k D.snd)) •
        d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) (epsFn k) := by
    rw [hdec, map_add (f := _), h3, h2, h3, smul_zero, add_zero, zero_add]
  have h4 : (tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h (dUnit t.G hW f)) =
      (epsIso k).hom.app ⊤ (d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) F) := by
    rw [← h1]
    exact (QCoh.app_app _ _ _ _).symm
  rw [tanEv, h4, hdF]
  erw [Scheme.Modules.Hom.app_smul, epsIso_d, hP]
  erw [smul_eq_mul, _root_.mul_one]
  simp

end Pairing

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p}

namespace Lat

variable {B : Mdl Y i₀}

end Lat

namespace FlagFam

variable {P : ∀ B : Mdl Y i₀, Lat B → Prop}

end FlagFam

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

end GlobalTheory.LocM
