module

public import Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues
public import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally
public import Development.EtaleCohomology.TateTwists.EtaleKummerTriangleExists
public import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsSeparatedAndGlue
public import Development.EtaleCohomology.EtaleSheaves.ChernClassExistence
public import Development.EtaleCohomology.EtaleSheaves.ChernClassRootLocalization
public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder
public import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsGlueOfForgetIsSheaf
public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeOneValueOfRootsKum, Development.EtaleCohomology.EtaleSheaves.ChernClassValueFirst

-- ===== clump member: Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeOneValueOfRootsKum =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeOneValueOfRootsKum", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues\npublic import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally\npublic import Development.EtaleCohomology.TateTwists.EtaleKummerTriangleExists\npublic import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsSeparatedAndGlue\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.V1

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Loc V (fun W k => Q W (k ≫ g))) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let R : ∀ ⦃Y⦄ ⦃f : Y ⟶ U⦄, S.arrows f → Sieve Y := fun Y f H => (hPQ Y f (hP Y f H)).choose
  refine ⟨Sieve.bind S.arrows R, Scheme.etaleTopology.bind_covering hS
    (fun Y f H => (hPQ Y f (hP Y f H)).choose_spec.1), ?_⟩
  rintro W _ ⟨Y, k, f, H, hk, rfl⟩
  exact (hPQ Y f (hP Y f H)).choose_spec.2 W k hk

theorem sec_res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (s : Sec F U) : Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem sec_res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (s : Sec F U) :
    Sec.res (𝟙 U) s = s := by
  simp only [Sec.res, op_id, CategoryTheory.Functor.map_id]; rfl

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (s : Sec F U) : Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  simp only [Sec.res, Sec.map]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    φ.hom.naturality]

theorem sx_res_comp {E : Spc} {p : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sx E p U) :
    (x.res g).res k = x.res (k ≫ g) := by
  simp only [Sx.res, op_comp, CategoryTheory.Functor.map_comp_apply]

theorem sx_res_id {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : x.res (𝟙 U) = x := by
  simp only [Sx.res, op_id, CategoryTheory.Functor.map_id_apply]

theorem units_map_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) =
      Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  ext; simp; rfl

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (s : Sec F U) : Sec.map ψ (Sec.map φ s) = Sec.map (φ ≫ ψ) s := rfl

theorem d_resGen (q : ℕ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    Sec.map ((res _ (tw q 1)).d 0 1) (resGen 1 ζ) = 0 := by
  have h : resι _ (tw q 1) ≫ (res _ (tw q 1)).d 0 1 = 0 := by
    have hc : (injectiveResolution (tw q 1)).ι'.f 0 ≫ (injectiveResolution (tw q 1)).cochainComplex.d 0 1 = 0 := by
      rw [(injectiveResolution (tw q 1)).ι'.comm 0 1]; simp
    exact (Category.assoc _ _ _).trans ((congrArg (fun f => _ ≫ f) hc).trans Limits.comp_zero)
  rw [resGen, sec_map_comp, h]
  simp [Sec.map]

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  simp only [lineUnit, Sx.res]
  rw [NatTrans.naturality_apply]
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map g.appTop.hom (glMat ((L.app _).app (op U) x))) = _
  ext
  simp [Matrix.GeneralLinearGroup.map]

noncomputable abbrev dkT (q : ℕ) (V : Scheme.{0}) (v : (Γ(V, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 1) V :=
  Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V v)

theorem isUnit_res {q : ℕ} {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hU.map g.appTop.hom

theorem kT_nat {q : ℕ} (hk : IsKum q (kumT q)) {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U)
    (v : (Γ(U, ⊤))ˣ) : Sec.res g (dkT q U v) = dkT q V (Units.map g.appTop.hom.toMonoidHom v) := by
  rw [dkT, sec_res_map, hk.1 V U g v hU]

theorem kT_pow {q : ℕ} (hk : IsKum q (kumT q)) {W : Scheme.{0}} (ζ : Prim q Γ(W, ⊤)) (w : (Γ(W, ⊤))ˣ) (a : ℕ) :
    ∀ w' : (Γ(W, ⊤))ˣ, (w' : Γ(W, ⊤)) = ζ.1 ^ a * w → dkT q W w' = dkT q W w := by
  induction a with
  | zero => intro w' h; have : w' = w := Units.ext (by simpa using h); subst this; rfl
  | succ n ih =>
    intro w' h
    have hu : IsUnit (ζ.1 ^ n * (w : Γ(W, ⊤))) :=
      isUnit_of_mul_isUnit_right (x := ζ.1) (by rw [← mul_assoc, ← pow_succ', ← h]; exact w'.isUnit)
    have e : (w' : Γ(W, ⊤)) = ζ.1 * (hu.unit : Γ(W, ⊤)) := by rw [IsUnit.unit_spec, h, pow_succ', mul_assoc]
    rw [dkT, hk.2 W ζ hu.unit w' e]
    simp only [Sec.map, map_add (f := _)]
    have h0 := d_resGen q ζ
    simp only [Sec.map] at h0
    rw [h0, add_zero]
    exact ih hu.unit (IsUnit.unit_spec hu)

theorem indep {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : IsKum q (kumT q))
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) {V : Scheme.{0}} (hV : IsUnit (q : Γ(V, ⊤))) (v v' : (Γ(V, ⊤))ˣ)
    (h : v ^ q = v' ^ q) : dkT q V v = dkT q V v' := by
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) V).1
  refine loc_bind ((hp q V).1 hV) ?_
  rintro W g ⟨ζ⟩
  have h1 : (v' * v⁻¹) ^ q = 1 := by rw [mul_pow, inv_pow, ← h, mul_inv_cancel]
  have hx : ((Units.map g.appTop.hom.toMonoidHom (v' * v⁻¹) : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one]
  refine loc_mono ((hp q W).2.2.1 ζ _ hx) ?_
  rintro W' k ⟨a, ha⟩
  rw [kT_nat hk hV, kT_nat hk hV]
  have hx' : ((Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom (v' * v⁻¹)) : (Γ(W', ⊤))ˣ) : Γ(W', ⊤))
      = (Prim.map k.appTop.hom ζ).1 ^ a := ha
  have e : ((Units.map (k ≫ g).appTop.hom.toMonoidHom v' : (Γ(W', ⊤))ˣ) : Γ(W', ⊤)) =
      (Prim.map k.appTop.hom ζ).1 ^ a * (Units.map (k ≫ g).appTop.hom.toMonoidHom v : (Γ(W', ⊤))ˣ) := by
    rw [← units_map_comp, ← units_map_comp, ← hx', ← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]
  exact (kT_pow hk _ _ a _ e).symm

def Q (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 1 U) (s : Sec ((res _ (tw q 1)).X 1) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = lineUnit L (x.res g) → Sec.res g s = dkT q V v

theorem Q_res {q : ℕ} {E : Spc} {L : E ⟶ ofCat (glCat 1)} {V U : Scheme.{0}} {x : Sx E 1 U} {s} (hQ : Q q L x s)
    (g : V ⟶ U) : Q q L (x.res g) (Sec.res g s) := by
  intro W k v hv
  rw [sec_res_comp]
  exact hQ W (k ≫ g) v (by rwa [← sx_res_comp])

theorem Q_uniq {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue)
    {E : Spc} {L : E ⟶ ofCat (glCat 1)} {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) {x : Sx E 1 U} {s s'}
    (hQ : Q q L x s) (hQ' : Q q L x s') : s = s' := by
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) U).1
  refine loc_mono ((hp q U).2.2.2 hU (lineUnit L x)) ?_
  rintro V g ⟨v, hv⟩
  have hv' : v ^ q = lineUnit L (x.res g) := by rw [lineUnit_res]; exact hv
  rw [hQ V g v hv', hQ' V g v hv']

theorem Q_ex {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : IsKum q (kumT q))
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue)
    {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (x : Sx E 1 U) :
    ∃ s, Q q L x s := by
  obtain ⟨S, hS, hr⟩ := (hp q U).2.2.2 hU (lineUnit L x)
  choose vs hvs using hr
  obtain ⟨s, hs'⟩ := (hs (ZMod q) ((res _ (tw q 1)).X 1) U).2 S hS (fun V g hg => dkT q V (vs V g hg)) (by
    intro V W g k hg
    rw [kT_nat hk (isUnit_res hU g)]
    apply indep hp hk hs (isUnit_res hU (k ≫ g))
    rw [← map_pow, hvs V g hg, units_map_comp, hvs W (k ≫ g) _])
  refine ⟨s, fun V g v hv => ?_⟩
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) V).1
  refine loc_mono (P := fun W h => S.arrows (h ≫ g))
    ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W h hh => hh⟩ ?_
  intro W h hh
  rw [sec_res_comp, hs' W (h ≫ g) hh, kT_nat hk (isUnit_res hU g)]
  apply indep hp hk hs (isUnit_res hU (h ≫ g))
  rw [hvs, ← map_pow, hv, lineUnit_res, units_map_comp]

end LateralTheory.EtaleFoundations.V1

open LateralTheory.EtaleFoundations.V1 in
theorem LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_one_value_of_roots_kummer_gluing (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists)
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) : LateralTheory.EtaleFoundations.ExistsNaturalEtaleKummerChernClassDegreeOneValue := by
  classical
  intro q _ E L hi
  have hU : ∀ (U : Scheme.{0}) (x : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hi U ⟨x.face 0⟩
  have hex : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ s, Q q L x s := fun U x => Q_ex hp (hk q) hs L (hU U x) x
  refine ⟨fun U x => (hex U x).choose, fun V U g x =>
    Q_uniq hp hs (hU V (x.res g)) (Q_res (hex U x).choose_spec g) (hex V (x.res g)).choose_spec, fun U x v hv => ?_⟩
  have h := (hex U x).choose_spec U (𝟙 U) v (by rwa [sx_res_id])
  rwa [sec_res_id] at h
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeOneValueOfRootsKum =====

-- ===== clump member: Development.EtaleCohomology.EtaleSheaves.ChernClassValueFirst =====
-- clump-header: {"m": "Development.EtaleCohomology.EtaleSheaves.ChernClassValueFirst", "h": "module\n\npublic import Development.EtaleCohomology.EtaleSheaves.ChernClassExistence\npublic import Development.EtaleCohomology.EtaleSheaves.ChernClassRootLocalization\npublic import Development.EtaleCohomology.TateTwists.EtaleKummerTriangleExists\npublic import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally\npublic import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder\npublic import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsGlueOfForgetIsSheaf\npublic import Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeOneValueOfRootsKum\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor

theorem kumT_ex_of (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists := by
  intro q _
  unfold kumT
  exact pick_spec (hk q)

theorem prim_loc_of (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally :=
  LateralTheory.EtaleFoundations.etale_locally_roots_of_unity_structure_of_exists_and_kummer LateralTheory.EtaleFoundations.etale_locally_exists_primitive_root_of_unity_of_invertible_order hr

theorem etale_kummer_chern_edge_values_exist_of_local_roots_and_kummer_torsor (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) :
    LateralTheory.E.ChernClassExistence.EtaleKummerChernEdgeValuesExistNatural :=
  LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_one_value_of_roots_kummer_gluing (prim_loc_of hr) (kumT_ex_of hk) LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf

end LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.EtaleSheaves.ChernClassValueFirst =====
