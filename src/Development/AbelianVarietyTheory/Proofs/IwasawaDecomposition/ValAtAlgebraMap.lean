module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.OfModel

section Values

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h]
  exact congrArg _ (IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec)

theorem valAt_mul {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_fnOf {U : Z.Opens} (hU : below y ∈ U) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : Γ(Z, U)) :
    valAt y (fnOf U (gen_mem hU) a) =
      (y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom a := by
  have e : Z.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) y =
      y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [← algebraMap_germ hU, valAt_algebraMap, ← e]
  rfl

end Values

theorem eval_pull {K O : Type} [CommRing K] [CommRing O] (φ : O →+* K) {X Z : Scheme.{0}} (j : Z ⟶ X)
    (y : Sp K ⟶ Z) (yt : Sp O ⟶ X) (e : spMap φ ≫ yt = y ≫ j) {U : X.Opens} {W : Z.Opens}
    (hW : W ≤ j ⁻¹ᵁ U) (h : ⊤ ≤ y ⁻¹ᵁ W) (ht : ⊤ ≤ yt ⁻¹ᵁ U) (a : Γ(X, U)) :
    (y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom ((j.appLE U W hW).hom a) =
      φ ((yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom a) := by
  have e1 : j.appLE U W hW ≫ y.appLE W ⊤ h = yt.appLE U ⊤ ht ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    simp only [e]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e3 : j.appLE U W hW ≫ y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
      (yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom) ≫ CommRingCat.ofHom φ := by
    rw [← Category.assoc, e1, Category.assoc, e2, Category.assoc]
  exact congrArg (fun ψ => ψ.hom a) e3

variable {F : Type} [Field F] [NumberField F]

variable {Y : Var F} (M : TrueGeo.Model Y) (B : LB M.X)

end GlobalTheory.TrueGeo.OfModel
