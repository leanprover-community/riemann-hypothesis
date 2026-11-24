module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsKillIdeal
public import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem fromSpec_Sp_eq (R' : Type) [CommRing R'] {W : (Sp R').Opens} (hW : IsAffineOpen W) :
    hW.fromSpec = spMap ((Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
      (Sp R').presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (𝟙 (Sp R')) (isAffineOpen_top (Sp R')) hW le_top
  rw [Category.comp_id, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h]
  simp [spMap, Scheme.Hom.appLE]

theorem killIdeal_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
    P R' x → P R'' (spMap g ≫ x)) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), P R' x →
    ∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom := by
  intro S P hP R' _ x hx V hV a ha
  rw [RingHom.mem_ker]
  apply (Sp R').IsSheaf.section_ext
  intro p hp
  obtain ⟨W, hWa, hpW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Sp R').isBasis_affineOpens) hp
  refine ⟨W, hWle, hpW, ?_⟩
  have hW : IsAffineOpen W := hWa
  have e : hW.fromSpec ≫ x = spMap (x.appLE V W hWle).hom ≫ hV.fromSpec := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec x hV hW hWle]; rfl
  have hy : ptQ P V hV _ (x.appLE V W hWle).hom := by
    show P _ (spMap (x.appLE V W hWle).hom ≫ hV.fromSpec)
    rw [← e, fromSpec_Sp_eq]
    exact hP _ _ _ x hx
  have h0 := ha _ _ hy
  rw [map_zero]
  simpa [Scheme.Hom.appLE] using h0

end GlobalTheory.PtClosed
