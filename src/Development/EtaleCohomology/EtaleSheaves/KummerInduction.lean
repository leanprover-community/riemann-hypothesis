module

public import Development.EtaleCohomology.EtaleSheaves.ContStepPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.ContStepPf

namespace LateralTheory.E.StepKPf

variable {J : Type} [SmallCategory J]

def lv (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J} (f : k ⟶ j0) :
    (D.obj k).Opens := (D.map f ≫ e.hom) ⁻¹ᵁ U

def lm {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) : c.pt.Opens :=
  (c.π.app j0 ≫ e.hom) ⁻¹ᵁ U

theorem lm_le {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J}
    (f : k ⟶ j0) : lm c e U ≤ (c.π.app k) ⁻¹ᵁ lv D e U f := by
  rw [lm, lv, ← Scheme.Hom.comp_preimage, ← Category.assoc, c.w f]

theorem lv_le (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : lv D e U (g ≫ f) ≤ (D.map g) ⁻¹ᵁ lv D e U f := by
  rw [lv, lv, ← Scheme.Hom.comp_preimage, ← Category.assoc, ← D.map_comp]

def rL {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J}
    (f : k ⟶ j0) : (lm c e U).toScheme ⟶ (lv D e U f).toScheme :=
  (c.π.app k).resLE _ _ (lm_le c e U f)

def rD (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : (lv D e U (g ≫ f)).toScheme ⟶ (lv D e U f).toScheme :=
  (D.map g).resLE _ _ (lv_le D e U f g)

def RC (q : ℕ) {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) : Prop :=
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj (lm c e U).toScheme) n i, ∃ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (lv D e U f).toScheme) n i), pull _ (sch.map (rL c e U f)) _ _ y = x) ∧
  ∀ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (lv D e U f).toScheme) n i), pull _ (sch.map (rL c e U f)) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map (rD D e U f g)) _ _ y = 0

def Restr : Prop := Hyp → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0})
  (e : D.obj j0 ≅ X) (U : X.Opens), IsCompact ((e.hom ⁻¹ᵁ U : (D.obj j0).Opens) : Set (D.obj j0)) →
  PC U.toScheme → RC q c e U

def DiagramChase₂ : Prop := Hyp → MV → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X) (U V : X.Opens), U ⊔ V = ⊤ →
  RC q c e U → RC q c e V → RC q c e (U ⊓ V) →
  ∀ (n i : ℤ) (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (D.obj k)) n i), pull _ (sch.map (c.π.app k)) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map (D.map g)) _ _ y = 0

theorem cpt_pre {Y X : Scheme.{0}} (e : Y ≅ X) (U : X.Opens) (hU : IsCompact (U : Set X)) :
    IsCompact ((e.hom ⁻¹ᵁ U : Y.Opens) : Set Y) :=
  (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isCompact_preimage.mpr hU

theorem StepK_of (hR : Restr) (hC : DiagramChase₂) : StepK := by
  intro h hmv X U V hU hV hUV pU pV pW q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i j y hy
  have := hqs j0
  have hU' := cpt_pre e U hU
  have hV' := cpt_pre e V hV
  have hW' : IsCompact ((e.hom ⁻¹ᵁ (U ⊓ V) : (D.obj j0).Opens) : Set (D.obj j0)) := by
    rw [Scheme.Hom.preimage_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ (e.hom ⁻¹ᵁ U).isOpen hU' (e.hom ⁻¹ᵁ V).isOpen hV'
  have rU := hR h q D c hc ha hcs hqs hu j0 X e U hU' pU
  have rV := hR h q D c hc ha hcs hqs hu j0 X e V hV' pV
  have rW := hR h q D c hc ha hcs hqs hu j0 X e (U ⊓ V) hW' pW
  let k := IsCofiltered.min j j0
  have hy' : pull _ (sch.map (c.π.app k)) _ _ (pull _ (sch.map (D.map (IsCofiltered.minToLeft j j0))) _ _ y) = 0 := by
    rw [← pull_comp, ← Functor.map_comp, c.w]; exact hy
  obtain ⟨l, g, hg⟩ := hC h hmv q D c hc j0 X e U V hUV rU rV rW n i k (IsCofiltered.minToRight j j0) _ hy'
  refine ⟨l, g ≫ IsCofiltered.minToLeft j j0, ?_⟩
  rw [D.map_comp, Functor.map_comp, pull_comp]; exact hg

end LateralTheory.E.StepKPf
