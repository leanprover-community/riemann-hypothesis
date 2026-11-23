module

import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TransversalZerosOfJacobianNeZeroDomain
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.IwLevel

theorem section_ext_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}} (h : X ⟶ Sp k) {f g : Sp k ⟶ X}
    (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _)
    (pt : Sp k) (e : f pt = g pt) : f = g := by
  apply GlobalTheory.KeyKa.section_ext_of_apply_eq <;> assumption

theorem finite_points_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj B] (π : A ⟶ B) (d : ℕ),
    IsIsogDeg π d → Set.Finite {a : 𝟙_ (Over (Sp k)) ⟶ A | a ≫ π = 1} := by
  intro k _ A B _ π d hπ
  have := hπ.fin
  let pt : Sp k := IsLocalRing.closedPoint k
  have hF := π.left.finite_preimage_singleton ((1 : 𝟙_ (Over (Sp k)) ⟶ B).left pt)
  refine Set.Finite.of_finite_image (f := fun a => a.left pt) (hF.subset ?_) ?_
  · rintro _ ⟨a, ha, rfl⟩
    change π.left (a.left pt) = _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, show a ≫ π = 1 from ha]
  · intro a _ b _ hab
    exact Over.OverMorphism.ext (section_ext_of_apply_eq A.hom (Over.w a) (Over.w b) pt hab)

end GlobalTheory.IwLevel
