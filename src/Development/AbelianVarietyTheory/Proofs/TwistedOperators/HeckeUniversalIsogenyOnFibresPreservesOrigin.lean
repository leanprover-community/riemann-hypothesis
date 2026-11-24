module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HkLiftIsPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

private theorem one_left_eq_eSec {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {Y : Scheme.{0}} (y : Y ⟶ S) :
    (1 : Over.mk y ⟶ G).left = y ≫ eSec G := by
  rw [eSec]
  show (toUnit _ ≫ η[G]).left = _
  rw [Over.comp_left]
  congr 1

private theorem eSec_hom {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : eSec G ≫ G.hom = 𝟙 _ := by
  rw [eSec]
  have := Over.w η[G]
  simpa using this

theorem hkMap_ptSec_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkMap Z hx hx' = (ptSecT Xo.univ.t.G (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := by
  intro E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'
  have key₁ : (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkLift Z h hx = h ≫ eSec Z.o₁.t.G := by
    apply Z.m₁.cart.1.hom_ext
    · rw [Category.assoc, hkLift_φ, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec, Category.assoc,
        Z.m₁.cm.e_comm, Z.m₁.base, ← Category.assoc, ← hx]
    · rw [Category.assoc, hkLift_hom, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst_assoc, Category.assoc, eSec_hom]
      simp
  haveI := Z.isog.1.1
  have hψ : eSec Z.o₁.t.G ≫ Z.ψ.left = eSec Z.o₂.t.G := by
    rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  apply GlobalTheory.HeckeFrCompare.gx_ext
  · rw [Category.assoc, hkMap_fst, ptSecT, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst, GlobalTheory.HeckeFrCompare.lift_l_fst]
    rfl
  · rw [Category.assoc, hkMap_snd, ← Category.assoc, key₁, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec,
      Category.assoc, ← Category.assoc (eSec _), hψ, Z.m₂.cm.e_comm, Z.m₂.base, ← Category.assoc, ← hx']

end GlobalTheory.HeckeEx
