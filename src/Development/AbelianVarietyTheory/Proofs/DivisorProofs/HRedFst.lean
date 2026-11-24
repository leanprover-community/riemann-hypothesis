module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntEval

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)}


variable (I) in
def hRed (h : 𝟙_ (Over (Sp R)) ⟶ G) (e : ℕ) : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e G).left :=
  pullback.lift (thick R I e ≫ h.left) (𝟙 _) (by
    rw [Category.assoc, Over.w h, Category.id_comp]
    exact Category.comp_id _)

theorem hRed_fst (h : 𝟙_ (Over (Sp R)) ⟶ G) (e : ℕ) : hRed I h e ≫ fGl I G e = thick R I e ≫ h.left :=
  pullback.lift_fst _ _ _

variable {D : DegData R I} {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

def TRel (U : UnifPre I D A G) (h : 𝟙_ (Over (Sp R)) ⟶ G) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)))
    (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, b.left] (DegPre.lineε 1))) (e : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (R ⧸ I ^ (e + 1))) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (JG : (Z ⟶ G.left) → U.LG.L.ι), Good D.toPre.P.L z J → Good U.LG.L z JG →
    val t (r ≫ thick R I e) z J *
        wv U e (r ≫ hRed I h e) z (J (r ≫ hRed I h e ≫ pGl U e)) (JG (r ≫ hRed I h e ≫ fGl I G e)) *
        val f (r ≫ thick R I e) z JG =
      val (L := D.toPre.P.L) D.toPre.rig (r ≫ thick R I e) z J

end GlobalTheory.Poinc.IntEval
