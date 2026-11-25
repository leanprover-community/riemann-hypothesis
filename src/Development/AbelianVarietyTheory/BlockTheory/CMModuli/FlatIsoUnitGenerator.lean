module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
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
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R}

def GtTors (k : ℕ) {T : Over (Sp R)} (g : Out.GtPt D T) : Prop :=
  ∃ h : Out.GtPt D T, Out.GtPt.IsNsmul k g h ∧ h.IsZero

def unitGen {X Y : Scheme.{0}} (L : LB X) (z : Γ(Y, ⊤)ˣ) :
    LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top z

def TorusVal {T : Over (Sp R)} (g : Out.GtPt D T) (χ : D.X) (z : Γ(T.left, ⊤)ˣ) : Prop :=
  g.b = Out.DegPre.zeroT D T ∧ LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (unitGen D.P.L z)

end Points

section Formal

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
  {A : Out.PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def FormalEq (U : Out.UnifPre I D A G) {T : Over (Sp R)} (x : T ⟶ G) (g : Out.GtPt D.toPre T) : Prop :=
  ∀ e : ℕ,
    (Out.fstG I e T).left ≫ g.b.left =
        ((Over.pullback (Out.thick R I e)).map x).left ≫ (U.gt e).pG.left ∧
      ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _
        (LB.pullGen D.toPre.P.L _ _ (g.s χ) (Out.fstG I e T).left)
        (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ((Over.pullback (Out.thick R I e)).map x).left)

structure IsFinitePart (U : Out.UnifPre I D A G) (k : ℕ) (N : Over (Sp R)) (g₀ : Out.GtPt D.toPre N)
    (x₀ : N ⟶ G) : Prop where
  finite : IsFinite N.hom
  flat : Flat N.hom
  gt_tors : GtTors k g₀
  gt_univ : ∀ (T : Over (Sp R)) (g : Out.GtPt D.toPre T), GtTors k g →
    ∃! h : T ⟶ N, Out.GtPt.IsPull h.left g₀ g
  g_tors : x₀ ^ k = 1
  g_mono : Mono x₀
  g_univ : ∀ T : Over (Sp R), IsFinite T.hom → ∀ x : T ⟶ G, x ^ k = 1 → ∃ h : T ⟶ N, h ≫ x₀ = x
  formal : FormalEq U x₀ g₀

end Formal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Flat

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

end Flat

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
