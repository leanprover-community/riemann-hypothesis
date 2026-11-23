module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

def TorusEndOf {S : Scheme.{0}} (X : Type) [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) : Prop :=
  ∀ χ : X, res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) = charUnit S X (h χ)

structure UnifPre.OLinear (O : Type) [Ring O] [StarRing O] {D : DegData R I}
    [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O) : Prop where
  ext : ∀ a : O, (Over.pullback (jK R)).map (ιG.act a) ≫ U.gen.hom = U.gen.hom ≫ ιA.act a
  q_lin : ∀ (e : ℕ) (a : O), (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
    (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a)
  i_lin : ∀ (e : ℕ) (a : O), ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
      splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
    TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
      (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i

end ReciprocityTheory.ChartRestriction.G.Out
