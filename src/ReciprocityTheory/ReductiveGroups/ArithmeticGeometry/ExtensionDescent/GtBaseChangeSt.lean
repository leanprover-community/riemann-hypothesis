module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def GtBaseChangeSt : Prop :=
  ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G], E.IsGt G →
    ∃ (E' : SplitExt S') (φ : E.X ≃+ E'.X) (e : E'.B ≅ (Over.pullback f).obj E.B),
      IsMonHom e.hom ∧
      (∀ χ : E.X, ∃ w : LB.Iso ((E.O χ).L.pull (e.hom.left ≫ pullback.fst E.B.hom f))
          (E'.O (φ χ)).L, w.IsGen) ∧
      E'.IsGt ((Over.pullback f).obj G)

def CubePullSt : Prop :=
  ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (m : CubeMap G' G) (L : RigLB G) (c : CubicalStr G L),
    ∃ (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen),
      (∃ c' : CubicalStr G' (m.rigLB L hL hr), m.IsPullCubical c' c) ∧
      (L.IsSymmetric → (m.rigLB L hL hr).IsSymmetric)

structure Laws3 : Prop where
  gtBaseChange : GtBaseChangeSt
  cubePull : CubePullSt

end ReciprocityTheory.ChartRestriction.G.Out
