module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

abbrev gK : pullback G.hom (jK V) ⟶ G.left := pullback.fst G.hom (jK V)

def endK (f : G ⟶ G) : pullback G.hom (jK V) ⟶ pullback G.hom (jK V) :=
  pullback.map G.hom (jK V) G.hom (jK V) f.left (𝟙 _) (𝟙 _) (by simp) (by simp)

def unitK : Spec (CommRingCat.of (FractionRing V)) ⟶ pullback G.hom (jK V) :=
  pullback.lift (jK V ≫ eSec G) (𝟙 _) (by simp [eSec])

def IsPullByEnd (U : Unif (maximalIdeal V) D A G) (f : G ⟶ G) (k N : ℕ) (s : U.SecK k) (s' : U.SecK (k * N)) : Prop :=
  ∃ u : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)]), u.IsGen ∧
    LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ u unitK)
      (LB.pullGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig (k * (N - 1))) (jK V)) ∧
    GeneratorPullback.SecRel U.LG.L (fun _ : Fin 1 => gK) (fun _ => ((k * N : ℕ) : ℤ)) s'
      (fun _ : Fin 1 => gK) (fun _ => (k : ℤ)) s (endK f)
      ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)] u

end ReciprocityTheory.ChartRestriction.G.DVR
