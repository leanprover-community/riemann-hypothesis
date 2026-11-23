module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum

open ReciprocityTheory.ChartRestriction.G.Semi

variable {S : Scheme.{0}}

structure PowerDatum (j : ℕ) (G' G : Over S) [GrpObj G'] [GrpObj G] where

  pr : Fin j → (G' ⟶ G)

  isMonHom : ∀ i, IsMonHom (pr i)

  bij : ∀ T : Over S, Function.Bijective (fun (x : T ⟶ G') (i : Fin j) => x ≫ pr i)

attribute [instance] PowerDatum.isMonHom


variable (G : Over S)

variable [GrpObj G]



section Symm

variable {G : Over S} [GrpObj G]

lemma eSec_inv : eSec G ≫ (GrpObj.inv (X := G)).left = 𝟙 _ ≫ eSec G := by
  rw [Category.id_comp, eSec, ← Over.comp_left]
  congr 1
  simp

variable [IsCommMonObj G]

def IsNormSymm (L : RigLB G) (w : LB.Iso L.L (L.L.pull (GrpObj.inv (X := G)).left)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec G) (fun _ => 1)) L.rig
      (rigPullOf (GrpObj.inv (X := G)).left (𝟙 _) eSec_inv L.L L.rig)

end Symm

namespace PowerDatum

variable {j : ℕ} {G' G : Over S} [GrpObj G'] [GrpObj G] (P : PowerDatum j G' G)

variable [IsCommMonObj G'] [IsCommMonObj G]

end PowerDatum

end GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum
