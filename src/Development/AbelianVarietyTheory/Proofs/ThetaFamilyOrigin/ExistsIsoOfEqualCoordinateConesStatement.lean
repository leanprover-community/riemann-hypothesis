module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsoOfEqualCoordinateCones
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_iso_of_equal_coordinateCones : ∀ (K : Type) [Field K] [IsAlgClosed K] (X X' : Over (Sp K)) [IsIntegral X.left] [IsIntegral X'.left] [IsProper X.hom] [IsProper X'.hom] (H : LB X.left) (H' : LB X'.left) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy X.hom H s Set.univ → ImmBy X'.hom H' s' Set.univ → cone X.hom H s = cone X'.hom H' s' → ∃ φ : X ≅ X', ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ X.left) (v : J → R), Crd H s y v → Crd H' s' (y ≫ φ.hom.left) v := by
  first | exact @GlobalTheory.ZH.IsoCone.exists_iso | exact GlobalTheory.ZH.IsoCone.exists_iso | (intros; apply GlobalTheory.ZH.IsoCone.exists_iso <;> assumption)
