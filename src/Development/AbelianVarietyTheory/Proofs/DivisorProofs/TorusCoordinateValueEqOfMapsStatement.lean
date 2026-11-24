module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateValueEqOfMaps
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torusCoordinate_value_eq_of_maps : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D'.P.L (D'.P.L.pull F)) (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left) (x : D'.X) (hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k) (hψ' : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k), LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)) → LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ' (g.t x)) → ∀ (z : (thickObj R' I' e G').left) (J : ((thickObj R' I' e G').left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (g.t x) f z J = val (g.t x) f' z J := by
  first | exact @GlobalTheory.Mum.gtCoord_val_eq_of_maps | exact GlobalTheory.Mum.gtCoord_val_eq_of_maps | (intros; apply GlobalTheory.Mum.gtCoord_val_eq_of_maps <;> assumption)
