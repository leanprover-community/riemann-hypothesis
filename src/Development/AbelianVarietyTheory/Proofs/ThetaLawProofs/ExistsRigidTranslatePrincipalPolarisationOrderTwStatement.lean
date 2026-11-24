module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_rigidTranslate_principalPolarisation_order_two : Out.Laws → ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (t : 𝟙_ (Over (Sp R)) ⟶ P.A), t ^ 2 = 1 → ∃ (P' : Out.PolAV (Sp R)) (e : P'.A ≅ P.A), IsMonHom e.hom ∧ P'.g = P.g ∧ LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left ∧ LBIso P'.L (LB.LinComb P.L (K := Fin 2) ![(e.hom ≫ ((toUnit P.A ≫ t) * 𝟙 P.A)).left, (toUnit P'.A ≫ t).left] ![1, -1]) := by
  first | exact @GlobalTheory.RigidTranslate.exists_rigid_translate | exact GlobalTheory.RigidTranslate.exists_rigid_translate | (intros; apply GlobalTheory.RigidTranslate.exists_rigid_translate <;> assumption)
