module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantLinearExtensionToAlgClosedField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.equivariant_linearExtension_to_algClosedField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (E₀ : Fam D.toPre (Kb R) N → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), Eqv D.toPre A (Kb R) N lab E₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (Kb R) F] [IsScalarTower (FractionRing R) (Kb R) F] (lab' : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A)), LabExt (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) lab lab' → ∀ (E' : Fam D.toPre F N →ₗ[F] SecF A F N), (∀ s, E' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s) = secPull A (Kb R) F N (E₀ s)) → ∀ (p : QkPt D.toPre F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D.toPre F N), GlobalTheory.UT.TXFrame N p w → SymLift A.A A.L N N (lab' p) θ → PhiRel D.toPre F N p w s s' → IsActOf A.A A.L N θ (E' s) (E' s') := by
  first | exact @GlobalTheory.Mum.UpAct.act_extension | exact GlobalTheory.Mum.UpAct.act_extension | (intros; apply GlobalTheory.Mum.UpAct.act_extension <;> assumption)
