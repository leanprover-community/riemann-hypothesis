module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisOfCompatibleTangentRelation
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isLieBasis_of_compatible_tangentRelation : ∀ (R : Type) [CommRing R] (G H : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (Rel : (epsR R ⟶ G) → (epsR R ⟶ H) → Prop), Rel 1 1 → (∀ y y' x x', Rel y x → Rel y' x' → Rel (y * y') (x * x')) → (∀ (c : R) (y : epsR R ⟶ G) (x : epsR R ⟶ H) (y' : epsR R ⟶ G) (x' : epsR R ⟶ H), y'.left = spMap (epsScaleR c) ≫ y.left → x'.left = spMap (epsScaleR c) ≫ x.left → Rel y x → Rel y' x') → (∀ y, IsTangent y → ∃ x, IsTangent x ∧ Rel y x) → (∀ y y' x, IsTangent y → IsTangent y' → Rel y x → Rel y' x → y = y') → (∀ y x x', Rel y x → Rel y x' → x = x') → ∀ (n : ℕ) (x : Fin n → (epsR R ⟶ H)) (y : Fin n → (epsR R ⟶ G)), IsLieBasis x → (∀ j, IsTangent (y j) ∧ Rel (y j) (x j)) → IsLieBasis y := by
  first | exact @GlobalTheory.LieTransfer.isLieBasis_of_rel | exact GlobalTheory.LieTransfer.isLieBasis_of_rel | (intros; apply GlobalTheory.LieTransfer.isLieBasis_of_rel <;> assumption)
