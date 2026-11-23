module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentCombinationCharacterValues
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.torusTangentCombination_characterValues : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)), (∀ l, (Φ _ (x l)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x l)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a l χ)))) → ∀ d : Fin r → R, (Φ _ (tanComb d x)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (tanComb d x)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (∑ l, d l * a l χ))) := by
  first | exact @GlobalTheory.MBLow.TorusVals.tanComb_vals | exact GlobalTheory.MBLow.TorusVals.tanComb_vals | (intros; apply GlobalTheory.MBLow.TorusVals.tanComb_vals <;> assumption)
