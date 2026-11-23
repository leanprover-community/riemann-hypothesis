module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackEighthPowerEndomorphismsFieldPoint
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pullback_eighth_power_endomorphisms_field_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] (P : PolAV (Sp R)) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (u' : Sp R ⟶ F.X), IsDiagEnd F W P u' ε → ∀ (K : Type) [Field K] (yK : R →+* K), ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ P.A.left) (_ : IsGrpPullback A.A P.A (spMap yK) φ) (_ : LBIso A.L (P.L.pull φ)) (εA : Matrix (Fin 8) (Fin 8) ℤ → (A.A ⟶ A.A)), IsDiagEnd F W A (spMap yK ≫ u') εA ∧ ∀ (Y : Over (Sp K)) (x x' : Y ⟶ A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), x'.left ≫ φ = x.left ≫ φ ≫ (ε E).left → x' = x ≫ εA E := by
  first | exact @GlobalTheory.Poinc.DiagPull.exists_pull_field | exact GlobalTheory.Poinc.DiagPull.exists_pull_field | (intros; apply GlobalTheory.Poinc.DiagPull.exists_pull_field <;> assumption)
