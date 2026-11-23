module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonGenericFibreDiagonalEndEighthPower
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
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_common_genericFibre_diagonalEnd_eighthPower : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R R' K : Type) [CommRing R] [CommRing R'] [Field K] (f : R →+* K) (f' : R' →+* K) (P : PolAV (Sp R)) (u : Sp R ⟶ F.X) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (P' : PolAV (Sp R')) (u' : Sp R' ⟶ F.X), IsDiagEnd F W P u ε → SharpOver F W P' u' → spMap f ≫ u = spMap f' ≫ u' → ∃ ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A), IsDiagEnd F W P' u' ε' ∧ ∃ (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left) (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap f) a ∧ IsGrpPullback P₀.A P'.A (spMap f') a' ∧ LBIso P₀.L (P.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') ∧ ∀ E, (ε₀ E).left ≫ a = a ≫ (ε E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε' E).left := by
  first | exact @GlobalTheory.Poinc.exists_common_fibre_diagEnd | exact GlobalTheory.Poinc.exists_common_fibre_diagEnd | (intros; apply GlobalTheory.Poinc.exists_common_fibre_diagEnd <;> assumption)
