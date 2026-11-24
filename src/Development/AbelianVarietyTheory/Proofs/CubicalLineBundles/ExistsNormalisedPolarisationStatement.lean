module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_normalized_symmetric_ample_lb : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A → LamEq P.L w (𝟙 P.A) P.L (𝟙 P.A) w' →
  ∃ L' : LB P.A.left, L'.IsLB ∧ Out.Rigidified P.A L' ∧ Out.Sym P.A L' ∧ Out.RelAmple P.A L' ∧ Out.KTriv P.A L' ∧ LamEq L' (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) ∧ LBIso L' (cubeLB P.A ![𝟙 P.A, w] L') := by
  first | exact @GlobalTheory.CM.exists_normalised_polarisation | exact GlobalTheory.CM.exists_normalised_polarisation | (intros; apply GlobalTheory.CM.exists_normalised_polarisation <;> assumption)
