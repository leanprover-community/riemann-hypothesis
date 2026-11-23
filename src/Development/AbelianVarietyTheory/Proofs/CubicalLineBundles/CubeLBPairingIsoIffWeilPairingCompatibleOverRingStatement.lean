module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring : Out.Laws → ∀ (R : Type) [CommRing R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (β : R →+* k),
  (LamEq A.L f₁ f₂ B.L g₁ g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β)) ∧ (IsDedekindDomain R → Function.Injective β → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β) → LamEq A.L f₁ f₂ B.L g₁ g₂) := by
  first | exact @GlobalTheory.PairingFibre.lamEq_weilEq_over_ring | exact GlobalTheory.PairingFibre.lamEq_weilEq_over_ring | (intros; apply GlobalTheory.PairingFibre.lamEq_weilEq_over_ring <;> assumption)
