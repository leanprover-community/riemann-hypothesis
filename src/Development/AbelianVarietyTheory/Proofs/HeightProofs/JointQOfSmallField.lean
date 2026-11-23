module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants

@[expose] public section

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open scoped IntermediateField

theorem curveOver_of_weberSet (D : D7) (F : IntermediateField ℚ ℂ) {n : ℕ} (hn : 0 < n)
    (h0 : D.host.φ₀ D.host.sqrtMinusD ∈ F)
    (h : ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔
      ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + D.host.φ₀ D.host.sqrtMinusD) / 2)) → weberSet L n ⊆ F) :
    GlobalTheory.CompRat.CurveOver (hostOfRecord D) F n :=
  (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ (hostOfRecord D) F n hn).1 h0 fun L hL =>
    ⟨h L hL (Set.mem_insert _ _), fun s hs =>
      h L hL (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩


end GlobalTheory.FieldSize
