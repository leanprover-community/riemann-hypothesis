module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerMoveScalarFibreMeasureOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.eichlerMove_scalar_fibre_measure_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 0 ≤ S.a → ∀ u : S.V, (S.InZ u → cint S.refT (ind fun t : E => (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) = 1) ∧ ((∃ t : E, (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) → S.InZ u) := by
  first | exact @GlobalTheory.MoveFibre.fibre_scalar | exact GlobalTheory.MoveFibre.fibre_scalar | (intros; apply GlobalTheory.MoveFibre.fibre_scalar <;> assumption)
