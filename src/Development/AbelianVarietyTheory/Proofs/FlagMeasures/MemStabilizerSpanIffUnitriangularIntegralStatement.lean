module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemStabilizerSpanIffUnitriangularIntegral
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

open Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise

theorem _root_.GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E), LinearIndependent E v → ∀ (g : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E), IsUni M → (∀ b, g (v b) = ∑ a, M a b • v a) → (g ∈ MulAction.stabilizer ((Fin N → E) ≃ₗ[E] (Fin N → E)) (Submodule.span L.O (Set.range v)) ↔ IsIntM L M) := by
  first | exact @GlobalTheory.HL.unistab_iff | exact GlobalTheory.HL.unistab_iff | (intros; apply GlobalTheory.HL.unistab_iff <;> assumption)
