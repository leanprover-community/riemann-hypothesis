module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMovesKernelCommonStabilizerSmulEqStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMoveKernelSymmStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMovesFiniteTargetsSplitStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetKernelBoundByWeightStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetKernelRowSumNearOneStatement
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
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem exists_symm_invariant_kernel : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, P Λ ↔ (S.IsTerm d Λ ∧ S.InFF β (j + 1) βJ d Λ)) → ∃ m : Submodule L.O S.V → Submodule L.O S.V → ℝ, (∀ h ∈ S.St, ∀ x y, P x → P y → m (h • x) (h • y) = m x y) ∧ ∀ x, P x → {y | P y ∧ m x y ≠ 0}.Finite ∧ (∀ y, P y → 0 ≤ m x y ∧ m x y = m y x) ∧ |(∑ᶠ y : {y // P y}, m x y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ‖∑ᶠ y : {y // P y}, (m x y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d P hP
  have hPe : P = fun Λ => S.IsTerm d Λ ∧ S.InFF β (j + 1) βJ d Λ :=
    funext fun Λ => propext (hP Λ)
  subst hPe
  refine ⟨fun x y => S.kern β (j + 1) βJ d x y, ?_, ?_⟩
  · intro h hh x y hx _
    exact GlobalTheory.T.frameMovesKernel_commonStabilizer_smul_eq L r k S d x hx.1 β (j + 1) βJ y h hh
  · intro x hx
    have base := GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split L r k S j β βJ d x hx.1 hx.2
    refine ⟨?_, ?_, GlobalTheory.T.hermitianDoubleCoset_kernel_row_sum_near_one L r k S hk j β βJ d x hx.1 hx.2,
      GlobalTheory.T.hermitianDoubleCoset_kernel_bound_by_weight L r k S hk j β βJ d x hx.1 hx.2⟩
    · exact base.2.2.1.subset fun y hy => hy.2
    · intro y hy
      exact ⟨base.2.2.2.1 y, GlobalTheory.T.hermDoubleCosetMoveKernel_symm L r k S j β βJ d x hx.1 hx.2 y hy.1 hy.2⟩

end GlobalTheory.HL
