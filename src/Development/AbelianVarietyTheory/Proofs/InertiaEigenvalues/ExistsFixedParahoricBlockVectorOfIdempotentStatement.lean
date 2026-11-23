module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedParahoricBlockVectorOfIdempotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_fixed_parahoricBlockVector_of_idempotent : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (x : W), resCard F = p → z * z = z → IsBlockVec χ π x → NotKilled π z x → ∃ y : W, y ≠ 0 ∧ IsBlockVec χ π y ∧ ∃ ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F, (∀ g, IsLift g (ℓ g)) ∧ (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y := by
  first | exact @GlobalTheory.BlockIdem.exists_fixed_blockVec | exact GlobalTheory.BlockIdem.exists_fixed_blockVec | (intros; apply GlobalTheory.BlockIdem.exists_fixed_blockVec <;> assumption)
