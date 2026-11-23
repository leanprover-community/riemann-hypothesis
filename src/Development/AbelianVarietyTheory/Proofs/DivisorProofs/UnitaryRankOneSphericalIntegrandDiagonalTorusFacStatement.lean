module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankOneSphericalIntegrandDiagonalTorusFac
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

theorem _root_.GlobalTheory.T.unitaryRankOne_sphericalIntegrand_diagonal_torus_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂˣ) (φ : GU σ n → ℂ), IsSphericalU q (fun i => (α i : ℂ)) φ →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → ∀ w x : GU σ n,
      φ (y⁻¹ * t * w * x) * (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
        chiDeltaU q (fun i => (actU k α i : ℂ)) t * φ (y⁻¹ * w * x) := by
  first | exact @GlobalTheory.WeylCell.U21TorusFactor.torus_factor | exact GlobalTheory.WeylCell.U21TorusFactor.torus_factor | (intros; apply GlobalTheory.WeylCell.U21TorusFactor.torus_factor <;> assumption)
