module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupExOf
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Filter

namespace PositivityTheory.Rg.BcB.F.SG

open PositivityTheory.Rg.BcB.F

variable {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
  [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)] {d : ℕ}

local notation "Vd" => EuclideanSpace ℂ (Fin d)

def trU (u : Vd →L[ℂ] Vd) (a : Prod' H d) (k : ℕ) : ℂ :=
  LinearMap.trace ℂ Vd (((u * a.2) ^ k : Vd →L[ℂ] Vd) : Vd →ₗ[ℂ] Vd)

def BoundAt (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (u : Vd →L[ℂ] Vd) (a : Prod' H d) : Prop :=
  ∃ (C : ℝ) (N j : ℕ), ∀ᶠ k : ℕ in atTop,
    ‖trU u a k‖ ≤ C * (1 + k) ^ N * Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * a.1 s) ^ (k - j)‖)

def TraceSplit (u : Vd →L[ℂ] Vd) (a : Prod' H d) (t : ι → ℕ → ℂ) : Prop :=
  ∀ᶠ k : ℕ in atTop, trU u a k = ∑ s, t s k

def BlockBound (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (a : Prod' H d) (t : ι → ℕ → ℂ) (j : ℕ) : Prop :=
  ∀ s, ∃ (C : ℝ) (N : ℕ), ∀ᶠ k : ℕ in atTop, ‖t s k‖ ≤ C * (1 + k) ^ N * ‖(β s ^ m * a.1 s) ^ (k - j)‖

theorem boundAt_of (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (u : Vd →L[ℂ] Vd) (a : Prod' H d) (t : ι → ℕ → ℂ) (j : ℕ)
    (h1 : TraceSplit u a t) (h2 : BlockBound β m a t j) : BoundAt β m u a := by
  choose C N hC using h2
  have hall := Filter.eventually_all.2 hC
  refine ⟨∑ s, |C s|, Finset.univ.sup N, j, ?_⟩
  filter_upwards [h1, hall] with k hk hks
  rw [hk]
  have hk1 : (1 : ℝ) ≤ 1 + (k : ℝ) := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  calc ‖∑ s, t s k‖ ≤ ∑ s, ‖t s k‖ := norm_sum_le _ _
    _ ≤ ∑ s, |C s| * (1 + (k : ℝ)) ^ (Finset.univ.sup N) *
          Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * a.1 s) ^ (k - j)‖) := by
        apply Finset.sum_le_sum
        intro s _
        have hP : (1 + (k : ℝ)) ^ (N s) ≤ (1 + (k : ℝ)) ^ (Finset.univ.sup N) :=
          pow_le_pow_right₀ hk1 (Finset.le_sup (Finset.mem_univ s))
        have hX : ‖(β s ^ m * a.1 s) ^ (k - j)‖ ≤
            Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * a.1 s) ^ (k - j)‖) :=
          Finset.le_sup' (fun s => ‖(β s ^ m * a.1 s) ^ (k - j)‖) (Finset.mem_univ s)
        calc ‖t s k‖ ≤ C s * (1 + (k : ℝ)) ^ (N s) * ‖(β s ^ m * a.1 s) ^ (k - j)‖ := hks s
          _ ≤ |C s| * (1 + (k : ℝ)) ^ (N s) * ‖(β s ^ m * a.1 s) ^ (k - j)‖ := by
            gcongr
            exact le_abs_self _
          _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hP (abs_nonneg _)) hX (norm_nonneg _)
              (by positivity)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

end PositivityTheory.Rg.BcB.F.SG

end
