module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

theorem exists_kStable_of_mem_lowKSub (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (hw : w ∈ lowKSub ε lam σ) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ IsKStableOn ε σ S ∧ w ∈ S := by
  classical
  obtain ⟨s, hs, hws⟩ := Submodule.mem_sSup_iff_exists_finset.1 hw
  refine ⟨⨆ i ∈ s, i, ?_, ?_, hws⟩
  · have hfg : (⨆ i ∈ s, i).FG := by
      refine Submodule.fg_biSup s (fun i => i) (fun i hi => ?_)
      obtain ⟨hfin, -⟩ := hs hi
      exact (Submodule.fg_iff_finiteDimensional i).2 hfin
    exact (Submodule.fg_iff_finiteDimensional _).1 hfg
  · intro g hg v hv
    have hle : (⨆ i ∈ s, i) ≤ (⨆ i ∈ s, i).comap ((σ g : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine iSup₂_le fun i hi => ?_
      obtain ⟨-, hstab, -⟩ := hs hi
      intro x hx
      exact (le_iSup₂ (f := fun j (_ : j ∈ s) => j) i hi) (hstab g hg x hx)
    exact hle hv

theorem isKFin_of_mem_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H), w ∈ lowKSub ε lam σ → IsKFin ε σ w := by
  intro n ε lam H _ _ σ w hw
  obtain ⟨S, hfin, hstab, hwS⟩ := exists_kStable_of_mem_lowKSub n ε lam H σ w hw
  exact ⟨S, hfin, hwS, hstab⟩

end GlobalTheory
