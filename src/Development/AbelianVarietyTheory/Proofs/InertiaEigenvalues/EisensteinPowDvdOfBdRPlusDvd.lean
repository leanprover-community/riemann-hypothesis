module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfProperties
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.DivTransfer

theorem div_transfer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), aDp l (bk.ev bk.E) ≠ 0 ∧
    ∀ (m : ℕ) (s : bk.S), aDp l (bk.ev bk.E) ^ m ∣ aDp l (bk.ev s) → bk.E ^ m ∣ s := by
  intro l _ K bk

  have hF := fun m => (GlobalTheory.AinfEPow.ePow_facts l K bk m).2.2.1
  have hS := fun m => (GlobalTheory.AinfEPow.ePow_facts l K bk m).2.1
  refine ⟨fun h0 => ?_, fun m s hd => ?_⟩
  · have h2 : bk.ev bk.E ^ 2 ∣ bk.ev bk.E := (hF 2 (bk.ev bk.E)).1 (by rw [h0]; exact Ideal.zero_mem _)
    obtain ⟨c, hc⟩ := hS 2 bk.E h2
    have h1 : bk.E * 1 = bk.E * (bk.E * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
    have hu : bk.E * c = 1 := (mul_left_cancel₀ bk.E_ne_zero h1).symm
    have hmem : (1 : Ainf l) ∈ RingHom.ker (Per.θ l) := by
      rw [← bk.span_ev, ← map_one bk.ev, ← hu, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [RingHom.mem_ker, map_one] at hmem
    exact one_ne_zero hmem
  · apply hS m s
    apply (hF m _).1
    obtain ⟨c, hc⟩ := hd
    rw [hc, ← map_pow, ← map_pow]
    exact Ideal.mul_mem_right _ _ ((hF m _).2 (by rw [map_pow]))

end GlobalTheory.BSP.DivTransfer
