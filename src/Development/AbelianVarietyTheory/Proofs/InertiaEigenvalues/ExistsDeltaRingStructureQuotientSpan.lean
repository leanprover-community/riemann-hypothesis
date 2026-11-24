module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.delta_quot_span : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (s : Set A), (∀ x ∈ s, D.δ x ∈ Ideal.span s) → ∃ D' : Delta l (A ⧸ Ideal.span s), IsδMap D D' (Ideal.Quotient.mk (Ideal.span s)) := by
  intro l _ A _ D s hs
  let N := Ideal.span s
  let g : A →+* W2 l (A ⧸ N) := (W2.map (Ideal.Quotient.mk N)).comp (deltaSectionToWittLengthTwo D)
  have hg : ∀ a ∈ N, g a = 0 := by
    intro a ha
    have hle : N ≤ RingHom.ker g := by
      refine Ideal.span_le.2 fun x hx => ?_
      rw [SetLike.mem_coe, RingHom.mem_ker]
      refine W2.ext ?_ ?_
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (hs x hx)
    exact hle ha
  let sec : A ⧸ N →+* W2 l (A ⧸ N) := Ideal.Quotient.lift N g hg
  have hsec : ∀ a, (sec a).fst = a := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  exact ⟨deltaStructureOfWittLengthTwoSection sec hsec, fun a => rfl⟩
