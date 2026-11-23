module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.yLoc_pf :
    PfHecke → ProdOp → YLoc := by
  intro hP hO E _ _ _ n S Z N hS hZ hG π y i hi f hf x hx
  classical
  obtain ⟨w, b⟩ := i
  let F : ∀ w', Bool → _ := fun w' b' =>
    if h : w' = w ∧ b' = b then h.1 ▸ f else ((N w' : Set _).indicator 1)
  have hFi : F w b = f := by simp [F]
  have hFam : Fam S N {(w, b)} F := by
    refine ⟨?_, ?_⟩
    · intro j hj
      obtain rfl := Finset.mem_singleton.mp hj
      exact ⟨hi, by simpa [hFi] using hf⟩
    · rintro ⟨w', b'⟩ _ hj
      have hne : ¬ (w' = w ∧ b' = b) := by
        rintro ⟨rfl, rfl⟩
        exact hj (Finset.mem_singleton_self _)
      simp [F, hne]
  have h1 := hO E n S Z N hS hZ hG {(w, b)} F hFam x (y.fix hx)
  have h2 := y.act _ (hP E n S Z N hS hZ hG {(w, b)} F hFam) ⟨x, hx⟩
  have h3 : Lw N w b f x = ((y.r (pf S F) ⟨x, hx⟩ : y.Y) : _) := by
    rw [h2]
    show _ = Lv _ _ _ x
    rw [h1]
    simp [hFi]
  show Lw N w b f x ∈ y.Y
  rw [h3]
  exact (y.r (pf S F) ⟨x, hx⟩).2
