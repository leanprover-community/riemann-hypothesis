module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

theorem posEx : PosEx := by
  intro F E _ _ _ _ _ σ hc δ hδ hs
  have key : ∀ w : InfinitePlace F, ∃ t : EmbOver E w, ∃ c : ℝ, 0 < c ∧ Complex.I * t.1 δ = c := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    have hconj : ∀ (t : E →+* ℂ) (x : E), t (σ x) = star (t x) := hc.2.2.2
    set z : ℂ := τ.1 δ with hz
    have hstar : star z = -z := by
      rw [hz, ← hconj, hs, map_neg]
    have hre : z.re = 0 := by
      have := congrArg Complex.re hstar
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
      linarith
    have hz0 : z ≠ 0 := by
      rw [hz]
      exact (map_ne_zero τ.1).2 hδ
    have him : z.im ≠ 0 := fun h => hz0 (Complex.ext hre h)
    have hI : Complex.I * z = ((-z.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨τ, -z.im, by linarith, hI⟩
    · refine ⟨⟨τ.1.comp (σ : E →+* E), ?_⟩, z.im, h, ?_⟩
      · refine Eq.trans ?_ τ.2
        ext x
        simp
      · have : (τ.1.comp (σ : E →+* E)) δ = -z := by
          simp [hs, hz]
        rw [this, mul_neg, hI]
        simp
  choose emb hemb using key
  exact ⟨emb, hemb⟩

end UpperTheory.Gal.TP.Skew

end
