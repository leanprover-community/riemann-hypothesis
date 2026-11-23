module

public import ReciprocityTheory.SemistableReduction.LatSemiSt
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
public import ReciprocityTheory.SemistableReduction.EmbMatMulVecInjective
public import ReciprocityTheory.SemistableReduction.ExistsIntSmulMemSpan

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

open NumberField

theorem degAdd_holds : DegAddStatement := by
  intro K _ _ r k m H L b c hH hL hb hc hlin hspan
  obtain ⟨hbi, -, hdis⟩ := DegAdd.indep_parts hlin
  have hidx := DegAdd.index_split L b c hb hc hdis
  have hne := DegAdd.relIndex_ne_zero_of_fg L hL (Fin.append b c) hspan
  rw [hidx] at hne
  have h1 := left_ne_zero_of_mul hne
  have h2 := right_ne_zero_of_mul hne
  have hs : ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ (Fin.append b c)).det.re =
      ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ b).det.re +
        ∑ σ : K →+* ℂ, Real.log (quotGramC (H σ) σ b c).det.re := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => DegAdd.log_det_gram_append (H σ) σ b c (hH σ) hbi hlin
  unfold latDeg quotDeg
  rw [hidx, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr h1) (Nat.cast_ne_zero.mpr h2), hs]
  ring

end ReciprocityTheory.MultiplicativeHeights
