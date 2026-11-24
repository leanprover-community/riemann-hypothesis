module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice.BaseChange

theorem gaussAbs_eq_iSup {K ι : Type} [Field K] [NumberField K] (v : FinitePlace K) (g : MvPolynomial ι K)
    (s : Finset (ι →₀ ℕ)) (hs : g.support ⊆ s) (hne : s.Nonempty) :
    gaussAbs v g = ⨆ k : s, v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ)) := by
  classical
  have : Nonempty s := hne.to_subtype
  have hsup : (g.support.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) = s.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal := by
    refine le_antisymm (Finset.sup_mono hs) (Finset.sup_le fun m hm => ?_)
    by_cases hm' : m ∈ g.support
    · exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) hm'
    · rw [MvPolynomial.notMem_support_iff.1 hm', map_zero, Real.toNNReal_zero]
      exact bot_le
  unfold gaussAbs
  rw [hsup]
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup s hne fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal
  rw [hkeq, Real.coe_toNNReal _ (apply_nonneg _ _)]
  refine le_antisymm (le_ciSup (f := fun k : s => v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ))) (Set.finite_range _).bddAbove ⟨k, hk⟩)
    (ciSup_le fun m => ?_)
  have h1 : (v (AddMonoidAlgebra.coeff g (m : ι →₀ ℕ))).toNNReal ≤ (v (AddMonoidAlgebra.coeff g k)).toNNReal := by
    rw [← hkeq]; exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) m.2
  have h2 := (Real.toNNReal_le_toNNReal_iff (apply_nonneg _ _)).1 h1
  exact h2

end GlobalTheory.HSChoice.BaseChange
