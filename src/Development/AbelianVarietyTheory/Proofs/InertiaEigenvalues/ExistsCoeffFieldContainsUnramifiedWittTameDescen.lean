module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUltrametricDistFinExt
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoeff

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a], e + 1 = l ^ a → ¬ l ∣ a → ∀ LL : FinExt l,
    (∃ LL' : FinExt l, LL.1 ≤ LL'.1 ∧ HasUnr a LL') ∧ (HasUnr a LL → TameDescentExponentData ↥LL.1 l e a) := by
  intro l _ a e _ h1 h2 LL
  refine ⟨?_, fun hU => ?_⟩
  · have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    have : FiniteDimensional ℚ_[l] ↥(Kunr l a) := (unrExt l a).2
    exact ⟨⟨LL.1 ⊔ Kunr l a, inferInstance⟩, le_sup_left, ⟨le_sup_right⟩⟩
  · obtain ⟨_, ω, hω, -, -⟩ := exists_gen l a
    have hlt := one_lt_pow_l l a
    have hmem : ω ∈ LL.1 := HasUnr.le (a := a) (IntermediateField.subset_adjoin _ _ (show ω ^ l ^ a = ω by
      rw [← Nat.sub_add_cancel hlt.le, pow_succ, hω.pow_eq_one, one_mul]))
    have he : e = l ^ a - 1 := by omega
    exact
      { succ_eq := h1
        not_dvd := h2
        finite := LL.2
        prim := ⟨⟨ω, hmem⟩, he ▸ (IsPrimitiveRoot.map_iff_of_injective (f := LL.1.val)
          Subtype.val_injective).1 hω⟩ }

end GlobalTheory.TameCoeff
