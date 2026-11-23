module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.AutNew
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CapTwo
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V UpperTheory.V.Af

open scoped BigOperators

theorem UpperTheory.V.Af.Rn.hermOf :
    UpperTheory.V.Af.Rn.HermOf := by
  intro c π hπ
  refine Br.hermEx ℚ 2 one_le_two π fun φ hφ => ?_
  classical
  have hX : TR.lie ℚ 2 (TR.oneL ℚ 2) = ∑ i, TR.lieS ℚ 2 i i 1 := by

    simp only [TR.lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.sum_single_one (m := Fin 2) (α := TR.Rinf ℚ)).symm
  have h1 : ∀ i, TR.lieS ℚ 2 i i 1 = TR.Eop Rat.infinitePlace i i := fun i => by
    rw [TR.Eop_eq]
    congr 1
    funext v
    rw [Subsingleton.elim v Rat.infinitePlace]
    simp
  rw [hX, Fin.sum_univ_two, h1, h1, LinearMap.add_apply]
  rw [(Br.capTwo ℚ π Rat.infinitePlace _ _ (hπ Rat.infinitePlace) φ hφ).1,
    add_neg_cancel, zero_smul]
