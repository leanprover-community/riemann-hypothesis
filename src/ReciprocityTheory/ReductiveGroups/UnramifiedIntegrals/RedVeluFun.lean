module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
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
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedHalf

@[expose] public section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem velu_pair (L : PeriodPair) (z P : ℂ) (hz : z ∉ L.lattice) (hP : P ∉ L.lattice)
    (hp : z + P ∉ L.lattice) (hm : z - P ∉ L.lattice) :
    (L.weierstrassP (z + P) - L.weierstrassP P) + (L.weierstrassP (z + -P) - L.weierstrassP (-P))
      = fW L.g₂ L.g₃ (L.weierstrassP P) / (L.weierstrassP z - L.weierstrassP P) ^ 2
        + fW' L.g₂ (L.weierstrassP P) / (2 * (L.weierstrassP z - L.weierstrassP P)) := by
  have hne := Formalism.L2.Th1.E.AddThm.P_sub_ne L z P hz hP hp hm
  have hP' : -P ∉ L.lattice := fun h => hP (by simpa using L.lattice.neg_mem h)
  have h1 := Formalism.L2.Th1.E.AddThm.P_add L z P hz hP hp hm
  have h2 := Formalism.L2.Th1.E.AddThm.P_add L z (-P) hz hP' (by simpa [sub_eq_add_neg] using hm)
    (by simpa using hp)
  rw [L.weierstrassP_neg, L.derivWeierstrassP_neg] at h2
  have hY := L.derivWeierstrassP_sq z hz
  have hy := L.derivWeierstrassP_sq P hP
  rw [L.weierstrassP_neg, h1, h2]
  unfold fW fW'
  generalize L.weierstrassP z = X at *
  generalize L.weierstrassP P = x at *
  generalize L.derivWeierstrassP z = Y at *
  generalize L.derivWeierstrassP P = y at *
  field_simp
  linear_combination 4 * hY + 4 * hy

theorem velu_fun (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) (z : ℂ) (hz : α * z ∉ L.lattice) :
    α ^ 2 * L.weierstrassP (α * z) = veluFun L.g₂ L.g₃ (xsOf L T) (L.weierstrassP z) := by
  obtain ⟨hK, hdisj⟩ := hT.kerReps
  have hzL : z ∉ L.lattice := fun h => hz (hs z h)
  rw [isogenyP L α _ hα hs hK z hz, Finset.sum_union hdisj,
    Finset.sum_image (by intro a _ b _ h; exact neg_injective h)]
  simp only [veluFun, xsOf]
  rw [Finset.sum_image (by intro a ha b hb h; exact hT.injOn ha hb h)]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hαP, h2P⟩ := hT.1 P hP

  have hPL : P ∉ L.lattice := fun h => h2P (by rw [two_mul]; exact L.lattice.add_mem h h)

  have hp : z + P ∉ L.lattice := fun h => hz (by
    have := L.lattice.sub_mem (hs _ h) hαP
    rwa [mul_add, add_sub_cancel_right] at this)
  have hm : z - P ∉ L.lattice := fun h => hz (by
    have := L.lattice.add_mem (hs _ h) hαP
    rwa [mul_sub, sub_add_cancel] at this)
  exact velu_pair L z P hzL hPL hp hm

end ReciprocityTheory.ChartRestriction.L1
