module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem BdCocycle.proof (hDense : RegYoDense.Statement) (hHolo : BdEqHolo.Statement) :
    BdCocycle.Statement := by
  intro X _ D A R g hg hEq j k l
  have hOopen : IsOpen (bdDom R j ∩ bdDom R k ∩ bdDom R l) :=
    ((isOpen_bdDom R j).inter (isOpen_bdDom R k)).inter (isOpen_bdDom R l)
  have hOjl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R l := fun _ hy => ⟨hy.1.1, hy.2⟩
  have hOjk : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R k := fun _ hy => hy.1
  have hOkl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R k ∩ bdDom R l := fun _ hy => ⟨hy.1.2, hy.2⟩
  have hYo : Set.EqOn (g j l) (fun y => g j k y * g k l y)
      ((bdDom R j ∩ bdDom R k ∩ bdDom R l) ∩ R.Yo) := by
    rintro y ⟨hyO, hyY⟩
    have hne : bdEq R l y ≠ 0 := fun h0 => ((hHolo D A R l).2 y hyO.2).1 h0 hyY
    have h1 := hEq j l y (hOjl hyO)
    have h2 := hEq j k y (hOjk hyO)
    have h3 := hEq k l y (hOkl hyO)
    apply mul_right_cancel₀ hne
    show g j l y * bdEq R l y = g j k y * g k l y * bdEq R l y
    rw [← h1, h2, h3, mul_assoc]
  have hall := hYo.of_subset_closure ((hg j l).mono hOjl)
    (((hg j k).mono hOjk).mul ((hg k l).mono hOkl)) Set.inter_subset_left
    ((hDense D A R).open_subset_closure_inter hOopen)
  intro y hy
  exact hall hy

end GroundTheory.Heights₂.Heights.AnalyticLimit
