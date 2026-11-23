module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

theorem intLog_shortW (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K)
    (h2 : ‖(2 : K)‖ = 1) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ ≤ 1) :
    IntLog (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3))
      (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW g2 g3)) := by
  set W := Formalism.L2.Th1.A.shortW g2 g3 with hW
  have h4 : ‖(4 : K)‖ = 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, norm_mul, h2, one_mul]
  have hmem : ∀ x : K, ‖x‖ ≤ 1 → x ∈ Formalism.G.unitBall K := fun x hx => hx
  have ha4 : W.a₄ ∈ Formalism.G.unitBall K := by
    apply hmem
    show ‖-g2 / 4‖ ≤ 1
    rw [norm_div, norm_neg, h4, div_one]; exact hg2
  have ha6 : W.a₆ ∈ Formalism.G.unitBall K := by
    apply hmem
    show ‖-g3 / 4‖ ≤ 1
    rw [norm_div, norm_neg, h4, div_one]; exact hg3
  have h0 : (0 : K) ∈ Formalism.G.unitBall K := (Formalism.G.unitBall K).zero_mem
  have hcm := Formalism.L2.Th1.A.coeffMem K W (Formalism.G.unitBall K) h0 h0 h0 ha4 ha6
  obtain ⟨hl0, hl1, hlom, -⟩ := Formalism.L2.Th1.A.logSpec K W
  obtain ⟨he0, -, hle, hel, -⟩ := Formalism.L2.Th1.A.expSpec K W
  obtain ⟨-, hfgl⟩ := Formalism.L2.Th1.A.fglLog K W
  refine ⟨⟨hl0, hl1, he0, hel, hle⟩, ?_, ?_⟩
  · intro n
    rw [hlom]
    exact hcm.2.2.2.2.1 n
  · intro n
    unfold Formalism.L2.Th1.C.fadd
    rw [← hfgl]
    exact hcm.2.2.2.2.2.2.1 n

end GlobalTheory.Honda
