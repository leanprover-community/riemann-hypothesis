module

public import Formalism.WachLatticeTwists.HodgeTateChains.Statement
public import Formalism.WindowSums.AnnihilatorPolynomials.ValProd
public import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

theorem rVal : StatRVal := by
  intro ℓ _ w m hm h2 hw U i
  have key := (Formalism.WindowSums.valProd_of Formalism.WindowSums.valuation_zpow_sub_one ℓ w m hm h2 hw).2
    ((U.erase i).map ⟨fun a => a - i, sub_left_injective⟩) (by
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
      intro a ha h0
      exact (Finset.mem_erase.1 ha).1 (by omega))
  have hev : (Rpoly ℓ w U i).eval 1 =
      ∏ a ∈ U.erase i, (1 - ((w ^ (-(a - i)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
    unfold Rpoly
    rw [eval_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [neg_sub]
  rw [Finset.prod_map, Finset.sum_map, Finset.card_map] at key
  simp only [Function.Embedding.coeFn_mk] at key
  rw [hev]
  refine ⟨key.1, ?_⟩
  rw [key.2]
  unfold rI
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
