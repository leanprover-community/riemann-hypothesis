module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementK
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.KSum

open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)

theorem coeff_two_pSeries (L : PeriodPair) :
    PowerSeries.coeff 2 (pSeries L) = L.g₂ / 20 := by
  rw [Formalism.L2.Th1.F.pSeriesCoeff L 2, if_neg (by norm_num)]
  first
    | (simp only [PeriodPair.g₂]; push_cast; ring)
    | (unfold PeriodPair.g₂; push_cast; ring)
    | (norm_num [PeriodPair.g₂]; ring)

theorem coeff_two_shift (L : PeriodPair) (P : ℂ) (hP : P ∉ L.lattice) :
    PowerSeries.coeff 2 (taylor0 (fun z => L.weierstrassP (z + P)))
      = 3 * L.weierstrassP P ^ 2 - L.g₂ / 4 := by
  unfold taylor0
  rw [PowerSeries.coeff_mk]
  have hc : IsClosed (L.lattice : Set ℂ) := by
    first
      | exact L.isClosed_lattice
      | exact PeriodPair.isClosed_lattice L
      | (haveI : DiscreteTopology L.lattice.toAddSubgroup := inferInstanceAs (DiscreteTopology L.lattice)
         exact (L.lattice.toAddSubgroup).isClosed_of_discreteTopology)
  have hopen : ∀ᶠ w in nhds P, w ∉ L.lattice := hc.isOpen_compl.mem_nhds hP
  have hev : deriv L.weierstrassP =ᶠ[nhds P] L.derivWeierstrassP := by
    filter_upwards [hopen] with w hw
    first
      | exact (L.hasDerivAt_weierstrassP hw).deriv
      | exact (PeriodPair.hasDerivAt_weierstrassP L hw).deriv
      | exact congrFun L.deriv_weierstrassP w
  have h1 : deriv (fun z => L.weierstrassP (z + P)) = fun w => deriv L.weierstrassP (w + P) := by
    funext w
    rw [deriv_comp_add_const]
  have h2 : deriv (fun w => deriv L.weierstrassP (w + P)) 0 = 6 * L.weierstrassP P ^ 2 - L.g₂ / 2 := by
    rw [deriv_comp_add_const, zero_add, hev.deriv_eq]
    exact (Formalism.L2.Th1.F.pSecond L P hP).deriv
  have h3 : iteratedDeriv 2 (fun z => L.weierstrassP (z + P)) =
      deriv (deriv (fun z => L.weierstrassP (z + P))) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h3, h1, h2, Nat.factorial_two]
  push_cast
  ring

theorem kappa_sum_holds : KappaSum := by
  intro L α S hα hst hS
  obtain ⟨neg, -, -, -, h3⟩ := Formalism.L2.Th1.F.endoZInstance L α S hα hst hS
  have h4 := congrArg (PowerSeries.coeff 2) h3

  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_add (f := _), map_sum,
  coeff_two_pSeries] at h4
  have h5 : ∀ P : S, PowerSeries.coeff 2
      (taylor0 (fun z => L.weierstrassP (z + (P : ℂ))) - PowerSeries.C (L.weierstrassP (P : ℂ)))
        = 3 * L.weierstrassP (P : ℂ) ^ 2 - L.g₂ / 4 := by
    intro P
    rw [map_sub, coeff_two_shift L P (hS.1 P P.2).2, PowerSeries.coeff_C]
    simp
  rw [Finset.sum_congr rfl (fun P _ => h5 P),
    Finset.sum_coe_sort S (fun P => 3 * L.weierstrassP P ^ 2 - L.g₂ / 4)] at h4
  linear_combination -h4

end Formalism.L2.Th1.B.KSum
