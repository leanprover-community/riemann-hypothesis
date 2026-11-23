module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndRaw

@[expose] public section

set_option autoImplicit false

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart)

namespace GlobalTheory

theorem bilinPart_canonGauge_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → (∀ i j, ((bilinPart k h)ᵀ - bilinPart k h) i j ∈ (algebraMap R k).range) ∧ (∀ a : O, (∀ i j, ((dAct k B a)ᵀ * bilinPart k h - bilinPart k h * dAct k B (star a)) i j ∈ (algebraMap R k).range)) ∧ (∀ a : O, (∀ i j, (dAct k B a) i j ∈ (algebraMap R k).range)) ∧ dAct k B 1 = 1 ∧ (∀ a b : O, dAct k B (a + b) = dAct k B a + dAct k B b) ∧ ∀ a b : O, dAct k B (a * b) = dAct k B a * dAct k B b := by
  intro R _ d O _ _ k _ _ _ B h hc
  refine ⟨fun i j => ?_, fun a i j => ?_, fun a i j => ?_, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_one k B,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add k B, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul k B⟩
  · have e := congrArg (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1)) hc.sy
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_expS_two _ (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_swap_sub_low h hc.ax0 hc.ax1) _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz i j), map_sub, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ev_swap', coeff_map,
      Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single, add_comm (Finsupp.single (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.swE d _) 1)] at e
    exact ⟨_, e⟩
  · obtain ⟨r, hr⟩ := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.M_int B h hc a j i
    refine ⟨-r, ?_⟩
    rw [map_neg, hr]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gaugeBilinearTerm_eq_neg_double_sum, bilinPart,
      neg_mul, Finset.sum_neg_distrib, mul_comm (dAct k B _ _ _)]
    ring
  · exact ⟨coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act a i), by
      unfold dAct FB.actK; rw [coeff_map]⟩

end GlobalTheory
