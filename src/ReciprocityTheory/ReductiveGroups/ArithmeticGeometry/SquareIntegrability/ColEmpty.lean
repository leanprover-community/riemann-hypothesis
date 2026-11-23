module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropASt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.EpsilonLeHalf

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

theorem colTorus (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColTorusStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI c hc σ x0 u hx0 hu n hn hun hc6
  exact ct_core hP hGT hA hS hI c hc σ x0 u hx0 hu n hn hun hc6

theorem colAbel (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColAbelStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI c hc σ ξ _ hξ1 hξI
  exact cab_core hP hGT hA hS hI c hc σ ξ hξ1 hξI

theorem colEmpty (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColEmptyStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hM : 0 ≤ M1 (E := E) P.m := by
    unfold M1 PT.rd
    positivity
  have hu0 : IsU I (0 : Vsp X.dim) 0 := ⟨Submodule.zero_mem _, fun a _ => by simp [Hf]⟩
  obtain ⟨s', hs', ζ, hζ, hd, hl⟩ := ct_core hP hGT hA hS hI 0 (Nat.zero_le _) σ 0 0
    (Submodule.zero_mem _) hu0 1 le_rfl (by norm_num)
    (fun y _ uy _ => by simpa using mul_nonneg hM (sq_nonneg ‖uy‖))
  have h0 := hd Fin.elim0 (fun k => k.elim0)
  simp only [d1, iteratedFDeriv_zero_apply, pow_zero, Finset.univ_eq_empty, Finset.prod_empty,
    mul_one] at h0
  refine ⟨s', hs', ?_, by simpa using hl⟩
  have h1 := norm_sub_norm_le ζ (s' 0)
  rw [norm_sub_rev] at h1
  have h2 := epsilon_le_half P
  linarith

end ReciprocityTheory.ChartRestriction.G.I2
