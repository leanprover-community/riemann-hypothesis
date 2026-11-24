module

public import ReciprocityTheory.NeutralLocalFields.Duality
public import ReciprocityTheory.GroupCohomology.ContinuousContractNth
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem kbarRep_contAction : ReciprocityTheory.Gal.ContAction (kbarRep p K) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  show Continuous fun q : GK p K × KbarMult p => kbarRep p K q.1 q.2
  rw [continuous_prod_of_discrete_right]
  intro y
  rw [continuous_discrete_rng]
  intro x
  rw [isOpen_iff_mem_nhds]
  intro g0 hg0
  have hop := stabilizer_isOpen_of_isIntegral (K := K) (L := PadicAlgCl p)
    (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
  have hn : (fun g : GK p K => g0⁻¹ * g) ⁻¹' (MulAction.stabilizer (GK p K)
      (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) : Set (GK p K)) ∈ nhds g0 :=
    (hop.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : (g0⁻¹ * g) (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
      = (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := hg
  have hgg : g (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
      = g0 (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := by
    have := congrArg g0 hg'
    rw [AlgEquiv.mul_apply] at this
    rw [← this]
    exact (g0.apply_symm_apply _).symm
  have hxy : kbarRep p K g y = kbarRep p K g0 y := Units.ext hgg
  show kbarRep p K g y = x
  rw [hxy]
  exact hg0

noncomputable def kbarT : TRep ℤ (GK p K) where
  V := KbarMult p
  rho := kbarRep p K
  cont := kbarRep_contAction p K

scoped instance : DiscreteTopology (kbarT p K).V := inferInstanceAs (DiscreteTopology (KbarMult p))

end ReciprocityTheory.DiscreteGroups.LocalClassField
