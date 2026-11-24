module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfinite
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem zero_of_powers_compact {G : Type*} [Monoid G] [TopologicalSpace G] (f : G → ℝ) (hf : Continuous f)
    (hm : ∀ x y, f (x * y) = f x + f y) (S : Set G) (hS : IsCompact S) (k : G) (hk : ∀ m : ℕ, k ^ m ∈ S) : f k = 0 := by
  obtain ⟨C, hC⟩ := (hS.image hf).isBounded.exists_norm_le
  have h1 : f 1 = 0 := by
    have := hm 1 1
    rw [mul_one] at this
    linarith
  have hp : ∀ m : ℕ, f (k ^ m) = m * f k := by
    intro m
    induction m with
    | zero => simp [h1]
    | succ m ih => rw [pow_succ, hm, ih]; push_cast; ring
  by_contra hne
  have hpos : 0 < |f k| := abs_pos.2 hne
  obtain ⟨m, hmC⟩ := exists_nat_gt (C / |f k|)
  have hb := hC _ ⟨k ^ m, hk m, rfl⟩
  rw [hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at hb
  rw [div_lt_iff₀ hpos] at hmC
  linarith

private theorem continuous_kI (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (kI E n) := by
  have hu : Continuous (Unitary.toUnits : Kinf E n → _) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  exact GlobalTheory.CuspQuot.continuous_infGL.comp hu

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.detZero_pf :
    DetZero := by
  intro E _ _ _ n
  have hc := DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)
  have hm := DiscreteGroups.T1.G.Dcy.logAbs_det_mul' (E := E) (n := n)
  refine ⟨fun k => ?_, fun K hK k hk => ?_⟩
  · haveI : CompactSpace (Kinf E n) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n
    exact zero_of_powers_compact _ hc hm (Set.range (kI E n)) (isCompact_range (continuous_kI E n)) _
      fun m => ⟨k ^ m, map_pow _ _ _⟩
  · exact zero_of_powers_compact _ hc hm (finGL E n '' (K : Set _))
      (hK.image GlobalTheory.BCT.GlobLev.continuous_finGL_ad) _ fun m => ⟨k ^ m, K.pow_mem hk m, map_pow _ _ _⟩
