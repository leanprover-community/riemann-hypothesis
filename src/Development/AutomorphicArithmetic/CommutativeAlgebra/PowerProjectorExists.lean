module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundleStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowerOfAbelianSchemeProjective
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IteratedFiberPowerZeroIsIsoAndSuccIsPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open UpperTheory.Gal.Int.Geo

private theorem relDim_pow {S : Scheme.{0}} (A : Over S) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) (k : ℕ) :
    SmoothOfRelativeDimension (k * g) (GlobalTheory.KS.pow A k).hom := by
  induction k with
  | zero =>
    obtain ⟨h0, -⟩ := UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback A
    simp only [zero_mul]
    infer_instance
  | succ m ih =>
    obtain ⟨-, hs⟩ := UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback A
    obtain ⟨u, v, hpb, hcomp⟩ := hs m
    have hu : SmoothOfRelativeDimension g u :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback hpb.flip hg
    rw [← hcomp, Nat.succ_mul, Nat.add_comm]
    infer_instance

theorem UpperTheory.power_projector_exists :
    PowProj := by
  intro q _ D R _ _ b N _ _ X s o k
  letI := o.grp
  haveI := o.comm
  have hT := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle q D R b N X s o
  refine ⟨fun hs => GlobalTheory.KS.isProjOver_pow R X s hs o.A o.ab _ hT.2 o.ample k, ?_⟩
  intro d hd
  haveI := relDim_pow o.A D.g hT.1 k
  exact ⟨k * D.g + d, inferInstance⟩
