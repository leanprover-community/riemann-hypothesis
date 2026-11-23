module

public import Formalism.HarderNarasimhan.StatementPl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteInvLeft
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop.DimLogTop

theorem log_size_le (f r L kap S : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hk0 : 0 ≤ kap)
    (hk : Real.log kap ≤ 2 * L) (hfr : Real.log (f * r) ≤ L) (hS0 : 0 ≤ S)
    (hS : S ≤ (f * r * L) ^ 2 * kap + 6 * f * r ^ 2) : Real.log S ≤ 20 * L := by
  rcases hS0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; linarith
  have hfr0 : 0 < f * r := by positivity
  have e1 : f * r ≤ Real.exp L := (Real.log_le_iff_le_exp hfr0).1 hfr
  have e2 : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have e3 : kap ≤ Real.exp (2 * L) := by
    rcases hk0.eq_or_lt with h0 | h0
    · rw [← h0]; exact (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp h0).1 hk
  have e4 : (7 : ℝ) ≤ Real.exp (6 * L) := by linarith [Real.add_one_le_exp (6 * L)]
  have hE : Real.exp (6 * L) = Real.exp L ^ 2 * Real.exp L ^ 2 * Real.exp (2 * L) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  have hE2 : Real.exp L ^ 2 ≤ Real.exp (6 * L) := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; linarith)
  have a1 : (f * r * L) ^ 2 * kap ≤ Real.exp (6 * L) := by
    rw [hE, mul_pow]
    have : (f * r) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ hfr0.le e1 2
    have : L ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ (by linarith) e2 2
    gcongr
  have a2 : 6 * f * r ^ 2 ≤ 6 * Real.exp (6 * L) := by
    have : f * r ^ 2 ≤ (f * r) ^ 2 := by nlinarith
    have : (f * r) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ hfr0.le e1 2
    nlinarith
  have a3 : S ≤ Real.exp (12 * L) := by
    have : Real.exp (12 * L) = Real.exp (6 * L) * Real.exp (6 * L) := by rw [← Real.exp_add]; ring_nf
    rw [this]
    have := Real.exp_pos (6 * L)
    nlinarith
  have := (Real.log_le_iff_le_exp h).2 a3
  linarith

theorem cube_le (Cb L Zb : ℝ) (hL : Cb ≤ L) (hL1 : 1 ≤ L) (hZ : L ≤ Zb) : Cb * Zb ^ 3 ≤ Zb ^ 12 := by
  have h1 : 1 ≤ Zb := hL1.trans hZ
  have h9 : Zb ≤ Zb ^ 9 := le_self_pow₀ h1 (by norm_num)
  have h3 : 0 ≤ Zb ^ 3 := by positivity
  calc Cb * Zb ^ 3 ≤ Zb ^ 9 * Zb ^ 3 := mul_le_mul_of_nonneg_right (by linarith) h3
    _ = Zb ^ 12 := by ring

theorem rkK_eq_finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (L : Submodule (𝓞 K) V) (h : Submodule.span K (L : Set V) = ⊤) :
    Formalism.HN.rkK L = Module.finrank K V := by
  unfold Formalism.HN.rkK
  rw [h, finrank_top]

end GlobalTheory.CovTop.DimLogTop

end
