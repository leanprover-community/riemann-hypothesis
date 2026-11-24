module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleTwistLarger

theorem isAmpleLB_tens_lbPow_succ {S : Scheme.{0}} {L M : LB S} {N m : ℕ} (hL : L.IsLB) (hM : M.IsLB)
    (hG : GlobalTheory.IsGenerated (lbPow L N)) (hA : GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * m)) M)) :
    GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * (m + 1))) M) := by
  have h₁ := GlobalTheory.isLB_lbPow hL (N * (m + 1))
  have h₂ := GlobalTheory.isLB_lbPow hL (N * m)
  have h₃ := GlobalTheory.isLB_lbPow hL N
  have hT := GlobalTheory.CechPic.isLB_tens h₁ hM
  have hS := GlobalTheory.CechPic.isLB_tens h₂ hM
  have hq := LB.isLB_div hT hS
  refine hA.tensor_isGenerated hG hT ((GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_div hq h₃)).1 ?_)
  rw [GlobalTheory.CechPic.cls_div hq h₃, GlobalTheory.CechPic.cls_div hT hS, GlobalTheory.CechPic.cls_tens h₁ hM,
    GlobalTheory.CechPic.cls_tens h₂ hM, GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_lbPow hL,
    Nat.mul_succ, add_smul]
  abel

theorem isAmpleLB_tens_lbPow_of_le : ∀ (S : Scheme.{0}) (L M : LB S) (N k : ℕ), L.IsLB → M.IsLB → GlobalTheory.IsGenerated (lbPow L N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k)) M) → ∀ k', k ≤ k' → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k')) M) := by
  intro S L M N k hL hM hG hA k' hk
  induction k', hk using Nat.le_induction with
  | base => exact hA
  | succ m _ ih => exact isAmpleLB_tens_lbPow_succ hL hM hG ih

end GlobalTheory.AmpleTwistLarger
