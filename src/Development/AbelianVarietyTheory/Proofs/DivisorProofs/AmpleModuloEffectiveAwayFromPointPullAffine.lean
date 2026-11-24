module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.AmplePull

theorem ampleAt_pull : ∀ (Y X : Scheme.{0}) (π : X ⟶ Y) [IsAffineHom π] (N : LB Y), N.IsLB → ∀ x : X,
    AmpleAt N (π x) → AmpleAt (N.pull π) x := by
  intro Y X π _ N hN x h
  obtain ⟨m, A, s, hm, hA, hAmp, hy⟩ := h
  have hNm : (lbPow N m).IsLB := isLB_lbPow hN m
  have hP : (LB.div (lbPow N m) A).IsLB := LB.isLB_div hNm hA
  have hN' : (N.pull π).IsLB := LB.isLB_pull hN π
  have hA' : (A.pull π).IsLB := LB.isLB_pull hA π
  have hNm' : (lbPow (N.pull π) m).IsLB := isLB_lbPow hN' m
  have hQ : (LB.div (lbPow (N.pull π) m) (A.pull π)).IsLB := LB.isLB_div hNm' hA'
  have iso : LBIso (LB.div (lbPow (N.pull π) m) (A.pull π)) ((LB.div (lbPow N m) A).pull π) := by
    rw [← cls_eq_iff hQ (LB.isLB_pull hP π), cls_div hNm' hA' hQ, cls_pull hP π, cls_div hNm hA hP,
      cls_lbPow hN' m hNm', cls_pull hN π hN', cls_pull hA π hA', cls_lbPow hN m hNm, map_sub, map_nsmul]
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hQ (LB.isLB_pull hP π) iso (ZM.RepBC.secPull _ π s)
  refine ⟨m, A.pull π, t, hm, hA', hAmp.pull_of_isAffineHom π, ?_⟩
  rw [ht, GlobalTheory.ZV.GraphSystem.nonzeroLocus_pull]
  exact hy

end GlobalTheory.AmplePull
