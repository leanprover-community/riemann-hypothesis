module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleByO1
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjVar

theorem exists_generating_secs_tens_lbPow_O1 : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ (n : ℕ) (u : Fin n → (CechPic.tens L (lbPow ((ProjSpace.O1 ℂ Y.N).pull Y.ι) m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro Y L hL
  obtain ⟨s, hs⟩ := exists_veryAmpleBy_O1 Y
  have hH : ((ProjSpace.O1 ℂ Y.N).pull Y.ι).IsLB := pull_isLB (ProjSpace.O1_isLB ℂ Y.N) _
  generalize (ProjSpace.O1 ℂ Y.N).pull Y.ι = H at s hs hH
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated ℂ Y.X Y.str H _ s hH hs L hL
  refine ⟨t₀.toNat, fun m hm => ?_⟩
  obtain ⟨n, u, hu⟩ := ht m (by omega)
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens L (lbPow H m)).IsLB := isLB_tens hL hP
  have e : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) =
      cls L hL - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hL (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hL hH _)
  have e' : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hL hP, cls_lbPow hH, neg_zsmul, natCast_zsmul, sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨_, v, hv⟩

end GlobalTheory.ProjVar
