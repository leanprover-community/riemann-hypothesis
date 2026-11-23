module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecNonzeroOnFiniteOfGenerated
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistMove

theorem exists_generating_secs_tens_lbPow {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F)
    (H : LB X) (N : ℕ) (s : Fin (N + 1) → H.Sec) (hH : H.IsLB) (hs : AbLaw.VeryAmpleBy p H s)
    (M : LB X) (hM : M.IsLB) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (n : ℕ) (u : Fin n → (CechPic.tens M (lbPow H m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated F X p H N s hH hs M hM
  refine ⟨t₀.toNat, fun m hm => ?_⟩
  obtain ⟨n, u, hu⟩ := ht m (by omega)
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens M (lbPow H m)).IsLB := isLB_tens hM hP
  have e : cls (AbLaw.tw M H m) (AbLaw.isLB_tw hM hH _) =
      cls M hM - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hM (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hM hH _)
  have e' : cls (AbLaw.tw M H m) (AbLaw.isLB_tw hM hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hM hP, cls_lbPow hH, neg_zsmul, natCast_zsmul,
      sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨_, v, hv⟩

theorem exists_twist_generated_sec_nonzero : ∀ (F : Type) [Field F] [Infinite F] (X : Scheme.{0}) (p : X ⟶ Sp F), IsProjOver p → ∀ (B : LB X), B.IsLB → ∀ S : Set X, S.Finite → ∃ (A : LB X) (_ : A.IsLB) (a : A.Sec), (∃ (n : ℕ) (u : Fin n → A.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ (∃ (n : ℕ) (u : Fin n → (CechPic.tens B A).Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ ∀ z ∈ S, z ∈ nonzeroLocus a := by
  intro F _ _ X p hp B hB S hS
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨N, ι, hι, e⟩ := hp
  haveI := hι
  have hs := ProjSpace.veryAmpleBy_secPull_coord ι
  rw [e] at hs
  have hH : ((ProjSpace.O1 F N).pull ι).IsLB := pull_isLB (ProjSpace.O1_isLB F N) _
  obtain ⟨H, hH, s, hs⟩ : ∃ H : LB X, H.IsLB ∧ ∃ s : Fin (N + 1) → H.Sec, AbLaw.VeryAmpleBy p H s :=
    ⟨_, hH, _, hs⟩
  obtain ⟨m₁, h₁⟩ := exists_generating_secs_tens_lbPow p H N s hH hs B hB
  obtain ⟨m₂, h₂⟩ := exists_generating_secs_tens_lbPow p H N s hH hs (LB.triv X) (LB.isLB_triv X)
  obtain ⟨n₁, u₁, hu₁⟩ := h₁ (max m₁ m₂) (le_max_left _ _)
  obtain ⟨n₂, u₂, hu₂⟩ := h₂ (max m₁ m₂) (le_max_right _ _)
  have hP : (lbPow H (max m₁ m₂)).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens (LB.triv X) (lbPow H (max m₁ m₂))).IsLB := isLB_tens (LB.isLB_triv X) hP
  have e₂ : cls _ hT = cls _ hP := by rw [cls_tens (LB.isLB_triv X) hP, cls_triv, zero_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hP e₂ _ u₂ hu₂
  obtain ⟨a, ha⟩ := exists_sec_nonzero_on_finite_of_generated F X p _ hP _ v hv S hS
  exact ⟨_, hP, a, ⟨_, v, hv⟩, ⟨_, u₁, hu₁⟩, ha⟩

end GlobalTheory.TwistMove
