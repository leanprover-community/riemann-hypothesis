module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_subsingleton_coh_twist_tens_lbPow : ∀ (k : Type) [Field k] {Y : Scheme.{0}} (f : Y ⟶ Sp k), IsProjOver f → ∀ (A N : LB Y), IsAmpleLB A → N.IsLB → ∀ (G : Y.Modules) [IsFiniteQC G] (B : ℕ), ∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < B → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
  intro k _ Y f hf A N hA hN G _ B
  letI := algebraΓOfHom f
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  have H (m : Fin B) : ∃ q : ℕ, ∀ n ≥ q, ∀ p, 0 < p →
      Subsingleton (coh (twist (twist G (lbPow N m)) (lbPow A n)) p) :=
    have := isFiniteQC_twist (F := G) (isLB_lbPow hN m)
    eventually_atTop.1 (hA.eventually_subsingleton_coh_twist (f := f) (fun _ => rfl) _)
  choose q hq using H
  obtain ⟨Q, hQ⟩ := Finite.exists_le q
  refine ⟨Q, fun j m hj hm p hp => ?_⟩
  have := hq ⟨m, hm⟩ j ((hQ _).trans hj) p hp
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq G (isLB_lbPow hN m)
    (isLB_lbPow hA.isLB j) (isLB_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)) (by
      rw [cls_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m),
        ← cls_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m) (isLB_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)),
        ← cls_tens (isLB_lbPow hN m) (isLB_lbPow hA.isLB j) (isLB_tens (isLB_lbPow hN m) (isLB_lbPow hA.isLB j))]
      exact (cls_eq_iff _ _).2 (tens_comm_iso (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)))
  exact (cohOn.mapIso k ⊤ p e).symm.injective.subsingleton

end GlobalTheory
