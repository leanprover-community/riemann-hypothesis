module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapUnit

theorem rho_one_eval : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ h : Module.Dual K (C.V 0) →+ B, C.Rho P.oneS h → ∀ φ : Module.Dual K (C.V 0), h φ = C.o (φ P.oneV) := by
  intro Λ A B K _ _ _ _ C hC P hP h hR φ
  obtain ⟨hsem, e, z, hz, hb⟩ := hR
  have hw : C.b 0 z = ((C.ℓ : B) ^ e) • C.μ 0 P.oneV := by
    have h0 : C.b 0 (z - ((C.ℓ : A) ^ e) • P.oneZ) = 0 := hC.sep 0 _ (fun n => by
      rw [map_sub, map_smul, hP.one_r, hz, sub_self])
    rw [map_sub, map_smulₛₗ, hP.one_b, sub_eq_zero] at h0
    rw [h0]
    simp
  haveI := hC.fin 0
  let bs := Module.finBasis K (C.V 0)
  have h1 := hb bs
  rw [hw] at h1
  have h2 : ∑ s, h (bs.coord s) • C.μ 0 (bs s) = C.μ 0 P.oneV := by
    obtain ⟨u, hu⟩ := hC.unit.pow e
    rw [← hu] at h1
    have h1' := congrArg (fun w => ((u⁻¹ : Bˣ) : B) • w) h1
    simpa only [smul_smul, Units.inv_mul, one_smul] using h1'
  have h3 : C.μ 0 P.oneV = ∑ s, C.o (bs.coord s P.oneV) • C.μ 0 (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]

    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smulₛₗ]
    rfl
  have h4 : (fun s => h (bs.coord s)) = fun s => C.o (bs.coord s P.oneV) :=
    (hC.basis 0 bs (C.μ 0 P.oneV)).unique h2.symm h3
  have h5 : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [Finset.sum_apply, Module.Basis.coord_apply, Finsupp.single_apply]
  have h6 : φ P.oneV = ∑ s, bs.coord s P.oneV * φ (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]

    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl

  rw [h6, map_sum]
  conv_lhs => rw [h5]

  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hsem, map_mul, mul_comm]
  exact congrArg (· * C.o (φ (bs s))) (congrFun h4 s)

end GlobalTheory.CompanionTheory.KapUnit
