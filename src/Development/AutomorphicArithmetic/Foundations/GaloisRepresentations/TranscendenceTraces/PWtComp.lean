module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtComp_of :
    SumComp → FibFin → WtComp := by
  intro hsum hfin W Z S r p _ _ w' w hr hp A φ hφ
  obtain ⟨m, hm1, hm2⟩ : ∃ m : A.V ⟶ pullback p A.u,
      m ≫ pullback.fst p A.u = A.v ≫ r ∧ m ≫ pullback.snd p A.u = A.r :=
    ⟨pullback.lift (A.v ≫ r) A.r (by rw [Category.assoc]; exact A.pb.w),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsq : IsPullback A.v m r (pullback.fst p A.u) := by
    refine IsPullback.of_bot ?_ hm1.symm (IsPullback.of_hasPullback p A.u)
    rw [hm2]
    exact A.pb
  let C : Sq r := ⟨pullback p A.u, A.V, pullback.fst p A.u, A.v, m, hsq⟩
  haveI : IsFinite m := C.finite
  haveI : IsFinite (pullback.snd p A.u) := (Sq.of p A.u).finite
  obtain ⟨ψ1, hψ1, hψ1s⟩ := hr C φ hφ
  obtain ⟨ψ2, hψ2, hψ2s⟩ := hp (Sq.of p A.u) ψ1 hψ1
  refine ⟨ψ2, hψ2, ?_⟩
  intro Ω _ _ x
  have hsc : ∀ c : (gp Ω ⟶ A.V) → ℤ, ∑ᶠ z ∈ fib (m ≫ pullback.snd p A.u) x, c z =
      ∑ᶠ y ∈ fib (pullback.snd p A.u) x, ∑ᶠ z ∈ fib m y, c z := by
    intro c
    have h := congrArg (AddEquiv.ulift : ULift.{1} ℤ ≃+ ℤ)
      (hsum m (pullback.snd p A.u) Ω x (ULift.{1} ℤ) (fun z => ULift.up (c z)))
    simp only [AddEquiv.map_finsum] at h
    exact h
  refine (hψ2s Ω x).trans ?_
  rw [← hm2, hsc]
  refine finsum_mem_congr rfl ?_
  intro y _
  refine (congrArg (fun t => w Ω (y ≫ pullback.fst p A.u) * t) (hψ1s Ω y)).trans ?_
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl ?_
  intro z hz
  have hz' : z ≫ m = y := hz
  show w Ω (y ≫ pullback.fst p A.u) * (w' Ω (z ≫ A.v) * φ (pt z)) =
    w' Ω (z ≫ A.v) * w Ω ((z ≫ A.v) ≫ r) * φ (pt z)
  rw [Category.assoc, ← hm1, ← Category.assoc, hz']
  exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm
