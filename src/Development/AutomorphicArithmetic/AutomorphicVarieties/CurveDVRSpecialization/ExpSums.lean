module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.HalesJewett
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

theorem UpperTheory.V.Pr.expSums :
    UpperTheory.V.Pr.ExpSums := by
  intro κ ι σ _ _ _ α c hα hc
  classical
  by_contra hne
  push Not at hne
  choose C hC using hne
  obtain ⟨a, ha, b, s, hs⟩ :=
    Combinatorics.exists_mono_homothetic_copy (Finset.range (Fintype.card ι)) C
  let e := (Fintype.equivFin ι).symm
  have hinj : Function.Injective fun j : Fin (Fintype.card ι) => ((α s (e j) : κˣ) : κ) ^ a := by
    intro i j hij
    by_contra h
    refine hα s (e i) (e j) (fun h' => h (e.injective h')) a ha ?_
    apply Units.ext
    simpa using hij
  have h0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (v := fun j => c s (e j) * ((α s (e j) : κˣ) : κ) ^ b) hinj (by
      intro i
      have h1 := hC (a • (i : ℕ) + b)
      rw [hs i (Finset.mem_range.2 i.2), ← e.sum_comp] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, pow_add, pow_mul]
      ring)
  obtain ⟨i, hi⟩ := hc s
  have h2 := congrFun h0 (e.symm i)
  simp only [Equiv.apply_symm_apply, Pi.zero_apply, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact hi h2
  · exact pow_ne_zero _ (α s i).ne_zero h2
