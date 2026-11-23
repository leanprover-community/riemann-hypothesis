module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IsCoordA
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNsmulMemClosure
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys

@[expose] public section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

private lemma exists_nsmul_mem_closure {V : Type*} [AddCommGroup V] [Module ℚ V] (s : Set V) (w : V)
    (hw : w ∈ Submodule.span ℚ s) : ∃ k : ℕ, 0 < k ∧ k • w ∈ AddSubgroup.closure s :=
  _root_.UpperTheory.Reformulated.B.ExistsNsmulMemClosure.exists_nsmul_mem_closure s w hw

theorem UpperTheory.p_lattice_saturated_and_cofinite :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (M : AddSubgroup (VQ D)), UpperTheory.Gal.W2.IsPLat D M → (∀ (m : ℕ) (w : VQ D), m.Coprime p → m • w ∈ M → w ∈ M) ∧ ∀ w : VQ D, ∃ r : ℕ, p ^ r • w ∈ M := by
  intro p hp D M hM
  obtain ⟨-, s, hs, hmem⟩ := hM
  have hprime : p.Prime := hp.out
  refine ⟨?_, ?_⟩
  · intro m w hm hw
    obtain ⟨m', hm', hc⟩ := (hmem _).1 hw
    refine (hmem _).2 ⟨m' * m, Nat.Coprime.mul_left hm' hm, ?_⟩
    rwa [mul_smul]
  · intro w
    obtain ⟨k, hk, hkw⟩ := exists_nsmul_mem_closure (s : Set (VQ D)) w (by rw [hs]; trivial)
    obtain ⟨r, k', hk', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' p hprime.ne_one
    refine ⟨r, (hmem _).2 ⟨k', ((Nat.Prime.coprime_iff_not_dvd hprime).2 hk').symm, ?_⟩⟩
    rw [smul_smul, mul_comm]
    exact hkw
