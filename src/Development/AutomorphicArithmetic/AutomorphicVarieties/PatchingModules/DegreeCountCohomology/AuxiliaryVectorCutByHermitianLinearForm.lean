module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FrobFormTrunc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Statement
public import Mathlib.Algebra.Algebra.ZMod
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem linearMap_comp_eq_on_smul_of_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (φ : ℤ_[l] →+* R)
    (h : ∀ y : R, l • y = 0) (τ : R →+ ZMod l) (a : ℤ_[l]) (y : R) :
    τ (φ a * y) = PadicInt.toZMod a * τ y := by
  have hspec := PadicInt.toZMod_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hspec
  obtain ⟨c, hc⟩ := hspec
  have ha : a = c * (l : ℤ_[l]) + ((PadicInt.toZMod a).val : ℤ_[l]) := by
    rw [hc, ZMod.cast_eq_val]
    ring
  have key : φ a * y = ((PadicInt.toZMod a).val : R) * y := by
    have e : φ a = φ c * (l : R) + ((PadicInt.toZMod a).val : R) := by
      rw [← map_natCast φ l, ← map_natCast φ, ← map_mul, ← map_add (f := _), ← ha]
    rw [e, add_mul, mul_assoc, ← nsmul_eq_mul l y, h y, mul_zero, zero_add]
  rw [key, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

private theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (m : ℕ) :
    ∃ τ : (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ m}) →+ ZMod l,
      ∀ y, (∀ z, τ (y * z) = 0) → y = 0 := by
  cases m with
  | zero =>
    refine ⟨0, fun y _ => ?_⟩
    have htop : Ideal.span {(PowerSeries.X : PowerSeries k) ^ 0} = ⊤ := by
      rw [pow_zero, Ideal.span_singleton_one]
    exact (Ideal.Quotient.subsingleton_iff.2 htop).elim _ _
  | succ k0 =>
    letI := ZMod.algebra k l
    obtain ⟨lam, -, hlam, -⟩ := UpperTheory.V.AlgebraTools.frob_form_trunc (k := k) l k0
    exact ⟨lam, hlam⟩

theorem UpperTheory.V.Pa.pair1 :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (m : ℕ), ∃ τ : x.Am m →+ ZMod l, (∀ y, (∀ z, τ (y * z) = 0) → y = 0) ∧ ∀ (a : ℤ_[l]) y, τ (algebraMap x.A (x.Am m) (algebraMap ℤ_[l] x.A a) * y) = PadicInt.toZMod a * τ y := by
  intro l _ F n x m
  obtain ⟨-, -, -, h4, -, -, -, -, hc⟩ := finAm l F n x m 0
  obtain ⟨τ, hτ⟩ := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero l x.K m
  exact ⟨τ, hτ, fun a y =>
    linearMap_comp_eq_on_smul_of_eq l (x.Am m) ((algebraMap x.A (x.Am m)).comp (algebraMap ℤ_[l] x.A)) h4 τ a y⟩
