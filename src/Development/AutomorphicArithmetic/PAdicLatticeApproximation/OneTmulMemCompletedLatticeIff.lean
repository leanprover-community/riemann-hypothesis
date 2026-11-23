module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAwayStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

private theorem val_p_eq_one {p : ℕ} [Fact p.Prime] (v : AwayP p) :
    v.1.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  intro hp
  apply v.2
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
  exact (hmax.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hp)).symm

private theorem isIntAf_of_pow_mul {p : ℕ} [Fact p.Prime] (q : ℚ) (r : ℕ) (c : ℤ)
    (h : ((p ^ r : ℕ) : ℚ) * q = c) : IsIntAf (algebraMap ℚ (AfP p) q) := by
  intro v
  rw [AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have hc : v.1.valuation ℚ (c : ℚ) ≤ 1 := by
    simpa using v.1.valuation_le_one (K := ℚ) c
  have hp : v.1.valuation ℚ ((p ^ r : ℕ) : ℚ) = 1 := by
    have h1 := val_p_eq_one v
    rw [eq_intCast] at h1
    push_cast at h1 ⊢
    rw [map_pow, h1, one_pow]
  have hq : v.1.valuation ℚ q ≤ 1 := by
    have h2 := congrArg (v.1.valuation ℚ) h
    rw [map_mul, hp, _root_.one_mul] at h2
    rw [h2]
    exact hc
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
  exact hq

theorem UpperTheory.one_tmul_mem_completedLattice_iff :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} (z : VQ D), (1 : AfP p) ⊗ₜ[ℚ] z ∈ LaHat D ↔ ∃ (r : ℕ) (x : D.La), p ^ r • z = (1 : ℚ) ⊗ₜ[ℤ] x := by
  intro p _ D z
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let bQ := Algebra.TensorProduct.basis ℚ b
  have key : ∀ i, (KNLevel.bA b).repr ((1 : AfP p) ⊗ₜ[ℚ] z) i = algebraMap ℚ (AfP p) (bQ.repr z i) := by
    intro i
    simp [KNLevel.bA, Algebra.TensorProduct.basis_repr_tmul, bQ]
  have hsm : ∀ (r : ℕ) i, bQ.repr (p ^ r • z) i = ((p ^ r : ℕ) : ℚ) * bQ.repr z i := by
    intro r i
    rw [← Nat.cast_smul_eq_nsmul ℚ, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
  have htm : ∀ (x : D.La) i, bQ.repr ((1 : ℚ) ⊗ₜ[ℤ] x) i = (b.repr x i : ℚ) := by
    intro x i
    simp [bQ, Algebra.TensorProduct.basis_repr_tmul]
  rw [KNLevel.mem_laHat_iff b]
  simp only [key]
  constructor
  · intro h
    choose k a hka using fun i => T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway p (bQ.repr z i) (h i)
    let r := ∑ i, k i
    let c : _ → ℤ := fun i => (p : ℤ) ^ (r - k i) * a i
    have hc : ∀ i, ((p ^ r : ℕ) : ℚ) * bQ.repr z i = (c i : ℚ) := by
      intro i
      have hk : k i ≤ r := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hpow : (p : ℚ) ^ r = (p : ℚ) ^ (r - k i) * (p : ℚ) ^ (k i) := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      have ha := hka i
      push_cast at ha ⊢
      rw [hpow, _root_.mul_assoc, ha]
      simp [c]
    refine ⟨r, b.equivFun.symm c, ?_⟩
    apply bQ.ext_elem
    intro i
    have hb : b.repr (b.equivFun.symm c) i = c i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hsm, htm, hb]
    exact hc i
  · rintro ⟨r, x, hx⟩ i
    apply isIntAf_of_pow_mul _ r (b.repr x i)
    rw [← hsm, hx, htm]
