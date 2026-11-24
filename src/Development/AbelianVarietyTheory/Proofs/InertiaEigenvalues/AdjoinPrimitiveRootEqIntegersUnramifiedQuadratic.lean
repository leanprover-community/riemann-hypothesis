module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

noncomputable section
namespace GlobalTheory.UnitLemma.Unr
open Polynomial

theorem mem_adjoin_of_pow_eq_one_of_isUnit {R F L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {z : L} {N : ℕ} (hN : IsUnit (N : R)) (hz : z ^ N = 1) (hadj : Algebra.adjoin F {z} = ⊤)
    {y : L} (hy : IsIntegral R y) : y ∈ Algebra.adjoin R {z} := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hzR : IsIntegral R z := by
    refine ⟨X ^ N - C 1, monic_X_pow_sub_C 1 hN0, ?_⟩
    simp [eval₂_sub, hz]
  have hzF : IsIntegral F z := hzR.tower_top
  let pb := PowerBasis.ofAdjoinEqTop hzF hadj
  have hgen : pb.gen = z := PowerBasis.ofAdjoinEqTop_gen hzF hadj
  have hmem := Algebra.discr_mul_isIntegral_mem_adjoin F (R := R) (B := pb) (hint := by rw [hgen]; exact hzR) (hz := hy)
  rw [hgen] at hmem
  haveI : Module.IsTorsionFree R L := .of_smul_eq_zero fun r x hx => by
    rw [Algebra.smul_def, mul_eq_zero, IsScalarTower.algebraMap_apply R F L,
      map_eq_zero_iff _ (algebraMap F L).injective, IsFractionRing.to_map_eq_zero_iff] at hx
    exact hx
  have hIntAe : ∀ p : R[X], IsIntegral R (aeval z p) := fun p =>
    adjoin_le_integralClosure hzR (aeval_mem_adjoin_singleton R z)
  set m := minpoly R z with hm
  obtain ⟨h, hmh⟩ : m ∣ X ^ N - C 1 :=
    minpoly.isIntegrallyClosed_dvd hzR (by simp [hz])
  have hder : (N : L) * z ^ (N - 1) = aeval z (derivative m) * aeval z h := by
    have := congrArg (fun p => aeval z (derivative p)) hmh
    simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_add (f := _), map_mul] at this
    have h0 : aeval z m = 0 := minpoly.aeval R z
    simpa [h0] using this
  have hint : ∀ x : L, IsIntegral R x → ∃ r : R, algebraMap R F r = Algebra.norm F x := fun x hx =>
    IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm F hx)
  obtain ⟨ra, hra⟩ := hint _ (hIntAe (derivative m))
  obtain ⟨rb, hrb⟩ := hint _ (hIntAe h)
  obtain ⟨rz, hrz⟩ := hint _ hzR
  have hinj := IsFractionRing.injective R F
  have hrzN : rz ^ N = 1 := hinj (by rw [map_pow, hrz, ← map_pow, hz, map_one, map_one])
  have hprod : ra * rb = (N : R) ^ Module.finrank F L * rz ^ (N - 1) := by
    apply hinj
    have hNL : ((N : L)) = algebraMap F L (N : F) := (map_natCast _ _).symm
    rw [map_mul, hra, hrb, ← map_mul, ← hder, map_mul, map_pow (Algebra.norm F), hNL,
      Algebra.norm_algebraMap, map_mul, map_pow, map_pow, hrz, map_natCast]
  have hra_unit : IsUnit ra := by
    have : IsUnit (ra * rb) := by
      rw [hprod]
      have hrzu : IsUnit rz := isUnit_iff_exists_inv.2 ⟨rz ^ (N - 1), by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN0), hrzN]⟩
      exact (hN.pow _).mul (hrzu.pow _)
    exact isUnit_of_mul_isUnit_left this
  have hdisc : Algebra.discr F pb.basis = algebraMap R F ((-1) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra) := by
    rw [Algebra.discr_powerBasis_eq_norm, map_mul, hra, map_pow, map_neg, map_one, hgen,
      minpoly.isIntegrallyClosed_eq_field_fractions' F hzR, derivative_map, aeval_map_algebraMap]
  obtain ⟨v, hv⟩ : IsUnit ((-1 : R) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra) :=
    ((isUnit_one.neg).pow _).mul hra_unit
  rw [hdisc, ← hv, algebraMap_smul] at hmem
  have : y = (↑v⁻¹ : R) • ((v : R) • y) := by rw [smul_smul, Units.inv_mul, one_smul]
  rw [this]
  exact Subalgebra.smul_mem _ hmem _

end GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing

theorem GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) → @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ → ∀ y : K'.E, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra y → y ∈ @Algebra.adjoin K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra {z} := by
  intro K K' d φ hφ hd z hz hadj y hy
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hφ.2.2.2.2]; exact Nat.pos_of_ne_zero hd)
  have hN : IsUnit (((K'.q ^ 2 - 1 : ℕ)) : K.O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    haveI := Fintype.ofFinite (ResidueField K.O)
    have hcard : ((K.q ^ 2 : ℕ) : ResidueField K.O) = 0 := by
      rw [← K.card_res, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
    have hq : 1 ≤ K'.q ^ 2 := by
      rw [hφ.1, ← pow_mul, mul_comm, pow_mul]
      apply Nat.one_le_pow
      rw [← K.card_res]; exact Nat.card_pos
    rw [Nat.cast_sub hq, hφ.1, ← pow_mul, mul_comm, pow_mul, Nat.cast_pow, hcard, zero_pow hd, Nat.cast_one,
      zero_sub]
    exact neg_ne_zero.2 one_ne_zero
  exact mem_adjoin_of_pow_eq_one_of_isUnit hN hz.pow_eq_one hadj hy
