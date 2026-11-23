module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.SplittingField.Construction

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.Det.resSq_fin {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [Module.Finite K K'] : (PowerSeries.map (algebraMap K K')).Finite := by
  classical
  letI := (PowerSeries.map (algebraMap K K')).toAlgebra
  let b := Module.finBasis K K'
  show Module.Finite (PowerSeries K) (PowerSeries K')
  refine ⟨⟨Finset.univ.image (fun i => PowerSeries.C (b i)), ?_⟩⟩
  rw [eq_top_iff]
  intro φ _
  have key : φ = ∑ i, (PowerSeries.mk fun n => b.repr (PowerSeries.coeff n φ) i) •
      PowerSeries.C (b i) := by
    ext n

    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sum, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_map, PowerSeries.coeff_mk]
    simp_rw [← Algebra.smul_def]
    exact (b.sum_repr _).symm
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

private theorem UpperTheory.V.Pa.Det.resSq_field (K : Type) [Field K] [Finite K] :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K'),
      ∀ a : K, IsSquare (algebraMap K K' a) := by
  classical
  letI := Fintype.ofFinite K
  let p : Polynomial K := ∏ a : K, (Polynomial.X ^ 2 - Polynomial.C a)
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ =>
    Polynomial.X_pow_sub_C_ne_zero (by norm_num) a
  refine ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, fun a => ?_⟩
  have hs := Polynomial.SplittingField.splits p
  have hd : (Polynomial.X ^ 2 - Polynomial.C a) ∣ p := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
  have hs' : ((Polynomial.X ^ 2 - Polynomial.C a).map (algebraMap K p.SplittingField)).Splits :=
    hs.of_dvd (Polynomial.map_ne_zero hp) (Polynomial.map_dvd _ hd)
  obtain ⟨x, hx⟩ := hs'.exists_eval_eq_zero (by
    rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
  refine ⟨x, ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx
  rw [← sq]; exact (sub_eq_zero.mp hx).symm

theorem UpperTheory.V.Pa.Det.resSq :
    ∀ {K : Type} [Field K] [Finite K], ∃ (K' : Type) (_ : Field K') (_ : Finite K') (j : PowerSeries K →+* PowerSeries K'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ ∀ c : (PowerSeries K)ˣ, IsSquare (residue (PowerSeries K') (j c)) := by
  intro K _ _
  obtain ⟨K', _, _, _, hsq⟩ := UpperTheory.V.Pa.Det.resSq_field K
  haveI : Finite K' := Module.finite_of_finite K
  have hcc : ∀ φ : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.map (algebraMap K K') φ) =
      algebraMap K K' (PowerSeries.constantCoeff φ) := by
    intro φ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  refine ⟨K', inferInstance, inferInstance, PowerSeries.map (algebraMap K K'),
    PowerSeries.map_injective _ (algebraMap K K').injective, ⟨fun φ hφ => ?_⟩,
    UpperTheory.V.Pa.Det.resSq_fin, fun c => ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, hcc, isUnit_iff_ne_zero,
      map_ne_zero_iff _ (algebraMap K K').injective] at hφ
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact hφ
  · obtain ⟨r, hr⟩ := hsq (PowerSeries.constantCoeff (c : PowerSeries K))
    refine ⟨residue (PowerSeries K') (PowerSeries.C r), ?_⟩
    rw [← map_mul, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
      mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub, hcc, hr, map_mul,
      PowerSeries.constantCoeff_C, sub_self]
    exact not_isUnit_zero
