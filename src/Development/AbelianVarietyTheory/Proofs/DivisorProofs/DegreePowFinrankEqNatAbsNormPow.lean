module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAevalEqProdAroots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyAndPrimeDvdDegOfDvdNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.DegNorm

open Polynomial IntermediateField

theorem deg_pow_finrank_eq_natAbs_norm_pow : ∀ (K : Type) [Field K] (B : AbVar K) (F : Type) [Field F] [NumberField F] (ψ : 𝓞 F →+* End B) (c : 𝓞 F), c ≠ 0 → deg (ψ c).asHom ^ Module.finrank ℚ F = (Algebra.norm ℤ c).natAbs ^ (2 * B.dim) := by
  intro K _ B F _ _ ψ c hc
  have hN : Algebra.norm ℤ c ≠ 0 := by
    intro h
    have h1 := Algebra.coe_norm_int c
    rw [h, Int.cast_zero, eq_comm, Algebra.norm_eq_zero_iff] at h1
    exact hc (by exact_mod_cast h1)
  by_cases hB : B.dim = 0
  · obtain ⟨y, hy⟩ := dvd_algebraMap_norm c
    have hcomp : (ψ y).asHom ≫ (ψ c).asHom = Algebra.norm ℤ c • 𝟙 B := by
      rw [← End.mul_asHom]
      rw [← map_mul, ← hy, algebraMap_int_eq, Int.coe_castRingHom, map_intCast, ← zsmul_one]
      rfl
    have h := isIsogeny_comp_iff_and_deg_comp K B B B (ψ y).asHom (ψ c).asHom rfl rfl
    obtain ⟨-, hd⟩ := GlobalTheory.MulIsogeny.mul_isogeny K B _ hN
    rw [hcomp] at h
    rw [h.2, hB, mul_zero, pow_zero] at hd
    have h1 : deg (ψ c).asHom = 1 := Nat.eq_one_of_mul_eq_one_left hd
    rw [h1, hB, mul_zero, pow_zero, one_pow]
  · classical
    obtain ⟨k, hk, hPQ⟩ := charpoly_eq_minpoly_pow B hB ψ c
    obtain ⟨⟨-, hd, -⟩, -⟩ := isCharpoly_charpoly_unique K B (ψ c)
    have hxint : IsIntegral ℚ (c : F) := Algebra.IsIntegral.isIntegral _
    have hdeg : k * Module.finrank ℚ ℚ⟮(c : F)⟯ = 2 * B.dim := by
      have e := congrArg Polynomial.natDegree hPQ
      rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _), hd,
        Polynomial.natDegree_pow, ← IntermediateField.adjoin.finrank hxint] at e
      omega
    have hD := deg_aeval_eq_prod_aroots K B (ψ c) (AlgebraicClosure ℚ) Polynomial.X
    simp only [aeval_X, Multiset.map_id'] at hD
    rw [hPQ, Polynomial.aroots_pow, Multiset.prod_nsmul] at hD
    have hNr := Algebra.norm_eq_prod_roots (K := ℚ) (L := F) (AlgebraicClosure ℚ) (x := (c : F))
      (IsAlgClosed.splits _)
    have e : algebraMap ℚ (AlgebraicClosure ℚ) ((deg (ψ c).asHom : ℚ) ^ Module.finrank ℚ⟮(c : F)⟯ F) =
        algebraMap ℚ (AlgebraicClosure ℚ) (Algebra.norm ℚ (c : F) ^ k) := by
      rw [map_pow, map_pow, hD, hNr, ← pow_mul, ← pow_mul, mul_comm]
    have e2 := (algebraMap ℚ (AlgebraicClosure ℚ)).injective e
    rw [← Algebra.coe_norm_int] at e2
    have e3 : (deg (ψ c).asHom : ℤ) ^ Module.finrank ℚ⟮(c : F)⟯ F = Algebra.norm ℤ c ^ k := by
      exact_mod_cast e2
    have e4 := congrArg (fun t : ℤ => t ^ Module.finrank ℚ ℚ⟮(c : F)⟯) e3
    simp only [← pow_mul] at e4
    rw [hdeg, mul_comm, Module.finrank_mul_finrank] at e4
    have e5 := congrArg Int.natAbs e4
    simpa [Int.natAbs_pow] using e5

end GlobalTheory.AV.AbVar.DegNorm
