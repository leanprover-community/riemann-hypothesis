module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
open Polynomial

namespace GlobalTheory.AV.AbVar

theorem int_of_charpoly_rat_of_monic_annihilator : ∀ (k V : Type) [Field k] [Algebra ℚ k] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (P : Polynomial ℚ) (Q : Polynomial ℤ), Q.Monic → Polynomial.aeval φ Q = 0 → P.map (algebraMap ℚ k) = φ.charpoly → ∃ P₀ : Polynomial ℤ, P₀.map (algebraMap ℤ ℚ) = P := by
  intro k V _ _ _ _ _ φ P Q hQ hφ hP
  have hinj : Function.Injective (algebraMap ℚ k) := (algebraMap ℚ k).injective
  have hPm : P.Monic := Polynomial.monic_of_injective hinj (by rw [hP]; exact LinearMap.charpoly_monic φ)
  set Qq : ℚ[X] := Q.map (algebraMap ℤ ℚ) with hQq
  have hmap : Qq.map (algebraMap ℚ k) = Q.map (algebraMap ℤ k) := by
    rw [hQq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hG : aeval φ (Q.map (algebraMap ℤ k)) = 0 := by
    rw [aeval_map_algebraMap]; exact hφ
  have hd := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank φ _ hG
  rw [← hP, ← hmap, ← Polynomial.map_pow, Polynomial.map_dvd_map' (algebraMap ℚ k)] at hd
  have hd' : P ∣ (Q ^ Module.finrank k V).map (algebraMap ℤ ℚ) := by
    rw [Polynomial.map_pow]; exact hd
  obtain ⟨P₀, hP₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ (hQ.pow _) hd'
  refine ⟨P₀, ?_⟩
  rw [hPm.leadingCoeff, Polynomial.C_1, _root_.mul_one] at hP₀
  exact hP₀

end GlobalTheory.AV.AbVar
