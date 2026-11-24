module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayMono

theorem exists_apply_eq_of_normal {K A Ω : Type} [Field K] [Field A] [Field Ω] [Algebra K A] [Algebra K Ω]
    [Normal K A] (i j : A →ₐ[K] Ω) (x : A) : ∃ y, j y = i x := by
  let _ := j.toRingHom.toAlgebra
  have : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  exact ⟨i.restrictNormal A x, i.restrictNormal_commutes A x⟩

theorem le_of_isRayFieldIn_of_dvd : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (𝔪 𝔪' : Ideal (𝓞 E))
    (M M' : IntermediateField ℚ ℂ), 𝔪' ≠ ⊥ → 𝔪 ∣ 𝔪' → IsRayFieldIn φ 𝔪 M → IsRayFieldIn φ 𝔪' M' → M ≤ M' := by
  rintro E _ _ φ 𝔪 𝔪' M M' hn hd ⟨h, _, hM⟩ ⟨h', _, hM'⟩ z hz
  let _ := algOf φ M h
  let _ := algOf φ M' h'
  let _ := φ.toAlgebra
  have := hM.1
  have := hM'.1
  obtain ⟨f⟩ := nonempty_algHom_of_isRay_of_dvd hn hd hM'.2 hM.2
  let i : M →ₐ[E] ℂ := { M.val.toRingHom with commutes' := fun _ => rfl }
  let i' : M' →ₐ[E] ℂ := { M'.val.toRingHom with commutes' := fun _ => rfl }
  obtain ⟨y, hy⟩ := exists_apply_eq_of_normal i (i'.comp f) ⟨z, hz⟩
  have hy' : ((f y : M') : ℂ) = z := hy
  exact hy' ▸ (f y).2

end GlobalTheory.Mem.RayMono
