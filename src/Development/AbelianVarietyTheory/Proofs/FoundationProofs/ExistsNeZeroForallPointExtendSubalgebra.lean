module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
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
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem exists_ne_zero_forall_point_extend_subalgebra :
    ∀ (k A R : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [CommRing R] [IsDomain R] [Algebra k R] (ξ : A →ₐ[k] R),
    Function.Injective ξ → ∀ T : Finset R,
    ∃ (a : A) (S : Subalgebra k R) (hξ : ∀ u, ξ u ∈ S), a ≠ 0 ∧ (∀ t ∈ T, t ∈ S) ∧
      ∀ φ : A →ₐ[k] k, φ a ≠ 0 → ∃ ψ : S →ₐ[k] k, ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := by
  intro k A R _ _ _ _ _ _ _ _ _ ξ hinj T
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  set S : Subalgebra k R := Algebra.adjoin k (ξ '' (s : Set A) ∪ (T : Set R)) with hSdef
  have hξ : ∀ u, ξ u ∈ S := by
    intro u
    have hu : u ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have : ξ u ∈ (Algebra.adjoin k (s : Set A)).map ξ := ⟨u, hu, rfl⟩
    rw [AlgHom.map_adjoin] at this
    exact Algebra.adjoin_mono Set.subset_union_left this
  have hT : ∀ t ∈ T, t ∈ S := fun t ht => Algebra.subset_adjoin (Set.subset_union_right ht)
  have hSfg : S.FG := Subalgebra.fg_def.2
    ⟨_, (s.finite_toSet.image ξ).union T.finite_toSet, rfl⟩
  haveI : Algebra.FiniteType k S := (Subalgebra.fg_iff_finiteType S).1 hSfg
  let f : A →ₐ[k] S := ξ.codRestrict S hξ
  letI : Algebra A S := f.toRingHom.toAlgebra
  haveI : IsScalarTower k A S := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  haveI : Algebra.FiniteType A S := Algebra.FiniteType.of_restrictScalars_finiteType k A S
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hfinj : Function.Injective (algebraMap A S) := by
    intro x y h
    apply hinj
    have := congrArg Subtype.val h
    exact this
  have hfp : Algebra.FinitePresentation A S := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  have hc := PrimeSpectrum.isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr hfp)
  obtain ⟨q, hq, H⟩ := exists_basicOpen_subset_of_isConstructible_of_bot_mem hc
    ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hfinj)⟩
  refine ⟨q, S, hξ, hq, hT, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom_extend_of_ker_mem_range_comap (A := S) φ.toRingHom
    (H ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime _⟩ (by simpa [RingHom.mem_ker] using hφ))
  have hψu : ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := fun u => by
    have := RingHom.congr_fun hψ u
    exact this
  refine ⟨{ ψ with commutes' := fun c => ?_ }, hψu⟩
  have h1 : (algebraMap k S c) = ⟨ξ (algebraMap k A c), hξ _⟩ := by
    ext; simp
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe]
  rw [h1, hψu, φ.commutes]

end GlobalTheory
