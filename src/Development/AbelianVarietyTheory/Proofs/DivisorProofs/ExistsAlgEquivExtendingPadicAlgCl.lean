module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct
open scoped Classical

namespace GlobalTheory.LKTrip

theorem exists_algEquiv_extending_padicAlgCl {p : ℕ} [Fact p.Prime]
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (φ : E →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x : E, σ x = φ x := by
  refine ⟨AlgEquiv.ofBijective (φ.liftNormal (PadicAlgCl p))
    (Algebra.IsAlgebraic.algHom_bijective _), fun x => ?_⟩
  exact φ.liftNormal_commutes (PadicAlgCl p) x

theorem HTGroup.sum_finrank_Fw_eq_finrank_Kq {p : ℕ} [Fact p.Prime] (G : HTGroup p) :
    ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank G.Kq G.F := by
  letI : Algebra G.Kq (PadicAlgCl p) := ((algebraMap ℚ_[p] (PadicAlgCl p)).comp G.u).toAlgebra
  haveI : FiniteDimensional G.Kq G.F := Module.Finite.of_restrictScalars_finite ℚ G.Kq G.F
  let f : (Σ w : Fin G.m, (G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) → (G.F →ₐ[G.Kq] PadicAlgCl p) := fun a =>
    { (a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1) with
      commutes' := fun x => by
        have h : G.embW a.1 (x : G.F) = algebraMap ℚ_[p] (G.Fw a.1) (G.u x) :=
          Subtype.ext (G.emb_over a.1 x)
        change a.2 (G.embW a.1 (x : G.F)) = algebraMap ℚ_[p] (PadicAlgCl p) (G.u x)
        rw [h, AlgHom.commutes] }
  have hf : ∀ a x, f a x = a.2 (G.embW a.1 x) := fun _ _ => rfl
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨w, φ⟩ ⟨w', ψ⟩ h
      have h' : ∀ x, φ (G.embW w x) = ψ (G.embW w' x) := fun x => by
        rw [← hf ⟨w, φ⟩, h, hf]
      obtain ⟨σ, hσ⟩ := exists_algEquiv_extending_padicAlgCl _ φ
      obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_padicAlgCl _ ψ
      obtain rfl : w = w' := by
        refine G.emb_inj w w' (σ.trans τ.symm) (RingHom.ext fun x => ?_)
        change τ.symm (σ (G.emb w x)) = G.emb w' x
        rw [AlgEquiv.symm_apply_eq]
        exact (hσ (G.embW w x)).trans ((h' x).trans (hτ (G.embW w' x)).symm)
      obtain rfl : φ = ψ := by
        refine IntermediateField.adjoin_algHom_ext ℚ_[p] ?_
        rintro _ ⟨x, rfl⟩
        exact h' x
      rfl
    · intro τ
      obtain ⟨w, σ, h⟩ := G.emb_all (τ : G.F →+* PadicAlgCl p) (fun x => τ.commutes x)
      refine ⟨⟨w, (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
      exact (DFunLike.congr_fun h x).symm
  have hc := Fintype.card_of_bijective hbij
  rw [Fintype.card_sigma, AlgHom.card] at hc
  simpa only [AlgHom.card] using hc

theorem HTGroup.two_mul_sum_finrank_Fw (p : ℕ) [Fact p.Prime] (G : HTGroup p) :
    2 * ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank ℚ G.F := by
  rw [G.sum_finrank_Fw_eq_finrank_Kq, ← G.hKq.1]
  exact Module.finrank_mul_finrank ℚ G.Kq G.F

end GlobalTheory.LKTrip
