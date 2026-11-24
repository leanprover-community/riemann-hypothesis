module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.FinPart

open scoped MonoidAlgebra

theorem exists_algHom_end_of_span_intertwiners :
    ∀ (H W V : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H W) (ρ : Representation ℂ H V),
      σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ →
      ∃ Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V, (∀ h, Φ (σ h) = ρ h) ∧
        ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ h)) → ∀ A, Commute T (Φ A) := by
  intro H W V _ _ _ _ _ _ σ ρ hirr hspan
  classical

  have hsurj : Function.Surjective σ.asAlgebraHom := by
    have hB := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hirr
    have hle : Submodule.span ℂ (Set.range σ) ≤ Subalgebra.toSubmodule σ.asAlgebraHom.range := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      exact ⟨MonoidAlgebra.single h 1, by simp [Representation.asAlgebraHom_single]⟩
    intro A
    have : A ∈ Subalgebra.toSubmodule σ.asAlgebraHom.range := hle (hB ▸ Submodule.mem_top)
    exact this

  have hint : ∀ (f : σ.IntertwiningMap ρ) (a : MonoidAlgebra ℂ H) (w : W),
      ρ.asAlgebraHom a (f.toLinearMap w) = f.toLinearMap (σ.asAlgebraHom a w) := by
    intro f a w
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hx, hy, map_add (f := _)]
    | single g c =>
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
      congr 1
      exact (Representation.IntertwiningMap.isIntertwining σ ρ f g w).symm
  have hker : RingHom.ker σ.asAlgebraHom ≤ RingHom.ker ρ.asAlgebraHom := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have hle : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) ≤
        LinearMap.ker (ρ.asAlgebraHom a) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker, hint, ha]
      simp
    rw [hspan, top_le_iff] at hle
    exact LinearMap.ker_eq_top.1 hle
  let Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V :=
    (Ideal.Quotient.liftₐ (RingHom.ker σ.asAlgebraHom) ρ.asAlgebraHom hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
  have hΦ : ∀ a, Φ (σ.asAlgebraHom a) = ρ.asAlgebraHom a := by
    intro a
    have : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a) =
        Ideal.Quotient.mk _ a := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    change Ideal.Quotient.liftₐ _ _ hker ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a)) = _
    rw [this]
    rfl
  refine ⟨Φ, fun h => ?_, fun T hT A => ?_⟩
  · have := hΦ (MonoidAlgebra.single h 1)
    simpa [Representation.asAlgebraHom_single] using this
  · obtain ⟨a, rfl⟩ := hsurj A
    rw [hΦ]
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _)]; exact hx.add_right hy
    | single g c =>
      rw [Representation.asAlgebraHom_single]
      exact (hT g).smul_right c

end GlobalTheory.FinPart
