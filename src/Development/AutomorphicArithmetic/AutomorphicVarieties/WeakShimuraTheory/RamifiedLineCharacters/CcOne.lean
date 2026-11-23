module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCohDefs
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.ccEx :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ c : InfinitePlace F → G F Ω, ∀ w, w.IsReal → IsCCAt w (c w) := by
  intro F Ω _ _ _ _ _
  classical
  have key : ∀ w : InfinitePlace F, w.IsReal → ∃ c : G F Ω, IsCCAt w c := by
    intro w hw
    have hφ : ∀ a, (starRingEnd ℂ) (w.embedding a) = w.embedding a := by
      intro a
      have h := ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)
      exact RingHom.congr_fun h a
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let e : Ω ≃ₐ[F] algebraicClosure F ℂ := IsAlgClosure.equiv F Ω (algebraicClosure F ℂ)
    let κ : ℂ →ₐ[F] ℂ :=
      { (starRingEnd ℂ) with commutes' := fun a => hφ a }
    let j : Ω →ₐ[F] ℂ := (algebraicClosure F ℂ).val.comp e.toAlgHom
    have hmem : ∀ x : Ω, (κ.comp j) x ∈ (algebraicClosure F ℂ).toSubalgebra := by
      intro x
      show (κ.comp j) x ∈ algebraicClosure F ℂ
      rw [map_mem_algebraicClosure_iff, mem_algebraicClosure_iff]
      exact Algebra.IsAlgebraic.isAlgebraic x
    let f : Ω →ₐ[F] algebraicClosure F ℂ := (κ.comp j).codRestrict _ hmem
    let c0 : Ω →ₐ[F] Ω := e.symm.toAlgHom.comp f
    let c : G F Ω := AlgEquiv.ofBijective c0 (Algebra.IsAlgebraic.algHom_bijective c0)
    refine ⟨c, j.toRingHom, fun x => ?_, ?_⟩
    · show ((e (e.symm (f x)) : algebraicClosure F ℂ) : ℂ) = (starRingEnd ℂ) (j x)
      rw [AlgEquiv.apply_symm_apply]
      rfl
    · have hj : j.toRingHom.comp (algebraMap F Ω) = w.embedding := by
        ext a
        exact j.commutes a
      rw [hj, InfinitePlace.mk_embedding]
  refine ⟨fun w => if hw : w.IsReal then (key w hw).choose else 1, fun w hw => ?_⟩
  simp only [dif_pos hw]
  exact (key w hw).choose_spec
