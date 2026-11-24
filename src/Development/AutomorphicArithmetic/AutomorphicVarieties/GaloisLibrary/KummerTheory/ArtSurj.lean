module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.artSurj :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Function.Surjective (artCl K Ω) ∧ IsLocallyConstant (artCl K Ω) := by
  intro K Ω _ _ _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  set L := GroundTheory.Global.hilbertClassField K Ω
  have hL : IsOpen ((AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker : Set (G K Ω)) := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_isOpen L
  have hker : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker ≤ (artCl K Ω).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom L x) = 1
    rw [hx, map_one]
  have hopen : IsOpen ((artCl K Ω).ker : Set (G K Ω)) := Subgroup.isOpen_mono hker hL
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω
      (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω y)
    refine ⟨σ, ?_⟩
    show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom L σ) = y
    rw [hσ, MulEquiv.symm_apply_apply]
  · rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    by_cases hy : ∃ g, artCl K Ω g = y
    · obtain ⟨g, rfl⟩ := hy
      have : (artCl K Ω) ⁻¹' {artCl K Ω g} = (fun x => g⁻¹ * x) ⁻¹' ((artCl K Ω).ker : Set (G K Ω)) := by
        ext x
        rw [Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
          MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, eq_comm]
      rw [this]
      exact hopen.preimage (continuous_const_mul g⁻¹)
    · push_neg at hy
      have : (artCl K Ω) ⁻¹' {y} = ∅ := by
        ext x
        simp [hy x]
      rw [this]
      exact isOpen_empty
