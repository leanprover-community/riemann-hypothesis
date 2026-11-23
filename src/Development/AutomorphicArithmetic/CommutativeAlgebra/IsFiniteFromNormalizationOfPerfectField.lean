module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
public import Mathlib.AlgebraicGeometry.Normalization
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ModuleFiniteIntegralClosureOfFiniteTypePerfect
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

theorem UpperTheory.isFinite_fromNormalization_of_perfectField :
    ∀ (k : Type) [Field k] [PerfectField k] {D T : Scheme.{0}} (t : T ⟶ Sp k) [LocallyOfFiniteType t] (f : D ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f] [IsIntegral D], IsFinite f.fromNormalization := by
  intro k _ _ D T t _ f _ _ _ _
  rw [isFinite_iff]
  refine ⟨inferInstance, fun U hU => ?_⟩
  rw [f.fromNormalization_app hU]
  letI := (f.app U).hom.toAlgebra
  have h : Module.Finite Γ(T, U) (integralClosure Γ(T, U) Γ(D, f ⁻¹ᵁ U)) := by
    rcases (f ⁻¹ᵁ U).1.eq_empty_or_nonempty with hE | hN
    · have hb : f ⁻¹ᵁ U = ⊥ := SetLike.ext' hE
      haveI : Subsingleton Γ(D, f ⁻¹ᵁ U) :=
        CommRingCat.subsingleton_of_isTerminal (D.sheaf.isTerminalOfEqEmpty hb)
      infer_instance
    · obtain ⟨x, hx⟩ := hN
      obtain ⟨V, hV, hxV, hVle⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp D.isBasis_affineOpens) hx
      haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
      haveI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
      have hkt : (t.appLE ⊤ U (by simp)).hom.FiniteType :=
        LocallyOfFiniteType.finiteType_appLE t (isAffineOpen_top _) hU (by simp)
      let kA : k →+* Γ(T, U) :=
        (t.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      have hkA : kA.FiniteType :=
        hkt.comp (RingHom.FiniteType.of_surjective _
          (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
      letI : Algebra k Γ(T, U) := kA.toAlgebra
      haveI : Algebra.FiniteType k Γ(T, U) := hkA
      haveI : IsNoetherianRing Γ(T, U) := Algebra.FiniteType.isNoetherianRing k Γ(T, U)
      have heq : (D.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom =
          (D.germToFunctionField V).hom.comp (f.appLE U V hVle).hom := by
        rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
        congr 1
        simp [Scheme.Hom.appLE]
      let φ : Γ(T, U) →+* D.functionField :=
        (D.germToFunctionField V).hom.comp (f.appLE U V hVle).hom
      letI : Algebra Γ(T, U) D.functionField := φ.toAlgebra
      have h1 : (D.germToFunctionField V).hom.EssFiniteType := GlobalTheory.essFiniteType_germ hV _ _
      have h2 : (f.appLE U V hVle).hom.EssFiniteType :=
        (LocallyOfFiniteType.finiteType_appLE f hU hV hVle).essFiniteType
      haveI : Algebra.EssFiniteType Γ(T, U) D.functionField := h2.comp h1
      haveI := UpperTheory.module_finite_integralClosure_of_finiteType_perfect k Γ(T, U) D.functionField
      let ψ : Γ(D, f ⁻¹ᵁ U) →ₐ[Γ(T, U)] D.functionField :=
        { (D.germToFunctionField (f ⁻¹ᵁ U)).hom with
          commutes' := fun a => by
            change (D.germToFunctionField (f ⁻¹ᵁ U)).hom ((f.app U).hom a) = φ a
            exact congrArg (fun g => g a) heq }
      exact GlobalTheory.finite_integralClosure_of_family (ι := Unit) (L := fun _ => D.functionField)
        (fun _ => ψ) (fun b hb => D.germToFunctionField_injective (f ⁻¹ᵁ U)
          (by rw [map_zero]; exact hb ()))
  rw [CommRingCat.hom_comp]
  refine RingHom.Finite.comp ?_ ?_
  · exact RingHom.Finite.of_surjective _
      (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.symm.surjective
  · exact (RingHom.finite_algebraMap).mpr h
