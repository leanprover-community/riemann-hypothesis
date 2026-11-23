module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwRamSplit
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.kwRamSub :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (L : IntermediateField ℚ Ω) [NumberField L] [IsAbelianGalois ℚ L] (M : ℕ), 0 < M → (∀ p : ℕ, p.Prime → ¬ p ∣ M → UnramAt L p) → ∃ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (M ^ n) ∧ L ≤ ℚ⟮ζ⟯ := by
  intro Ω _ _ _ L _ _ M hM hram
  obtain ⟨n, ⟨g⟩⟩ := kwRam L M hM hram
  haveI : NeZero (M ^ n) := ⟨by positivity⟩
  haveI : NeZero ((M ^ n : ℕ) : ℚ) := ⟨by exact_mod_cast (show M ^ n ≠ 0 by positivity)⟩
  haveI : IsCyclotomicExtension {M ^ n} ℚ (CyclotomicField (M ^ n) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (M ^ n) ℚ
    · rfl
  haveI : NumberField (CyclotomicField (M ^ n) ℚ) :=
    IsCyclotomicExtension.numberField {M ^ n} ℚ _
  have hgal : IsGalois ℚ L := IsAbelianGalois.toIsGalois
  obtain ⟨ξ, hξ⟩ : ∃ z : CyclotomicField (M ^ n) ℚ, IsPrimitiveRoot z (M ^ n) :=
    ⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩
  let ψ : CyclotomicField (M ^ n) ℚ →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨n, ψ ξ, hξ.map_of_injective ψ.injective, ?_⟩
  have hnorm : (ψ.comp g).fieldRange = L :=
    @AlgHom.fieldRange_of_normal ℚ Ω _ _ _ L
      (by convert hgal.to_normal; all_goals first | rfl | exact Subsingleton.elim _ _) (ψ.comp g)
  rw [← hnorm]
  intro x hx
  obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
  have hy : g y ∈ Algebra.adjoin ℚ {ξ} := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hξ]
    trivial
  have hψ : ψ (g y) ∈ Algebra.adjoin ℚ {ψ ξ} := by
    rw [← Set.image_singleton, ← AlgHom.map_adjoin]
    exact ⟨g y, hy, rfl⟩
  exact IntermediateField.algebra_adjoin_le_adjoin ℚ {ψ ξ} hψ
