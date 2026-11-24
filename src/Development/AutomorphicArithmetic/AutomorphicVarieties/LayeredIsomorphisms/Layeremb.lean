module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Rootdeg
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

@[expose] public section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.layeremb :
    ∀ (l j N : ℕ), l.Prime → 0 < N → ∀ (L₀ L₁ : Type) [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
      [Algebra L₀ L₁], Nonempty (L₀ →ₐ[ℚ] CyclotomicField N ℚ) → IsLayer l j L₀ L₁ →
        ∃ N' : ℕ, 0 < N' ∧ N' ≤ 2 * Module.finrank ℚ L₁ * N ∧ Nonempty (L₁ →ₐ[ℚ] CyclotomicField N' ℚ) := by
  intro l j N hl hN L₀ L₁ _ _ _ _ _ ⟨f⟩ ⟨⟨k, hk⟩, _⟩
  have hlk : 0 < l ^ k := pow_pos hl.pos k
  have hM : 0 < l ^ k * N := Nat.mul_pos hlk hN
  haveI : NeZero (l ^ k) := ⟨hlk.ne'⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : NeZero ((l ^ k * N : ℕ) : ℚ) := ⟨by exact_mod_cast hM.ne'⟩
  refine ⟨l ^ k * N, hM, ?_, ?_⟩
  · exact Nat.mul_le_mul_right N (rootdeg L₁ l k hl ⟨_, IsCyclotomicExtension.zeta_spec (l ^ k) L₀ L₁⟩)
  · obtain ⟨ζ, hζ⟩ := @IsCyclotomicExtension.exists_isPrimitiveRoot _ ℚ (CyclotomicField (l ^ k * N) ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension _ ℚ) _ (Set.mem_singleton _) hM.ne'
    have hN' := hζ.pow hM rfl
    have hl' := hζ.pow hM (Nat.mul_comm _ _)
    have i2 := @IsCyclotomicExtension.isSplittingField_X_pow_sub_one N _ ℚ (CyclotomicField N ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension N ℚ)
    let e : CyclotomicField N ℚ →+* CyclotomicField (l ^ k * N) ℚ :=
      (@Polynomial.IsSplittingField.lift (CyclotomicField (l ^ k * N) ℚ) ℚ (CyclotomicField N ℚ) _ _ _ _ _
        (Polynomial.X ^ N - 1) i2 (by simpa using Polynomial.X_pow_sub_one_splits hN')).toRingHom
    letI : Algebra L₀ (CyclotomicField (l ^ k * N) ℚ) := (e.comp f.toRingHom).toAlgebra
    haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one (l ^ k) L₀ L₁
    let h : L₁ →ₐ[L₀] CyclotomicField (l ^ k * N) ℚ :=
      Polynomial.IsSplittingField.lift _ (Polynomial.X ^ (l ^ k) - 1)
        (by simpa using Polynomial.X_pow_sub_one_splits hl')
    exact ⟨h.toRingHom.toRatAlgHom⟩
