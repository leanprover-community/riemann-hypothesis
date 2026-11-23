module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Ideal.Defs
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Basic

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem family_congr_basis_mod_nilpotent (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (ι : Type) (b b' : ι → M) (I : Ideal R) (n : ℕ) :
    I ^ n = ⊥ → LinearIndependent R b → Submodule.span R (Set.range b) = ⊤ →
    (∀ k, b' k - b k ∈ I • (⊤ : Submodule R M)) →
    LinearIndependent R b' ∧ Submodule.span R (Set.range b') = ⊤ := by
  intro hIn hli hsp hb
  let B : Module.Basis ι R M := Module.Basis.mk hli (by rw [hsp])
  let ν : Module.End R M := B.constr R (fun i => b' i - b i)
  have hν : ∀ i, ν (b i) = b' i - b i := by
    intro i
    have := B.constr_basis R (fun i => b' i - b i) i
    simpa [B, Module.Basis.mk_apply] using this
  have hrange : LinearMap.range ν ≤ I • (⊤ : Submodule R M) := by
    have e : LinearMap.range ν = Submodule.map ν (Submodule.span R (Set.range b)) := by
      rw [hsp, LinearMap.range_eq_map]
    rw [e, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    show ν (b i) ∈ _
    rw [hν]; exact hb i
  have hpow : ∀ k : ℕ, LinearMap.range (ν ^ k) ≤ I ^ k • (⊤ : Submodule R M) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
      calc Submodule.map ν (LinearMap.range (ν ^ k))
          ≤ Submodule.map ν (I ^ k • (⊤ : Submodule R M)) := Submodule.map_mono ih
        _ = I ^ k • Submodule.map ν ⊤ := Submodule.map_smul'' _ _ _
        _ ≤ I ^ k • (I • (⊤ : Submodule R M)) := by
            exact Submodule.smul_mono le_rfl (by rw [← LinearMap.range_eq_map]; exact hrange)
        _ = I ^ (k + 1) • (⊤ : Submodule R M) := by
            rw [pow_succ, Submodule.mul_smul]
  have hnil : IsNilpotent ν := by
    refine ⟨n, ?_⟩
    have := hpow n
    rw [hIn, Submodule.bot_smul, le_bot_iff, LinearMap.range_eq_bot] at this
    exact this
  have hunit : IsUnit (1 + ν) := hnil.isUnit_one_add
  have hbij : Function.Bijective ⇑(1 + ν) := (Module.End.isUnit_iff _).1 hunit
  have hcomp : b' = ⇑(1 + ν) ∘ b := by
    funext i; simp [hν]
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact hli.map' (1 + ν) (LinearMap.ker_eq_bot.2 hbij.1)
  · rw [hcomp, Set.range_comp, ← Submodule.map_span, hsp, ← LinearMap.range_eq_map,
      LinearMap.range_eq_top.2 hbij.2]

end GlobalTheory.BSP
