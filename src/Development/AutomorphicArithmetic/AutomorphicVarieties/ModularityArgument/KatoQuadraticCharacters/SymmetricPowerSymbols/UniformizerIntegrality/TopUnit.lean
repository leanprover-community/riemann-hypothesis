module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRingOfIntegersOfHol
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.IsSymb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.IsIntegralOfMemOverY
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT Polynomial

namespace UpperTheory.V.Z.Kato.Sym.PT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem mem_int (X : Tower Ω ε) (M : ℕ) (f : topL X M) (h : IsIntegral (Algebra.adjoin Ω {X.jK}) (f : X.K)) :
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    f ∈ FunctionField.ringOfIntegers Ω (topL X M) := by
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  obtain ⟨p, hpm, hp⟩ := h
  have hmem : ∀ P : Polynomial Ω, aeval X.jK P ∈ Algebra.adjoin Ω {X.jK} := fun P => by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨P, rfl⟩
  let g : Polynomial Ω →+* Algebra.adjoin Ω {X.jK} :=
    ((aeval X.jK).codRestrict (Algebra.adjoin Ω {X.jK}) hmem).toRingHom
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨P, rfl⟩ := hy
    exact ⟨P, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ :=
    lifts_and_natDegree_eq_and_monic ((lifts_iff_coeff_lifts p).mpr fun n => hg _) hpm
  refine ⟨q, hqm, Subtype.val_injective ?_⟩
  have e1 : ((topL X M).subtype).comp (algebraMap (Polynomial Ω) (topL X M)) =
      (aeval X.jK : Polynomial Ω →ₐ[Ω] X.K).toRingHom := RingHom.ext fun P => coe_jPoly X _ P
  have e2 : (algebraMap (Algebra.adjoin Ω {X.jK}) X.K).comp g =
      (aeval X.jK : Polynomial Ω →ₐ[Ω] X.K).toRingHom := RingHom.ext fun P => rfl
  have key := Polynomial.hom_eval₂ q (algebraMap (Polynomial Ω) (topL X M)) (topL X M).subtype f
  rw [e1] at key
  rw [← hq, eval₂_map, e2] at hp
  show (topL X M).subtype (eval₂ (algebraMap (Polynomial Ω) (topL X M)) f q) = ((0 : topL X M) : X.K)
  rw [key, ZeroMemClass.coe_zero]
  exact hp

theorem isTopUnit [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (M : ℕ) {u : X.K} (hu : IsU X u) (hF : u ∈ topF X M) :
    TopUnits.IsTopUnit X M u :=
  ⟨hu.1, hF, mdl_le_lev X _ _ hF, mem_int X M _ (intU Ω ε X M u hu).1, mem_int X M _ (intU Ω ε X M u hu).2⟩

end UpperTheory.V.Z.Kato.Sym.PT
