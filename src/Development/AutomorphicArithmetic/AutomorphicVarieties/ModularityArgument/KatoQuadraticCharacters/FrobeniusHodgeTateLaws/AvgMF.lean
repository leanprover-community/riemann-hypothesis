module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SerVal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinTameWeightSecondEqCharacterSumStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMuModelMeasureOfEigenfunctional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqEisensteinProductParityStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IterULevelValStable
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob

@[expose] public section

open UpperTheory.V.Z.Kato.Joint GlobalTheory.EisM

theorem UpperTheory.V.Z.Kato.Joint.avgMF :
    UpperTheory.V.Z.Kato.Joint.AvgMF := by
  intro k l N m θ χ f t α B c hp hk hodd hN hlN hm hχ hf hα hE
  haveI : NeZero N := ⟨hN.ne'⟩
  have hsq : ∀ ν : DirichletCharacter ℂ N, ν (-1) * ν (-1) = 1 := fun ν => by rw [← map_mul]; simp
  have hform : ∀ ν : DirichletCharacter ℂ N, ν (-1) = -θ (-1) → MF k (N * l) (ch (θ⁻¹ * ν)) (frm l N m k θ ν f) :=
    fun ν hν => (GlobalTheory.iterU_level_val_stable k N l m (θ⁻¹ * ν) (fun _ => 0) α B c _ (by omega) hp hα
      (GlobalTheory.T.isModularFormCoeffSeq_eisensteinProduct_parity k N l m (θ⁻¹ * ν) θ ν f hk hodd hN hp hm hlN rfl hν hf)).1
  have hsign : (θ * χ) (-1) = -θ (-1) := by
    rw [MulChar.coeToFun_mul, Pi.mul_apply, hχ]; ring
  have hmain := hform (θ * χ) hsign
  rw [inv_mul_cancel_left] at hmain
  refine ⟨hmain, ?_⟩
  have hφ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hN).ne'
  have htw : tw2 N (θ (-1)) =
      fun y => ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) * ch ν y := by
    funext y
    rw [GlobalTheory.T.tw2_eq_inv_totient_mul_sum_characters N (θ (-1)) hN y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have hmes : mesMu k l (hat θ) (tw2 N (θ (-1))) α B c m f =
      ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) *
        ((α ^ m)⁻¹ * lam B c (frm l N m k θ ν f)) := by
    unfold mesMu
    rw [htw, funext (measMu_zm_sum k l (hat θ) Finset.univ _ _ _), measMu_val_sum]
    rfl
  rw [hmes, Finset.sum_eq_single_of_mem (θ * χ) (Finset.mem_univ _)]
  · have h2 : (1 : ℂ) - θ (-1) * (θ * χ) (-1) = 2 := by
      rw [hsign]; linear_combination hsq θ
    rw [h2]
    field_simp
  · intro ν _ hne
    have h0 : (ν (-1) - θ (-1)) * (ν (-1) + θ (-1)) = 0 := by linear_combination hsq ν - hsq θ
    rcases mul_eq_zero.1 h0 with h | h
    · rw [sub_eq_zero.1 h, hsq θ]; ring
    · have hne' : θ⁻¹ * ν ≠ χ := fun h' => hne (by rw [← h', mul_inv_cancel_left])
      rw [hE.kill _ _ hne' (hform ν (eq_neg_of_add_eq_zero_left h))]
      ring
