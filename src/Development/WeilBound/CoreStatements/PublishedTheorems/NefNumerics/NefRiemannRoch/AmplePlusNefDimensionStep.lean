module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.AmplePlusNefIntegralStep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem isAmpleLB_tens_of_nef_descent : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → topologicalKrullDim X = (d + 1 : ℕ) → ∀ A N : LB X, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N) := by
  intro k _ _ d ih X _ _ hproj hdim A N hA hN
  have ampOfCls : ∀ {L M : LB X} (hL : L.IsLB) (hM : IsAmpleLB M), cls L hL = cls M hM.isLB → IsAmpleLB L :=
    fun hL hM h => IsAmpleLB.of_lbIso hM hL ((cls_eq_iff hL hM.isLB).1 h)
  obtain ⟨c, hc1, hcM⟩ := exists_isAmpleLB_tens_lbPow k X hproj A N hA hN.isLB
  have hMLB : (tens N (lbPow A c)).IsLB := isLB_tens hN.isLB (isLB_lbPow hA.isLB c)
  have hMcls : cls (tens N (lbPow A c)) hMLB = cls N hN.isLB + c • cls A hA.isLB := by
    rw [cls_tens hN.isLB (isLB_lbPow hA.isLB c), cls_lbPow hA.isLB]
  set I := interNum k (GlobalTheory.structureModule X) (Fin.cons A (fun _ : Fin d => tens N (lbPow A c)) : Fin (d + 1) → LB X)
  set q : ℕ := (2 * ((d : ℤ) + 1) * I).toNat + 1 with hqdef
  have hq1 : 1 ≤ q := by omega
  have hqlt : 2 * ((d : ℤ) + 1) * I < (q : ℤ) := by
    have := Int.self_le_toNat (2 * ((d : ℤ) + 1) * I)
    rw [hqdef]; push_cast; linarith
  have hP : ∀ b : ℕ, (tens (lbPow N q) (lbPow A b)).IsLB :=
    fun b => isLB_tens (isLB_lbPow hN.isLB q) (isLB_lbPow hA.isLB b)
  have clsP : ∀ b : ℕ, cls _ (hP b) = q • cls N hN.isLB + b • cls A hA.isLB := by
    intro b
    rw [cls_tens (isLB_lbPow hN.isLB q) (isLB_lbPow hA.isLB b), cls_lbPow hN.isLB, cls_lbPow hA.isLB]
  have base : IsAmpleLB (tens (lbPow N q) (lbPow A (c * q))) := by
    have hpow : IsAmpleLB (lbPow (tens N (lbPow A c)) q) := (isAmpleLB_pow_iff hMLB hq1).2 hcM
    refine ampOfCls (hP _) hpow ?_
    rw [clsP, cls_lbPow hMLB, hMcls, smul_add, smul_smul, mul_comm q c]
  have hcq : q ≤ c * q := by nlinarith
  have down : ∀ j : ℕ, j ≤ c * q - q → IsAmpleLB (tens (lbPow N q) (lbPow A (c * q - j))) := by
    intro j
    induction j with
    | zero => intro _; simpa using base
    | succ j hj =>
      intro hj1
      have hprev := hj (by omega)
      have e : c * q - j = (c * q - (j + 1)) + 1 := by omega
      rw [e] at hprev
      exact isAmpleLB_tens_lbPow_descent_step k d ih X hproj hdim A N (tens N (lbPow A c)) hA hN hMLB q c hq1
        hMcls hqlt (c * q - (j + 1)) (by omega) (by omega) hprev
  have hqq := down (c * q - q) le_rfl
  have e2 : c * q - (c * q - q) = q := by omega
  rw [e2] at hqq
  have hTLB : (tens A N).IsLB := isLB_tens hA.isLB hN.isLB
  have hpow : IsAmpleLB (lbPow (tens A N) q) := by
    refine ampOfCls (isLB_lbPow hTLB q) hqq ?_
    rw [cls_lbPow hTLB, cls_tens hA.isLB hN.isLB, clsP, smul_add, add_comm]
  exact (isAmpleLB_pow_iff hTLB hq1).1 hpow

end GlobalTheory
