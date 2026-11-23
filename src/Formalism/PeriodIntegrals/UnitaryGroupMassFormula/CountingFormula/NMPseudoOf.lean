module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module IsDedekindDomain Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

theorem nMPseudo_of (hE : JordanExists) (hD : DetLocal) (hC : CountExt) (hA : NormAssembly) : NMPseudo := by
  intro K F V ι _ _ _ _ _ _ _ _ _ _ _ _ _ h X x 𝔞 hcm hfix h2 hsymm hstar hne hind hspan hdet hint
  have hJ0 : (∏ i, 𝔞 i ^ 2) * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hne i))
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdet)
  have key : ∀ (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)), 𝔭.IsMaximal →
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          ((P.asIdeal.ramificationIdx (𝓞 F) * vJ h X (pbLat x 𝔞) 𝔭 : ℕ) : ℤ) := by
    intro 𝔭 P h𝔭 hP
    obtain ⟨b, a, hba⟩ := hE K F V ι h X x 𝔞 hcm hfix h2 hsymm hstar hne hind hspan hdet hint 𝔭 h𝔭
    have hcount : ∀ b' a', IsJordanIn h X (pbLat x 𝔞) 𝔭 b' a' →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          ((P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a' : ℕ) : ℤ) := by
      intro b' a' h'
      rw [hD K F V ι h X x 𝔞 hfix hstar hne hind hspan hdet 𝔭 b' a' h𝔭 h' P hP,
        hC K F _ 𝔭 P a' h𝔭 hP h'.2.2.2.2]
      rfl
    have he : P.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := by
      haveI := P.isPrime
      exact (Ideal.ramificationIdx_pos (R := 𝓞 F) P.asIdeal).ne'
    have hv : vJ h X (pbLat x 𝔞) 𝔭 = vJof 𝔭 a := by
      unfold vJ
      have hset : {v | ∃ b a, IsJordanIn h X (pbLat x 𝔞) 𝔭 b a ∧ v = vJof 𝔭 a} = {vJof 𝔭 a} := by
        ext v
        constructor
        · rintro ⟨b', a', h', rfl⟩
          have h3 := (hcount b' a' h').symm.trans (hcount b a hba)
          have h4 : P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a' = P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a := by
            exact_mod_cast h3
          exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he) h4
        · rintro rfl
          exact ⟨b, a, hba, rfl⟩
      rw [hset, csInf_singleton]
    rw [hv]
    exact hcount b a hba
  exact hA K F h2 _ (vJ h X (pbLat x 𝔞)) hJ0 key

end PI.UnitaryGroupMassFormula.CntFormula.R6
