module

public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

theorem concl_of_nat {j : ℕ} (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) (r : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hnu : ∀ la, 0 ≤ nus la) (hr0 : ∀ la, 0 ≤ r la) (hrs : Summable (fun la => r la * X.lN la))
    (hrb : (∑' la, r la * X.lN la) ≤ β)
    (hloc : ∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∀ V' : Submodule (X.Kl la) (X.Vl la), V' ≤ X.locK la (X.Msup ka) →
        X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
        ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
            (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
          (e : ℝ) * (Module.finrank (X.Kl la) V' : ℝ) + r la) :
    Concl X S ka wL wF T nus β := by
  unfold Concl
  refine ⟨r, hr0, hrs, hrb, ?_⟩
  intro la e he V' hV'
  have hT : (0 : ℝ) ≤ (T : ℝ) * nus la := mul_nonneg (Nat.cast_nonneg _) (hnu la)
  have he0 : (0 : ℤ) ≤ e := by
    have h := hT.trans he
    exact_mod_cast h
  lift e to ℕ using he0 with n
  have h := hloc la n (by exact_mod_cast he) V' hV'
  simpa only [Int.cast_natCast] using h

end Formalism.MainNotions.Gaps.EtaleWeightGaps
