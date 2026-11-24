module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HasseJidPow
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem sumN_eq {σ : Type*} (β : σ →₀ ℕ) : (β.sum fun _ n => n) = Finsupp.degree β := rfl

theorem mem_Jid_smul_top_of_JHfr {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (u : WeightFamilies.Wt D j)
    {b : ℕ} (hb : 1 ≤ b) (y : ↥(HK X la w u)) (hy : (y : Lw X la w) ∈ JHfr X la w u b) :
    y ∈ Jid X la w • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) := by
  have h1 : y ∈ Jid X la w ^ b • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) :=
    (mem_Jid_pow_smul_top X la w).2 ((mem_JHfr X la w).1 hy)
  exact Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) h1

theorem hasseVan_holds : HasseVan := by
  intro D B P j X ka wL wF G la a x hx β hβ h
  rw [reduction_eq_zero_iff_mem_ideal_smul]
  have hx' : (x : Lw X la G.w) ∈ JHfr X la G.w wF a :=
    (mem_JHfr X la G.w).2 ((mem_Jid_pow_smul_top X la G.w).1 hx)
  have h2 := hasse_jid_power X la G.w wF β a _ hx'
  exact mem_Jid_smul_top_of_JHfr X la G.w wF (b := a - β.sum fun _ n => n) (by omega) ⟨_, h⟩ h2

end PoleLengthBounds
