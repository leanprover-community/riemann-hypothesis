module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FoCong
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.t3Of :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) (a : W.R), (∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, a - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0)) → IsApproximateAnnihilatorAtLevels m a := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m a h j
  filter_upwards [h j, Λ.U_le (Filter.eventually_ge_atTop j)] with N hN hjN
  obtain ⟨a', ha', hor⟩ := hN
  obtain ⟨hf, hρf, -⟩ := foCong l L G0 T Λ n O r B u J D A W m j N hjN
  refine ⟨(fEl (T.Nq N) W.t.U * a') ^ (A.ex + 1), ?_, ?_⟩
  · have h1 : fo W * a - fEl (T.Nq N) W.t.U * a' ∈ maximalIdeal W.R ^ j := by
      have e : fo W * a - fEl (T.Nq N) W.t.U * a' =
          (fo W - fEl (T.Nq N) W.t.U) * a + fEl (T.Nq N) W.t.U * (a - a') := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ ha')
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (fo W * a) (fEl (T.Nq N) W.t.U * a') (A.ex + 1)
    rw [hc]
    exact Ideal.mul_mem_right _ _ h1
  · intro x
    rw [MN.smul_def, map_pow, map_mul, hρf]
    rcases hor with h0 | h0
    · rw [h0, mul_zero, zero_pow (Nat.succ_ne_zero _), zero_smul]
    · rw [pow_succ', mul_smul]
      exact (congrArg (fun y : (A.A N).M => (fEl (T.Nq N) (A.A N).U * (m.ρ N) a') • y) (h0 x)).trans
        (smul_zero _)
