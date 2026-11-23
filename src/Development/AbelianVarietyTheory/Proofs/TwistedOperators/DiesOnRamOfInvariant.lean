module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlagVolumeFiltration
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal

noncomputable section
namespace GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} {q : Unif k}

theorem oneOrbit : OneOrbit k n c q := by
  have h1 : ∀ (L₁ L₂ : Submodule 𝒪[k] (n → k)) (f₁ f₂ : n → k), IsGlue L₁ f₁ → IsGlue L₂ f₂ →
      ∃ g : GL n k, g • L₁ = L₂ ∧ g • f₁ - f₂ ∈ L₂ := by
    intro L₁ L₂ f₁ f₂ g₁ g₂
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n k) (glue g₁) (glue g₂)
    refine ⟨g, by rw [← glue_ker g₁, ← Pair.smul_ker, hg, glue_ker], ?_⟩
    have := (glue_hasVal g₁).gl_smul g
    rwa [hg, Pair.hasVal_one_iff (glue_hasVal g₂), glue_ker] at this
  refine ⟨h1, fun L₀ _ Q h₀ e h => ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu, L'', f'', hG, H⟩
    obtain ⟨g, hg, hg'⟩ := h1 _ _ _ _ (Pair.isGlue Q.hasVal_vec) hG
    refine ⟨u * embX c g, mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩),
      (u * embX c g * h₀)⁻¹ * h, ?_, by group⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, mul_smul, mul_smul, e, embX_smul_gluedS, hg, H,
      gluedS_congr hg']
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    obtain ⟨g, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
    refine ⟨_, Radical.conj_mem g hu, g • Q.ker, g • Q.vec, ?_, ?_⟩
    · simpa using Pair.isGlue (Q.hasVal_vec.gl_smul g)
    · rw [← embX_smul_gluedS, ← e, mul_smul _ κ, show κ • L₀ = L₀ from hκ]
      simp only [mul_smul, inv_smul_smul]

instance isLattice_interX (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [hL : L.IsFullLattice k] : (interX L).IsLattice k := by
  apply Submodule.IsLattice.of_fg k
  exact Submodule.fg_of_fg_map_injective (inX k n c)
    (fun x y h => funext fun r => congrFun h (Sum.inl r))
    (hL.fg.of_le (Submodule.map_comap_le _ _))

variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]

end GlobalTheory.LevelUnfold
