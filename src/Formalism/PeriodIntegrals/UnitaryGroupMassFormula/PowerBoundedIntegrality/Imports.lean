module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Development
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.PowBddIntWork

open Matrix NumberField

theorem stepA : StepA := by
  intro E _ _ k γ N hN hint
  classical
  let L : (Fin k → Fin k → 𝓞 E) →ₗ[ℤ] Matrix (Fin k) (Fin k) E :=
    { toFun := fun B => Matrix.of fun i j => ((N : E))⁻¹ * algebraMap (𝓞 E) E (B i j)
      map_add' := fun B C => by ext i j; simp [mul_add]
      map_smul' := fun c B => by
        ext i j
        first | (simp [zsmul_eq_mul]; ring) | simp [zsmul_eq_mul] }
  have hfg : (Submodule.map L ⊤).FG := Module.Finite.fg_top.map L
  have hle : Subalgebra.toSubmodule (Algebra.adjoin ℤ {γ}) ≤ Submodule.map L ⊤ := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro x hx
    obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
    refine ⟨fun i j => IsIntegralClosure.mk' (𝓞 E) ((N : E) * (γ ^ n) i j) (hint n i j), trivial, ?_⟩
    have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
    ext i j
    simp [L, IsIntegralClosure.algebraMap_mk', hN']
  haveI := isNoetherian_of_fg_of_noetherian _ hfg
  exact isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ {γ}) (isNoetherian_of_le hle) γ
    (Algebra.subset_adjoin (Set.mem_singleton γ))

end PI.PowBddIntWork
