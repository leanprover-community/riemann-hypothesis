module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex
public import GroundTheory.GlobalFields.Adele.Approximation
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

open NumberField IsDedekindDomain

namespace UpperTheory.V.Z.Sym.Glob

theorem apx {F : Type} [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (y : ∀ v : Pl F, Kv v)
    (hy : ∀ v, cv v d * y v ∈ v.adicCompletionIntegers F) : ∃ x : F, ∀ v, y v - cv v x ∈ v.adicCompletionIntegers F := by
  classical
  have hinv : ∀ᶠ v in Filter.cofinite, cv v d⁻¹ ∈ (v : Pl F).adicCompletionIntegers F :=
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) d⁻¹).2
  have hev : ∀ᶠ v in Filter.cofinite, y v ∈ (v : Pl F).adicCompletionIntegers F := by
    refine hinv.mono fun v hv => ?_
    have e : y v = cv v d⁻¹ * (cv v d * y v) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hd, map_one, one_mul]
    rw [e]
    exact mul_mem hv (hy v)
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) (K := F)
    (RestrictedProduct.mk y hev : FiniteAdeleRing (𝓞 F) F)
  exact ⟨k, fun v => GroundTheory.Global.mem_integralFiniteAdeles.mp hk v⟩

end UpperTheory.V.Z.Sym.Glob
