module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem valC_finiteDimensional {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) :
    FiniteDimensional ℂ (ValC (Gr emb σ n) lam) := by
  classical
  have h := span_evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ
  have h2 : ValC (Gr emb σ n) lam ≤
      Submodule.span ℂ (Set.range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i)) := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨F, rfl⟩

    rw [← (bVV K lam).sum_repr F, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI := FiniteDimensional.span_of_finite ℂ
    (Set.finite_range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i))
  exact Submodule.finiteDimensional_of_le h2

theorem GStep.fi_finiteDimensional {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K]
    [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)
    (hS : S.Ok) : FiniteDimensional ℂ (S.Fi emb σ lam) := by
  haveI := hS.fin_orb
  haveI := valC_finiteDimensional emb σ lam
  let f : S.Fi emb σ lam →ₗ[ℂ] (S.Cl → ValC (Gr emb σ n) lam) :=
    { toFun := fun φ c => ⟨φ.1 c, (φ.2 c).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun a b hab => ?_
  apply Subtype.ext
  funext c
  exact congrArg Subtype.val (congrFun hab c)

end GlobalTheory.Mem.Col2
