module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Span
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem localizedModule_mem_annSpan_smul_top (D : Type) [CommRing D] (S : Submonoid D) (x : D)
    (N : Type 1) [AddCommGroup N] [Module D N]
    (h : ∀ n : N, x • n = 0 → n ∈ Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N)) :
    ∀ n : LocalizedModule S N, algebraMap D (Localization S) x • n = 0 →
      n ∈ Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} •
        (⊤ : Submodule (Localization S) (LocalizedModule S N)) := by
  intro n hn
  set J : Ideal (Localization S) :=
    Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} with hJ
  have hIJ : Ideal.span {a : D | x * a = 0} ≤ J.comap (algebraMap D (Localization S)) := by
    rw [Ideal.span_le]
    intro a ha
    show algebraMap D (Localization S) a ∈ J
    apply Ideal.subset_span
    show algebraMap D (Localization S) x * algebraMap D (Localization S) a = 0
    rw [← map_mul, show x * a = 0 from ha, map_zero]
  have key : Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N) ≤
      ((J • (⊤ : Submodule (Localization S) (LocalizedModule S N))).restrictScalars D).comap
        (LocalizedModule.mkLinearMap S N) := by
    rw [Submodule.smul_le]
    intro r hr m _
    show LocalizedModule.mk (r • m) 1 ∈ J • (⊤ : Submodule (Localization S) (LocalizedModule S N))
    rw [← LocalizedModule.smul'_mk, ← algebraMap_smul (Localization S) r]
    exact Submodule.smul_mem_smul (hIJ hr) trivial
  induction n using LocalizedModule.induction_on with
  | _ m s =>
    rw [algebraMap_smul (Localization S) x, LocalizedModule.smul'_mk,
      ← LocalizedModule.zero_mk (1 : S), LocalizedModule.mk_eq] at hn
    obtain ⟨u, hu⟩ := hn
    simp only [one_smul, smul_zero] at hu
    have hxu : x • (u • m) = 0 := by rw [smul_comm]; exact hu
    have hmem := key (h _ hxu)
    have he : LocalizedModule.mk m s =
        (Localization.mk 1 (u * s) : Localization S) • LocalizedModule.mk (u • m) 1 := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one, LocalizedModule.mk_cancel_common_left]
    rw [he]
    exact Submodule.smul_mem _ _ hmem

end GlobalTheory
