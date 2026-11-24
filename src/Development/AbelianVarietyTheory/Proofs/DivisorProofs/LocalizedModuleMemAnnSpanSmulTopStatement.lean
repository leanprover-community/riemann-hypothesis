module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedModuleMemAnnSpanSmulTop
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.localizedModule_mem_annSpan_smul_of_mem : ∀ (D : Type) [CommRing D] (S : Submonoid D) (x : D) (N : Type 1) [AddCommGroup N] [Module D N], (∀ n : N, x • n = 0 → n ∈ Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N)) → ∀ n : LocalizedModule S N, algebraMap D (Localization S) x • n = 0 → n ∈ Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} • (⊤ : Submodule (Localization S) (LocalizedModule S N)) := by
  first | exact @GlobalTheory.localizedModule_mem_annSpan_smul_top | exact GlobalTheory.localizedModule_mem_annSpan_smul_top | (intros; apply GlobalTheory.localizedModule_mem_annSpan_smul_top <;> assumption)
