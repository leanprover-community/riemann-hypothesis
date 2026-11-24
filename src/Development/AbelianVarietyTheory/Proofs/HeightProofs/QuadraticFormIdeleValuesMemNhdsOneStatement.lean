module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticFormIdeleValuesMemNhdsOne
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

open NumberField IsDedekindDomain
open scoped Topology

theorem _root_.GlobalTheory.T.quadraticForm_ideleValues_mem_nhds_one : ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → {a : (AdeleRing (𝓞 F) F)ˣ | ∃ x y : AdeleRing (𝓞 F) F, (a : AdeleRing (𝓞 F) F) = x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2} ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) := by
  first | exact @GlobalTheory.QNorm.norm_form_mem_nhds_one | exact GlobalTheory.QNorm.norm_form_mem_nhds_one | (intros; apply GlobalTheory.QNorm.norm_form_mem_nhds_one <;> assumption)
