module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
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

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Iwasawa

theorem map_mem_GLint {F : Type} [Field F] [ValuativeRel F] {n : ℕ}
    (k : GL (Fin n) (ValuativeRel.valuation F).valuationSubring) :
    GeneralLinearGroup.map (algebraMap (ValuativeRel.valuation F).valuationSubring F) k ∈
      GLint 𝒪[F] n := by
  have key : ∀ (u : GL (Fin n) (ValuativeRel.valuation F).valuationSubring),
      IsInt 𝒪[F] ((GeneralLinearGroup.map
        (algebraMap (ValuativeRel.valuation F).valuationSubring F) u : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) := by
    intro u i j
    have h := (u.1 i j).2
    exact h
  refine ⟨key k, ?_⟩
  rw [← map_inv]
  exact key k⁻¹

theorem exists_upper_mul_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (h : LF O ϖ nrm q) (n : ℕ) (g : GL (Fin n) F) :
    ∃ b : GL (Fin n) F, (b : Matrix (Fin n) (Fin n) F).BlockTriangular id ∧
      ∃ k ∈ GLint O n, g = b * k := by
  obtain rfl := h.O_eq
  obtain ⟨k, b, hb, hg⟩ :=
    GlobalTheory.ValIwasawa.iwasawa (ValuativeRel.valuation F).valuationSubring F n g⁻¹
  refine ⟨b⁻¹, ?_, _, (GLint _ n).inv_mem (map_mem_GLint k), ?_⟩
  · let _ : Invertible (b : Matrix (Fin n) (Fin n) F) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  · rw [← _root_.mul_inv_rev, ← hg, inv_inv]

end GlobalTheory.CompanionTheory.QL.Iwasawa
