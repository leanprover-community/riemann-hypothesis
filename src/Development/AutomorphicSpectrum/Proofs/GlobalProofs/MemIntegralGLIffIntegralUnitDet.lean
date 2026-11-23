module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormPropertiesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QLDet

variable {F : Type} [Field F]

theorem det_mem_of_isInt (O : Subring F) {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsInt O M) :
    M.det ∈ O := by
  let M' : Matrix (Fin n) (Fin n) O := fun a b => ⟨M a b, h a b⟩
  have hM : M = O.subtype.mapMatrix M' := by
    ext a b
    rfl
  rw [hM, ← RingHom.map_det]
  exact (M'.det).2

theorem adjugate_isInt (O : Subring F) {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsInt O M) :
    IsInt O M.adjugate := by
  let M' : Matrix (Fin n) (Fin n) O := fun a b => ⟨M a b, h a b⟩
  have hM : M = O.subtype.mapMatrix M' := by
    ext a b
    rfl
  intro a b
  rw [hM, ← RingHom.map_adjugate]
  exact (M'.adjugate a b).2

theorem mem_GLint_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (hLF : LF O ϖ nrm q) (n : ℕ) (g : GL (Fin n) F) :
    g ∈ GLint O n ↔ (IsInt O (g : Matrix (Fin n) (Fin n) F) ∧
      nrm (g : Matrix (Fin n) (Fin n) F).det = 1) := by
  obtain ⟨-, -, hO, -, -, -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties hLF
  have hdet : (g : Matrix (Fin n) (Fin n) F).det * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ : IsInt O (g : Matrix (Fin n) (Fin n) F) ∧
        IsInt O ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := hg
    refine ⟨h1, ?_⟩
    have a1 := (hO _).2 (det_mem_of_isInt O h1)
    have a2 := (hO _).2 (det_mem_of_isInt O h2)
    have hm : nrm (g : Matrix (Fin n) (Fin n) F).det *
        nrm ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
      rw [← map_mul, hdet, map_one]
    have p1 := nrm.nonneg (g : Matrix (Fin n) (Fin n) F).det
    have p2 := nrm.nonneg ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det
    nlinarith
  · rintro ⟨h1, h2⟩
    show IsInt O (g : Matrix (Fin n) (Fin n) F) ∧ IsInt O ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    refine ⟨h1, ?_⟩
    intro a b
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    apply O.mul_mem
    · apply (hO _).1
      rw [map_inv₀, h2, inv_one]
    · exact adjugate_isInt O h1 a b

end GlobalTheory.CompanionTheory.QLDet
