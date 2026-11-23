module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffMulPolyMemCcMat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastSide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiFiniteSubspace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open GlobalTheory.Orb GlobalTheory.PsCo.Pc1
open Formalism.REAL (UJ KG toM)

namespace GlobalTheory.ShapeSmoothFinite

theorem continuous_matCoord_ujMat {n : ℕ} (ε : Fin n → Bool) : Continuous (matCoord (ujMat ε)) :=
  (Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val

theorem mem_ccMat_and_isBiFinite {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : Mat n → ℂ) (hφ : φ ∈ ShapeM ε d) :
    (fun g : UJ ε => φ (toM g)) ∈ CcMat (ujMat ε) ∧ IsBiFinite (KG ε) (fun g : UJ ε => φ (toM g)) := by
  obtain ⟨h0, hadd, hsmul⟩ := GlobalTheory.isBiFinite_subspace (UJ ε) (KG ε)
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, ⟨hH, R, hR⟩, -, rfl⟩ := h
    exact ⟨GlobalTheory.CutoffPoly.cutoff_mul_poly_mem_ccMat n ε H R hH hR P, GlobalTheory.PolyShapeFinite.main n ε H P⟩
  | zero => exact ⟨Submodule.zero_mem _, h0⟩
  | add φ ψ _ _ h h' => exact ⟨Submodule.add_mem _ h.1 h'.1, hadd _ _ h.2 h'.2⟩
  | smul c φ _ h => exact ⟨Submodule.smul_mem _ c h.1, hsmul c _ h.2⟩

theorem stShape : GlobalTheory.PsCo.Pc1.StShape := by
  intro n ε d φ hφ
  obtain ⟨h1, h2⟩ := mem_ccMat_and_isBiFinite ε d φ hφ
  exact ⟨h1, h2, continuous_of_mem_ccSmooth (continuous_matCoord_ujMat ε) h1, (mem_ccSmooth.1 h1).1⟩

end GlobalTheory.ShapeSmoothFinite
