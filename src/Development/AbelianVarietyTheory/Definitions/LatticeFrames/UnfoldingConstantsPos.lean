module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
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

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace

variable (D : D7) (u : D.what₂.Word)

def d0 : ℕ := Module.finrank ℂ (D.s.Cu u)

def hsDev : ℝ := hsNormSq (Kmat D.s u u - ContinuousLinearMap.id ℂ (D.s.Cu u))

def DiagS (e : ℝ) : Prop := hsDev D u ≤ e * (d0 D u : ℝ)

def SAbs (Γ₀ : ℝ) : Prop := hsDev D u ≤ Γ₀ * (d0 D u : ℝ) ^ 2 / D.what₂.Dstar + (d0 D u : ℝ) / 4

abbrev Desc : Type := (D.mem u).P.Mt →ₗ⋆[ℂ] D.s.HH

def MIMap (Θ : Desc D u) : Prop :=
  ∃ (s l : ℂ) (FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u), l ≠ 0 ∧ Function.Injective FF ∧
    ∀ (φ : (D.mem u).A.Mram) (F : (D.mem u).P.Mt),
      s * PhiC (D.mem u).C (D.mem u).A (D.mem u).P φ F = l * ⟪Θ F, D.s.Pu u (FF φ)⟫_ℂ

def OntoAll (Θ : Desc D u) : Prop := Function.Surjective Θ

def RamShare : Prop :=
  (dU D u : ℝ) = (d0 D u : ℝ) * (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f

def RamBig (δ : ℝ) : Prop := 0 < dU D u ∧ (1 - δ) * (d0 D u : ℝ) ≤ (dU D u : ℝ)

theorem d0_eq : d0 D u = D.duS u := (D.s_Cu u).finrank_eq

end GlobalTheory.Core.Rk

end
