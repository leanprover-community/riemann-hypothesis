module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLInvolutive
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nrmL_twconj (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) (g δ : GLw a w) :
    nrmL a w (g⁻¹ * δ * thL a w g) = g⁻¹ * nrmL a w δ * g := by
  have ht : ∀ y : GLw a w, nrmL a w y = y * thL a w y := fun y => by
    unfold nrmL thL
    rw [if_neg hw, if_neg hw]
  rw [ht, ht, map_mul, map_mul, map_inv, GlobalTheory.BCT.TwistInvol.thL_involutive]
  group

theorem nrm_twconj_pf (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) (g δ : GLw a w) :
    (nrmL a w (g⁻¹ * δ * thL a w g)).val.charpoly = (nrmL a w δ).val.charpoly := by
  rw [nrmL_twconj w hw a g δ]
  have h := Matrix.charpoly_units_conj g⁻¹ (nrmL a w δ).val
  simpa [Units.val_mul, mul_assoc] using h

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
