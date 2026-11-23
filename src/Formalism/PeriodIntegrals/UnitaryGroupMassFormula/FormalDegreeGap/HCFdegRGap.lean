module

public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

def HCFdegRGap : Prop :=
  ∀ (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal), Formalism.MainNotions.RT.cdScaleTieR cd s →
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ),
    1 ≤ (Finset.univ.filter (fun a => ε a = true)).card →
    1 ≤ (Finset.univ.filter (fun a => ε a = false)).card →
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
    32 * (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) + 2 < h →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
      fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam

end PI.UnitaryGroupMassFormula.HCFdegRGap
