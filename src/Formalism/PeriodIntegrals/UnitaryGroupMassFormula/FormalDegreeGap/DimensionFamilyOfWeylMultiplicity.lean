module

public import Formalism.LocalRingCardinality.DataTies
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

@[expose] public section

noncomputable section

open MeasureTheory

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.StandardLattice

theorem dsigEx_at (D : D7) (hd : dsigTie D) (ρ : D.what₂.Tau)
    (hex : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) (lamSH D.R (D.hc ρ)) σ) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) (lamSH D.R (D.hc ρ)) σ ∧
      IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ (D.dsig ρ) := by
  obtain ⟨H, i1, i2, σ, hσ⟩ := hex
  haveI : CompleteSpace H := hσ.1
  obtain ⟨d, hd0, hdI⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ σ hσ
  have hc : (0 : ℝ) < (D.s.cdScale _ (epsSH D.R) : ℝ) := D.s.cdScale_pos _ _
  have hF : IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ
      (d / (D.s.cdScale _ (epsSH D.R) : ℝ)) := by
    refine ⟨div_pos hd0 hc, fun v w v' w' => ⟨(hdI v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
    rw [MeasureTheory.integral_smul_measure, (hdI v w v' w').2, ENNReal.coe_toReal]
    have hc' : ((D.s.cdScale _ (epsSH D.R) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hd' : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [Complex.real_smul]
    push_cast
    field_simp
  have key := hd ρ H σ _ hσ hF
  refine ⟨H, i1, i2, σ, hσ, ?_⟩
  rw [← key]
  exact hF

end PI.UnitaryGroupMassFormula.HCFdegRGap
