module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PiMapMulRight
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory.MuNPi

open Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem muN_eq_pi_muNl : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word),
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (fun v => muNl C (X.pl v) v) := by
  intro D X θ C u
  have hloc : ∀ v, QPK.InvOn (muNl C (X.pl v) v) (NGv X u v : Set _) := by
    have h : ∀ τ w, vOf X τ = w → QPK.InvOn (muNl C τ w) (NGv X u w : Set _) := by
      rintro τ _ rfl
      exact invOn_muNl C u τ
    exact fun v => h (X.pl v) v (X.pl.symm_apply_apply v)
  haveI : ∀ v, SigmaFinite (muNl C (X.pl v) v) := fun v => (hloc v).1
  obtain ⟨hσ, h0, hc, hi⟩ := X.muN_haar u
  haveI := hσ
  rw [← NinfG_coe] at hc hi
  refine PiM.uniq_on_closed (NinfG X u) (NinfG_closed X u) _ _ hc ?_ hi ?_ h0 ?_
  · rw [NinfG, Subgroup.coe_pi]
    exact PiM.pi_conc _ _ fun v => (hloc v).2.2.1
  · intro g hg
    exact PiM.pi_map_mul_left _ g fun v => (hloc v).2.2.2 (g v) (hg v (Set.mem_univ v))
  · exact PiM.pi_ne_zero _ fun v => (hloc v).2.1

end GlobalTheory.MuNPi
