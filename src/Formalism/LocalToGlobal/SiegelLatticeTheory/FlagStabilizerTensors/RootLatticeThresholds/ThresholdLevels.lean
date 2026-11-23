module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdAtPlaceBounds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdOrder
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

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.ThresholdLevels

variable (C0 : ℝ)

theorem thrRow_holds {𝒞 : FamClass} : ∀ CA : ℝ, 1 ≤ CA → Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
    AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
      ∀ u u' : (Fm.D x i).what₂.Word, u ≠ u' → Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces CA (Fm.D x i) u u' := by
  intro CA hCA

  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 40⟩, fun Fm CH _ hL => ?_⟩⟩
  have h40 : (40 : ℝ) ≤ sCl Fm := (le_sC'_sCl hL).2
  refine ⟨0, fun x _ i hH u u' _ => ?_⟩
  obtain ⟨hD, hHy, _⟩ := hH
  exact ThresholdOrder.thrAt_of_pos CA (Fm.D x i) u u' (ThresholdAtPlaceBounds.thrSet_pos_at hD hHy h40 _ hCA u u')

end Formalism.L2.SG.Pf.ThresholdLevels
