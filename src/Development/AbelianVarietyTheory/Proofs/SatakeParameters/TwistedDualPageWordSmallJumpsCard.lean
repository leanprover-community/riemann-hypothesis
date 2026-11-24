module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardSmallTwistedDualJumpsEqRankStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CloudLowJumpsReflectAndCardStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem twistedDualPageWord_small_jumps_card : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T2 ∧ ∀ i, ((pageWord L j ε τ φ).J2 i).card = D.R.r ∧ (((pageWord L j ε τ φ).J2 i).filter fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
  intro D L C j ε τ φ hR
  have hbox := (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR).2.2.2.2.2
  have hcount : ∀ i, (((pageWord L j ε τ φ).J2 i).filter
      fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
    intro i
    refine GlobalTheory.T.card_filter_abs_le_jT2_eq_rank (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) L.etaSz ?_ ?_ (hbox i)
    · intro a
      have h := (L.cloud_v (D.eTau.symm ⟨plc (letter τ φ i), plc_mem _⟩) a).1
      exact_mod_cast h
    · intro a
      exact L.be_close _ a j
  refine ⟨fun i => ⟨fun u hu => ?_, (hcount i).le⟩, fun i => ⟨?_, hcount i⟩⟩
  · exact Multiset.mem_of_le
      ((GlobalTheory.T.cloudLowJumps_reflect_and_card (hcAt D (letter τ φ i)) j).2 (pos ε (letter τ φ i))).2.2.2 hu
  · exact ((GlobalTheory.T.cloudLowJumps_reflect_and_card (hcAt D (letter τ φ i)) j).2 (pos ε (letter τ φ i))).2.2.1

end GlobalTheory.HTW
