module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.IfaceSt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.ParEpsQOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapStep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportInt

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

def NVStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ),
    1 ≤ k → IsHCPar (parLam k r v b) → Interlaces k r u v b → HalfInts k r u v b → LowGaps r b h →
    GapLap (parEps k r) (parLam k r v b) h → BesselAll (parEps k r) (parLam k r v b) u

theorem nv_of (hI : Base.StepIBaseStatement) (hS : StepStatement) (hIS : S0.IntSStatement)
    (hDD : DecDerivStatement) : NVStatement := by
  intro k r u v b h hk hHC hIL hHalf hLow hGap
  have hp := parEps_pOf k r hk
  have hq := parEps_qOf k r hk
  have hSG : StepGap (parEps k r) r h := by
    have := gapLap_stepGap _ (parEps k r) (parLam k r v b) h (by rw [hp]; omega) (by rw [hq]; omega) hGap
    rwa [hq, Nat.add_sub_cancel] at this
  obtain ⟨t₀, ht⟩ := hI k r u v b hk hHC hIL hHalf
  exact TransportInt.transport_of hIS hDD hk hGap
    (walkStep hIS hS k r u v b h t₀ hk hHC hIL hHalf hLow hSG (ht t₀ le_rfl))

end ReciprocityTheory.ChartRestriction.DS.Lap
