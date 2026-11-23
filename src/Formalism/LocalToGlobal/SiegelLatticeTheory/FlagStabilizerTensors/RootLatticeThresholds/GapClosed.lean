module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSGap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk

namespace Formalism.L2.SG.GapClosed

theorem gapEv_closed_of (𝒞 : FamClass) (hT : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) :
    Closed 𝒞 fun Fm _ => 𝒞 Fm → Formalism.L2.SG.LoopsTies.GapEv Fm := by
  obtain ⟨e, he, H⟩ := Formalism.L2.SG.ThmSOwn.gapRowT (𝒞 := 𝒞) (Formalism.L2.SG.ResidEvFree.residEv_closed_free 𝒞)
  refine ⟨e, he, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := H eps h1 h2
  exact ⟨K, fun Fm CH hc hL _ => hK Fm CH ⟨hc, hT Fm hc⟩ hL ⟨hc, hT Fm hc⟩⟩

end Formalism.L2.SG.GapClosed

end
