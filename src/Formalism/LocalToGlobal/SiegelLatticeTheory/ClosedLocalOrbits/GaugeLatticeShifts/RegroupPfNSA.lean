module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfColCover
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions

section NSAPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NDense : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : X.B.I.Gf), n ∈ X.NfinU u →
    ∀ U : Set X.B.I.Gf, IsOpen U → n ∈ U →
      ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧ ν.2 ∈ U

theorem nStrongApproxC_of (hD : NDense) : NStrongApproxC := by
  intro D X u hK hKL n hn c
  have hcl := Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen X hK hKL
  have hc : Continuous fun m : X.B.I.Gf => c⁻¹ * (m⁻¹ * n) * c :=
    (continuous_const.mul (continuous_inv.mul continuous_const)).mul continuous_const
  obtain ⟨ν, hνr, hν1, hν2, hνU⟩ := hD D X u n hn {m | c⁻¹ * (m⁻¹ * n) * c ∈ X.K2} (hcl.2.preimage hc)
    (by simpa using hK.1)
  exact ⟨ν, hνr, hν1, hν2, hνU⟩

end NSAPf

end Formalism.L2.SG.Pf.RegroupPf
