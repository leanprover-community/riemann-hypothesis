module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.UpLatLoc0Of
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.DnIncInt0Of
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.DnLatKer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.IntInvOfLoc
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

open NumberField Ideal Matrix IsDedekindDomain

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Host Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.UG

variable {D : D7} {u : D.what₂.Word}

theorem dnLatLoc0_of_away (T : Forms0 D u) (hA : AwayLat0 T) : DnLatLoc0 T := by
  intro w hw hs v c g hg γ η κ hη hy hP B B' B₂ hB hB' hB₂ τ
  split_ifs with hτ
  · subst hτ
    have hk := lk_locP T.atT T.cls0 v c
    refine intInv_of_loc T.atT w hw hs v B₂ B' γ.1 hB₂ hB' ?_ ?_
    · rw [hP, ← hk]
      exact le_locP' _ _
    · rw [hk, ← hP]
      exact le_locP' _ _
  · obtain ⟨v', rfl⟩ : ∃ v', (D.fm u).tauOf w v' = τ := ⟨((D.fm u).tauOf w).symm τ, by simp⟩
    have hv' : v' ≠ v := fun h => hτ (h ▸ rfl)
    have hA' := hA v v' hv' c ((D.fm u).dn 0 v c g) γ η κ hη hy
    refine intInv_of_loc T.atT w hw hs v' B₂ B γ.1 hB₂ hB ?_ ?_
    · rw [hA']
      exact le_locP' _ _
    · rw [← hA']
      exact le_locP' _ _

end PI.UnitaryGroupMassFormula.IAT

end
