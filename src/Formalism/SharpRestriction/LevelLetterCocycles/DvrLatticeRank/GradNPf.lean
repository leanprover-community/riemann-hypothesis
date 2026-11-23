module

public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfA
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB
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

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem gradNCondition : Formalism.MainNotions.N.Ln34.GradNStep := by
  intro D HW F Cm CA CB CK hA l hlp hl K LL hG π' E hR T h' hh' hT
  have h1 : adm1 D HW F Cm := hA.1
  rcases Nat.eq_zero_or_pos (sK l K) with hs0 | hs
  ·
    apply gradNPf_small
    simp [MK, hs0]
  · obtain ⟨f, t, x, u, -, -, hf, ht, hE, hΔ, hγ, hK, hN⟩ :=
      gradNPf_hyps D HW F Cm h1 l hl K LL hG π' E hR T hT hs
    rcases le_or_gt (MK l K h') 1 with hM | hM
    · apply gradNPf_small
      exact hM
    · obtain ⟨a, ha⟩ := hN (MK l K h' - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ MK l K h')] at ha
      refine gradNPf_local (hf := hf) (ht := ht) (hu := hE) (hπΔ := hΔ) (hγN := hγ) (hK := hK)
        (hM := by omega) (a := a) (ha := ?_)
      convert ha using 2
      · rw [(D.loc l).PD_p K]
      · rfl

end Formalism.MainNotions.N.Ln34

end
