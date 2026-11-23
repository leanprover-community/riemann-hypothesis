module

public import Formalism.SharpRestriction.LevelLetterCocycles.MixedPositionHypothesis
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

theorem uniformiser_ring_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) : p9R D HW := by
  unfold adm1 Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeGlobal Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeLocal at h1
  intro l _ hl K LL hG T hT
  have h9 := (h1 l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT
  unfold Formalism.MainNotions.DeltaInvariantLattices.p9 at h9
  have hpe : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs : ((HW l).W K 1 LL hG).s = 1 := by
    first
    | exact (HW l).W_s K 1 LL hG
    | exact (HW l).hs K 1 LL hG
    | exact (HW l).s_eq K 1 LL hG
    | exact (HW l).W_s
    | rfl
  obtain ⟨-, ⟨π', E, hr, -⟩, -⟩ := h9 hs (by rw [hpe]; exact hl)
  refine ⟨π', E, ?_⟩
  convert hr using 2 <;> first | rfl | (simp only [eK, sK, hpe]) | (unfold eK sK; simp [hpe])

end Formalism.MainNotions.N.Ln34

end
