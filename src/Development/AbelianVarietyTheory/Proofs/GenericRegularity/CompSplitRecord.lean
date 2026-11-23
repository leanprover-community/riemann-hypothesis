module

public import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspRestrictComp
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
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
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg




theorem compSplit_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (hG : GenFrEx (T.Q.Xo j) T.Q.c), CompSplitSt h j hG := by
  intro D T h j hj hG Z w g
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  have hg : (g : T.R j) ∈ T.C j w := cutR_le T.C j w g.2
  obtain ⟨g', hg', h1, h0⟩ := exists_cusp_restrict_comp _ _ _ _ (T.Q.Xo j) T.Q.c hL hG (hA hG) _
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (fun σ hσ => h.unf j hj σ hσ) Z (wtA w) w.n (g : T.R j) hg
  have hm : g' ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]; exact hg'
  exact ⟨⟨g', hm⟩, h1, h0⟩

end GlobalTheory.Reg
