module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.LiftBoundOfHypotheses
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CardLinkIdxMulLe
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.ExistsOfMemSupportLin
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.OmegaValue
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.PrimedEmbeddingInjective
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.RenamePullLCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutedExponentApplyBlock
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SumOnLetterApplyInl
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.TestBoundOfRhoAndNormSets
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem plane_gram_theorem_of_five_lemmas (h1 : 1 ≤ C0) (hV2 : V2 K) (hSPAN : SPAN K v p) (hPROJ : PROJ K v p C0)
    (hDIG : DIG K v p) (hDER : DER K v p) : LiftBoundUniform K v p C0 :=
  plane_gram_theorem_of_combined_lemmas h1 (stepBC_of (stepB_of h1 hV2 hPROJ) (stepC_of hV2 (segStep_of hSPAN)))
    (stepDEF_of h1 hDIG (stepG_of hV2) (stepP_of v p C0 h1 hPROJ) (stepE_of v p hV2 hDER))

end Formalism.MainNotions.PlaneGram
