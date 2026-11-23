module

public import GroundTheory.ProfiniteCohomology.PoitouTate.RealTrace
import GroundTheory.ProfiniteCohomology.TorsionDualFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (N : ℕ) [NeZero N] [Fintype S]

theorem exists_gsTraceQZ :
    ∃ χ : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ QZ,
      χ.comp (ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom.toAddMonoidHom =
        gsSumInvReal S ιr ιs N :=
  QZ.exists_comp_eq_of_ker_le _ _ fun ξ hξ => gsSumInvReal_eq_zero_of S ιr ιs N ξ hξ

def gsTraceQZ : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ QZ :=
  Classical.choose (exists_gsTraceQZ S ιr ιs N)

theorem gsTraceQZ_comp :
    (gsTraceQZ S ιr ιs N).comp
        (ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom.toAddMonoidHom =
      gsSumInvReal S ιr ιs N :=
  Classical.choose_spec (exists_gsTraceQZ S ιr ιs N)

theorem nsmul_gsTraceQZ
    (z : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3) :
    N • gsTraceQZ S ιr ιs N z = 0 :=
  (map_nsmul (gsTraceQZ S ιr ιs N) N z).symm.trans
    ((congrArg (gsTraceQZ S ιr ιs N) (nsmul_tateCompactCohomologyRes_eq_zero (gsFinFamily S ιs)
      (gsRealFamily S ιr) (nsmul_gsRoots S N) 3 z)).trans (map_zero _))

def gsTrace : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N :=
  zmodOfQZ (gsTraceQZ S ιr ιs N) (nsmul_gsTraceQZ S ιr ιs N)

theorem gsTrace_localToCompact (ξ : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2) :
    zmodToQZ N (gsTrace S ιr ιs N
      ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ)) =
      ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w) :=
  (zmodToQZ_zmodOfQZ _ _ _).trans (DFunLike.congr_fun (gsTraceQZ_comp S ιr ιs N) ξ)

end GroundTheory.ProfCoh
