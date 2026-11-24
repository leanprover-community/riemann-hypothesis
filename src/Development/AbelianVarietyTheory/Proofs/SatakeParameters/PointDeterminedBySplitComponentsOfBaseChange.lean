module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicRepEqOfEqAtAlmostAllSplitPlacesStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.PtOfLocSplit

theorem eventually_splitOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    ∀ᶠ w in Filter.cofinite, IsSplitPl H w → SplitOut N i w := by
  have hl : (N.l i).Prime := Fact.out
  have hfin : (placesOver H.E (N.l i)).Finite := by
    have h0 : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ 0 := by simpa using hl.ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  filter_upwards [hfin.eventually_cofinite_notMem, (N.S i).eventually_cofinite_notMem,
    (N.Q i).eventually_cofinite_notMem] with w h1 h2 h3 hw using ⟨hw, h1, h2, h3⟩

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.PtOfLoc N A i := by
  intro R H what₂ N A i hBC hSp hRep P P' x hx hloc
  have hPP : P = P' := GlobalTheory.T.automorphicRep_eq_of_eq_at_almost_all_split_places R H what₂ N A i hBC hSp hRep P P' <| by
    filter_upwards [eventually_splitOut N i] with w hw hs using hloc w (hw hs)
  rw [hPP]; exact hx

end GlobalTheory.PtOfLocSplit
