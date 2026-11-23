module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSplitPointAtPlaceOverSplitStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsProdSinglePlacePiecesOfSuppAtStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemFourierJacobiGroupOfSumFrameSymmetricStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowLift
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem inBasis_congr {D : D7} {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    {x y : GL (Fin n) (Lev.EAf D)} (e : GlobalTheory.StdFrames.loc w x = GlobalTheory.StdFrames.loc w y) : inBasis h β w x = inBasis h β w y := by
  simp only [inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, e]

theorem mem_jacGrp_of_hasLoc : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t j σ, j ∈ idx D → ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m) (hσ : D.R.m - 1 - j = 2 * σ),
    1 ≤ σ → ∀ (r : GA D (ch.G.V (.grid D.R.m j))) (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj r g → (∀ w, g w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
    r ∈ jacGrp (rowJac ch.G j hj' σ hσ) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t j σ hi hj hj' hσ h1 r g hr hg
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, hc⟩, hsupp, hloc⟩ := hr
  obtain ⟨h, hh1, hh2, hr⟩ := GlobalTheory.T.exists_prod_single_place_pieces_of_suppAt _ _ es hes hc r hsupp
  rw [hr]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨q, hqe, -, hqpr⟩ := GlobalTheory.T.exists_cmSplitPoint_at_place_over_split D w.1 (es w.1) (hes w.1 w.2) s.hF
  have hF := ch.S.row t (Set.mem_univ t) w.1 w.2 j hj'
  have e1 : GlobalTheory.StdFrames.loc w.1 (Lev.finE (ch.G.V (.grid D.R.m j)) (h w)) =
      GlobalTheory.StdFrames.loc w.1 (Lev.finE (ch.G.V (.grid D.R.m j)) r) := Units.ext (hh2 w)
  have hm : toFrame one_le_sLen hj' (g w) ∈ symR (Kw w.1) _ _ := hg w
  rw [← hloc w] at hm
  refine GlobalTheory.T.rowTest_mem_fourierJacobiGroup_of_sumFrame_symmetric (ch.G.rowDec j hj') hσ h1 w.1 _ _ _ hF (fun p => frameScal_ne w.1 _ _ p) (topRank_eq ch.G t w.1 hj)
    (rank_vertex ch.G t w.1 (X := (D.R.m, j)) ⟨le_rfl, hj⟩)
    (by have := topRank_add (G := locGrid ch.G t w.1) one_le_sLen j; have hm' : (locGrid ch.G t w.1).m = D.R.m := rfl; rw [hm'] at this; omega)
    q (fun x => (hqpr x).trans rfl) (h w) (hqe ▸ hh1 w) ?_
  rw [inBasis_congr _ _ _ e1]
  exact hm

end GlobalTheory.RowLift
