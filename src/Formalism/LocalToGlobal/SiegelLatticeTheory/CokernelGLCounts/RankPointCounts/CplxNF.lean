module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SpanAtMono
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplittingAdmissibleOfTermData
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Formalism.FlagUnipotentLattices.AutBoundOfMinkowskiBound

@[expose] public section

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nfRat : NFRat := by
  intro D X u u' Λ Λ' q hrel hG
  obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hpos : ∀ w : D.what₂.Word, 0 < (σ ((Tu D w : ℕ) : D.host.E)).re := by
    intro w
    rw [map_natCast, Complex.natCast_re]
    exact_mod_cast tie_Tu_pos D w
  obtain ⟨j, hj, c, hN⟩ := _root_.Formalism.HermitianLatticeCounting.P.existsNormalForm D.host.E (VS D).V σ (nfH (VS D)) D.R.rS
    (nfF (lf D (X.Fu u)).fl (nf_T_ne D u)) (nfF (frq X q).fl (nf_T_ne D u')) (fun x => p_starConj D σ x)
    (hpos u) (hpos u') (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ)
    (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u') _) σ)
    (nf_rel D.host.F (tie_trace D.sp.cm) _ _ _ _ hrel) ((nf_G _ _ _ _).trans hG)
  obtain ⟨-, -, -, -, ⟨h1, h2⟩, ⟨-, h3⟩⟩ := nf_gen _ _ _ _ j hj c hN
  exact ⟨h1, h2, h3⟩

theorem cplxNF : CplxNF := cplxNF_of nfRat

end PI.SchurPlaces
