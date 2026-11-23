module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalisedAdaptedVectorZero
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormalFrame0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExistG2OfStandardLattices
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi Formalism.IndefR.Seed.Frm IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VertexFromTransport

theorem vertexAt_of_levTransport : ∀ {D : D7} {T : Type} (L : LevCh D T), (∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP) →
    ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Transport L.Pg (Wc D i) (Yc D 0) (L.βW i) (L.βY 0) →
    ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (Formalism.IndefR.Lev.EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf L.βY 0) (L.βW i) eW ι L.Pg := by
  intro D T L _ i ht
  have hr : (D.sp.Y 0).rank = (D.sp.W ((i : ℕ) + 1)).rank := by
    rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.W_rank _ (by omega) (by omega)]
    simp [Ranks.rankY]
  exact GlobalTheory.NormalFramesLevels.vertexAt_of_transport L.Pg _ hr _ _
    (GlobalTheory.NormalFramesLevels.transport_betaYOf L.Pg (Wc D i) (L.βW i) L.βY ht)

end GlobalTheory.VertexFromTransport
