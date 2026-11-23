module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurCoreA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClmEqZeroOfSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CplxNF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeviTens
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SubOneMulVecFix
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
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

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem schurNFC_of (hA : SchurCoreA) (hB : GeomB) : SchurNFC := by
  intro D X u u' Λ Λ' q hdiff hrel hG P hP
  obtain ⟨C, hC, hM⟩ := hB D X u u' Λ Λ' q hrel hG
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  refine hA D.R.k (InfinitePlace X.B.I.F) (X.Vloc u) (X.Vloc u') (X.Vpi u) (X.Vpi u') (X.tensU u) (X.tensU u')
    (X.tensU_inner u) (X.tensU_span u) (X.tensU_inner u') (X.tensU_span u') (X.piLoc u) (X.piLoc u')
    (fun v i => ((D.hcW u (X.pl v)).u i : ℝ)) (fun v i => ((D.hcW u' (X.pl v)).u i : ℝ))
    (fun v => X.piLoc_type u v) (fun v => X.piLoc_type u' v) v₀ (hdiff (X.pl v₀)) C hC P ?_
  intro M hMu
  obtain ⟨h, hh, h1, h2⟩ := hM M hMu
  exact ⟨X.piU u h, X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1), h1, h2, hP h hh⟩

end PI.SchurPlaces

theorem schurNFC : Formalism.L2.SG.KappaOffDiagonal.SchurNFC :=
  PI.SchurPlaces.schurNFC_of (PI.SchurPlaces.schurCoreA_of Formalism.MainNotions.BridgeLemma.schur_lemma_unitary_distinct_params)
    (PI.SchurPlaces.Geo.geomB_of PI.SchurPlaces.leviTens PI.SchurPlaces.wfrSpan PI.SchurPlaces.cplxNF)
