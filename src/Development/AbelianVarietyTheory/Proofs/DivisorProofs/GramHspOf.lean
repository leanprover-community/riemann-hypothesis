module

public import Formalism.LocalRingCardinality.DataTheta
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField

namespace GlobalTheory.WeilSchrodinger

variable (D : D7)

def sesq {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) :
    (Fin k → D.host.E) →ₗ⋆[D.host.E] (Fin k → D.host.E) →ₗ[D.host.E] D.host.E :=
  Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) G

def hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm) (nd : (sesq D G).Nondegenerate)
    (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D where
  V := Fin k → D.host.E
  hT := sesq D G
  herm := herm
  nondeg := nd
  rank := k
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := sg
  L0 := L
  standardTuple_isLattice := hL
  baseLattice_isUnimodular := hU

variable {D}

theorem gram_hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm)
    (nd : (sesq D G).Nondegenerate) (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) :
    (hspOf D G herm nd L hL hU sg).gram = G := by
  funext i j
  have e : ∀ m : Fin k, Pi.basisFun D.host.E (Fin k) m = Pi.single m 1 := fun m => Pi.basisFun_apply _ _ m
  simp only [HSpace.gram, hspOf, sesq]
  erw [e i, e j]
  exact Matrix.toLinearMapₛₗ₂'_single (R := D.host.E) (starRingEnd D.host.E) (RingHom.id D.host.E) G i j

end GlobalTheory.WeilSchrodinger

end
