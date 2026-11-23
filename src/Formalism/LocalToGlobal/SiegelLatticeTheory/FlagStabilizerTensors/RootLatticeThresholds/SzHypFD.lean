module

public import Formalism.LocalRingCardinality.DataTies
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound
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

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

namespace Formalism.L2.SG.Pf.SzHypFD

variable {D : D7}

def DsigHC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → 1 ≤ Cl * large₂.sc.L →
    ∀ τ : D.what₂.Tau, D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ))

theorem dsig_eq [hF : Fact DsigHC] {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) :
    D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := hF.out D large₂ C' Cl Cg cb Cu cT CT hT hH hCL τ


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem vv_eq_vand {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by
  have hanti := Formalism.MainNotions.BridgeLemma.szh_anti hH τ
  have hSF : (0 : ℝ) < ∏ i ∈ range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [dsig_eq hT hH hCL τ, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← dimS_eq]
  field_simp


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem fdl_of_ties {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) :
    Sz.FormalDegreeLower (Formalism.MainNotions.BridgeLemma.cfgOf D τ) (1 / 2) (VV D τ) := by
  unfold Sz.FormalDegreeLower
  rw [Formalism.MainNotions.BridgeLemma.Vand_lam D τ, vv_eq_vand hT hH hCL τ]
  have h0 : 0 ≤ vand (lamSH D.R (D.hc τ)) := Formalism.MainNotions.BridgeLemma.szh_vand_nonneg _ (Formalism.MainNotions.BridgeLemma.szh_anti hH τ)
  linarith

end Formalism.L2.SG.Pf.SzHypFD
