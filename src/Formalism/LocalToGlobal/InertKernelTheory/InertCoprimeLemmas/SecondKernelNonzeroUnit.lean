module

public import Formalism.LocalToGlobal.InertKernelTheory.K2OfAgreements
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.IntermediateMapWittQuadratic
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

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.K2

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem p_ne_zero_Kf (Y : Pend X) : (p : X.G.Kf) ≠ 0 := by
  intro h
  have h1 : algebraMap (K0 p) Y.Kc (p : K0 p) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap X.G.Kf Y.Kc), h, map_zero]
  rw [map_eq_zero_iff _ (algebraMap (K0 p) Y.Kc).injective] at h1
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1

theorem eS_ne_zero (Y : Pend X) (j : ℕ) (La : X.Lt j) : Y.eS j La ≠ 0 := by
  unfold Pend.eS
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (p_ne_zero_Kf Y)

theorem eT_ne_zero (Y : Pend X) (j : ℕ) (La' : X.Lt (j + 1)) : Y.eT j La' ≠ 0 := by
  unfold Pend.eT
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (p_ne_zero_Kf Y)

theorem kernel_of_smul : KerOfSmul := by
  intro p _ X Y j La La' f h G
  have hne : Y.eS j La * (Y.eT j La')⁻¹ ≠ 0 :=
    mul_ne_zero (eS_ne_zero Y j La) (inv_ne_zero (eT_ne_zero Y j La'))
  unfold Pend.ker Pend.kerF
  rw [h, map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem ker_zero (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : Y.ker j La La' 0 = 0 := by
  simp only [Pend.ker, Pend.kerF, map_zero, LinearMap.zero_apply, smul_zero]

theorem ker_add (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (G1 G2 : (X.Pj j).Xsp) :
    Y.ker j La La' (G1 + G2) = Y.ker j La La' G1 + Y.ker j La La' G2 := by
  simp only [Pend.ker, Pend.kerF, map_add (f := _), LinearMap.add_apply, smul_add]

theorem ker_smul (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (a : X.G.Kf) (G : (X.Pj j).Xsp) :
    Y.ker j La La' (a • G) = a • Y.ker j La La' G := by
  simp only [Pend.ker, Pend.kerF, map_smul, LinearMap.smul_apply]
  rw [smul_smul, smul_smul, mul_comm]

theorem map_smul_Kf (Y : Pend X) {σ : Type} (a : X.G.Kf) (P : MvPolynomial σ X.G.Kf) :
    MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (a • P) = a • MvPolynomial.map (algebraMap X.G.Kf Y.Kc) P := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, algebraMap_smul]

theorem body_of_span (Y : Pend X) (j : ℕ) (cK : Y.Kc) (S : Set (X.Fm j))
    (hS : ∀ F ∈ S, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2))
    (F : X.Fm j) (hF : F ∈ Submodule.span X.G.Kf S) :
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2) := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    intro c' L' _
    simp only [map_zero, Pi.zero_apply, ker_zero, smul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    intro c' L' hL
    simp only [map_add (f := _), Pi.add_apply, ker_add, smul_add, Finset.sum_add_distrib, hx c' L' hL, hy c' L' hL]
  | smul a x _ hx =>
    intro c' L' hL
    simp only [map_smul, Pi.smul_apply, ker_smul]
    rw [map_smul_Kf Y, hx c' L' hL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun La _ => ?_
    rw [smul_comm]

section Rec

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

theorem sharpQ_qOf {t : KerEntTied ex} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {i : ℕ}
    {x : ((Tw.fm u μ).lat i).V} (h : ∃ Q, SharpQ t Tw u μ i x Q) : SharpQ t Tw u μ i x (qOf t Tw u μ i x) := by
  unfold qOf
  rw [dite_eq_left h]
  exact Classical.choose_spec h

end Rec

end Formalism.L2.KerInert.K2
