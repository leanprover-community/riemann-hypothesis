module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

section ColCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full
open Matrix

def NStrongApproxC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized →
    ∀ n ∈ X.NfinU u, ∀ c : X.B.I.Gf, ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧
      c⁻¹ * ((ν.2)⁻¹ * n) * c ∈ X.K2

theorem hfin_le_sfinU {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (x : X.B.I.Gf)
    (hx : x ∈ Hfin X u) : x ∈ SfinU X u := by
  refine ⟨fun a => ?_, ?_⟩
  · have h1 : X.B.I.fmat x *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a) =
        Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a) := hx (X.eR a) (Or.inl (Or.inl ⟨a, rfl⟩))
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]
    exact Submodule.zero_mem _
  · have h1 : X.B.I.fmat x *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u) =
        Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u) := hx (X.zR u) (Or.inr rfl)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]
    exact Submodule.zero_mem _

theorem colCoverC_of (hSA : NStrongApproxC) : ColCoverC := by
  intro D X Y u u' hH ρ δ hδ hdec
  obtain ⟨n, h, k, hn, hk, hy⟩ := hdec
  obtain ⟨ρ', ⟨γ0, κ, hh⟩, -⟩ := Y.colReps u' h
  have hK := Y.hK
  have hγ := Subgroup.mem_inf.mp γ0.2
  have hγp := Subgroup.mem_prod.mp hγ.2
  have hh' : (h : X.B.I.Gf) = (γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) *
      ((κ : Hfin X u') : X.B.I.Gf) := by
    rw [hh]
    rfl
  have hκ : (X.xu u')⁻¹ * ((κ : Hfin X u') : X.B.I.Gf) * X.xu u' ∈ X.K2 := κ.2
  obtain ⟨ν, hν, hν1, hν2, hνk⟩ := hSA D X u' hK hH.1 n hn
    ((γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')
  have hd2 := eq_mul_inv_of_mul_eq hy
  refine ⟨ρ', δ⁻¹ * ν * (γ0 : X.B.I.GA), ⟨?_, ?_⟩, ?_⟩
  · exact mul_mem (mul_mem (inv_mem hδ) hν) hγ.1
  · show (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (δ⁻¹ * ν * (γ0 : X.B.I.GA)).2 *
        (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2
    have hT : (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (δ⁻¹ * ν * (γ0 : X.B.I.GA)).2 *
        (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') =
        k⁻¹ * ((X.xu u')⁻¹ * ((κ : Hfin X u') : X.B.I.Gf) * X.xu u')⁻¹ *
          (((γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * (ν.2⁻¹ * n) *
            ((γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u'))⁻¹ := by
      simp only [Prod.snd_mul, Prod.snd_inv]
      rw [hd2, hh']
      simp only [aC]
      group
    rw [hT]
    exact hK.2.1 _ (hK.2.1 _ (hK.2.2.1 _ hk) _ (hK.2.2.1 _ hκ)) _ (hK.2.2.1 _ hνk)
  · have hcancel : δ * (δ⁻¹ * ν * (γ0 : X.B.I.GA)) = ν * (γ0 : X.B.I.GA) := by group
    rw [hcancel]
    refine Subgroup.mem_inf.mpr ⟨mul_mem hν hγ.1, mul_mem ?_ ?_⟩
    · exact Subgroup.subset_closure ⟨fun v => (hν1 v).1, ⟨hν2.1, hν2.2.1⟩⟩
    · exact Subgroup.subset_closure ⟨hinf_le_sinf X u' _ hγp.1, hfin_le_sfinU X u' _ hγp.2⟩

end ColCoverPf

end Formalism.L2.SG.Pf.RegroupPf
