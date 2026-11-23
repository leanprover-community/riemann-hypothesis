module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormUniformiserEqInvAbsNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplit
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem nvOK_nvL : ∀ (D : D7) (v : Pl D) (ϖ : Ov D v), Irreducible ϖ → ∀ w : (Lv D v)ˣ,
    (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → NvOK (O := Ov D v) (nvL D v) w := by
  intro D v ϖ hϖ w hw
  have hu1 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ϖ) := by
    unfold Formalism.UG.IsUnifV
    rw [GlobalTheory.SplitDetValue.valued_irreducible v hϖ] <;> rfl
  have hn : ‖algebraMap (Ov D v) (Lv D v) ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ :=
    GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu1
  have hc : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ ≠ 0 := by
    rw [Ne, inv_eq_zero, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  unfold NvOK
  refine ⟨fun u => ?_, ?_⟩
  · show ‖algebraMap (Ov D v) (Lv D v) (u : Ov D v)‖₊ = 1
    have hu2 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ((u : Ov D v) * ϖ)) := by
      unfold Formalism.UG.IsUnifV
      rw [map_mul, map_mul, GlobalTheory.SplitDetValue.valued_unit v u, GlobalTheory.SplitDetValue.valued_irreducible v hϖ,
        one_mul] <;> rfl
    have h2 := GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu2
    rw [map_mul, nnnorm_mul, hn] at h2
    exact (mul_eq_right₀ hc).mp h2
  · show ‖(w : Lv D v)‖₊ = _
    rw [hw, hn, Fintype.card_eq_nat_card, GlobalTheory.SplitDetValue.card_residue_eq]

end GlobalTheory.CompanionTheory.Jp
