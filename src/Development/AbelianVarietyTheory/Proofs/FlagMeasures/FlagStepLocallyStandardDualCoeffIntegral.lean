module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIsotropicFlagMovesStepIntoPrevStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.MainNotions.S

namespace GlobalTheory.LocCoef

theorem h_es_eq_zero_of_mem_Fj {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type}
    [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r)
    (a : Fin r) (u : V) (hu : u ∈ Fr.Fj a.val) : H.h u (Fr.es a) = 0 := by
  unfold Formalism.MainNotions.S.LocNG.FrameD.Fj at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : b.val < a.val := hb
    have hba : b ≠ a := fun h => by subst h; exact lt_irrefl _ hb'
    unfold Formalism.MainNotions.S.LocNG.FrameD.e
    rw [Fr.h_es b a, if_neg hba]
  | zero => exact H.h_zero_left _
  | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

theorem h_es_mem_O_of_mem_LamStd {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type}
    [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r)
    (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) (w : V) (hw : w ∈ Fr.LamStd L) :
    H.h w (Fr.es a) ∈ M.L.O := by
  unfold Formalism.MainNotions.S.LocNG.FrameD.LamStd at hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx.1 a
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
  | smul c x _ hx =>
    have : H.h (c • x) (Fr.es a) = (c : E) * H.h x (Fr.es a) := H.h_smul_left (c : E) x _
    rw [this]; exact M.L.O.mul_mem c.2 hx

end GlobalTheory.LocCoef

theorem GlobalTheory.locCoef_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) (v : V), v ∈ Fr.Fj (a.val + 1) → v ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L) → H.h v (Fr.es a) ∈ M.L.O := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr n hn L a v hv hvimg
  unfold Formalism.MainNotions.S.LocNG.img at hvimg
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hvimg
  have hwv' : n w = v := hwv
  have hu := (GlobalTheory.T.unipotentRadical_isotropicFlag_moves_step_into_prev Fr n hn (a.val + 1) (Nat.succ_le_of_lt a.isLt) v hv).2
  simp only [Nat.add_sub_cancel] at hu
  have hsymm : n.symm v = w := by rw [← hwv']; exact n.symm_apply_apply w
  rw [hsymm] at hu
  have h0 := GlobalTheory.LocCoef.h_es_eq_zero_of_mem_Fj Fr a (w - v) hu
  have hwO := GlobalTheory.LocCoef.h_es_mem_O_of_mem_LamStd Fr L a w hw
  have hdecomp : H.h w (Fr.es a) = H.h (w - v) (Fr.es a) + H.h v (Fr.es a) := by
    rw [← H.h_add_left, sub_add_cancel]
  rw [hdecomp, h0, zero_add] at hwO
  exact hwO
