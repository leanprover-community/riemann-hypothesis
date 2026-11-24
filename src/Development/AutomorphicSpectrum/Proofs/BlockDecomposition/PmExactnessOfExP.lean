module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

theorem cech_d_eq_dZ (P : PM.{0} R ι) (n : ℕ) (c : P.cech.X n) :
    P.cech.d n c = dZ P.M (fun h x => P.res h x) n c := by
  funext i
  simp only [CrystallineSemistableComparison.Cos.d, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, dZ]
  rfl

theorem cech_d_aug (P : PM.{0} R ι) (x : P.M ∅) : P.cech.d 0 (P.aug x) = 0 := by
  rw [cech_d_eq_dZ]
  funext i
  have key : ∀ (k : Fin 2), P.res (ent_comp i k.succAbove) (P.aug x (i ∘ k.succAbove)) =
      P.res (Finset.empty_subset (ent i)) x := fun k => P.res_comp _ _ x
  simp only [dZ, Fin.sum_univ_two, key]
  simp
  rfl

theorem ex_of_exP : ∀ {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] (P : PM.{0} R ι),
    ExP P.M (fun h x => P.res h x) → P.Ex := by
  intro R _ ι _ P h
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨cech_d_aug P, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · rw [one_smul]
    exact h0 x fun i => congrFun hx i
  · obtain ⟨x, hx⟩ := h1 y ((cech_d_eq_dZ P 0 y).symm.trans hy)
    exact ⟨x, (funext hx).trans (one_smul _ _).symm⟩
  · obtain ⟨b, hb⟩ := h2 n y ((cech_d_eq_dZ P (n + 1) y).symm.trans hy)
    exact ⟨b, ((cech_d_eq_dZ P n b).trans hb).trans (one_smul _ _).symm⟩

end GlobalTheory.CompanionTheory.SurjectionOntoH4
