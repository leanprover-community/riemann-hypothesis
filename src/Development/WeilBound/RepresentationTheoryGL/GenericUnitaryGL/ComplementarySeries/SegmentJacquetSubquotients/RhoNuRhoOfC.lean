module

import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.RhoNuRhoOfC
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.Published

namespace PositivityTheory.RgGu.NR

namespace RedC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irr_congr {h N : ℕ} {x x' : Fin h → IrrGL (k := k)} (e : x = x') (hd : ∑ a, (x a).1 = N) :
    ∃ hd' : ∑ a, (x' a).1 = N, ((prodIrr x hd).IsIrreducible ↔ (prodIrr x' hd').IsIrreducible) := by
  subst e
  exact ⟨hd, Iff.rfl⟩

theorem irr_tw {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (s : ℂ)
    (hi : (prodIrr x hd).IsIrreducible) : (prodIrr (fun a => (x a).nu s) hd).IsIrreducible :=
  GlobalTheory.Parabolic.isIrreducible_of_equiv (prodIrrTwistEquiv x hd (absPow k s) (isSmoothChar_absPow s))
    (isIrreducible_twist hi _)

end RedC

open RedC in

theorem redCl_ofC (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : SomeRed k) (h2 : CuspUnit k) (h3 : GlobalTheory.BZSeg.CuspPairIrr k) : RedCl k := by
  apply CompanionTheory.RgGu.NR.redCl_ofC <;> assumption

theorem rhoNuRho_ofC (h : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    RedCl k) : PositivityTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := by
  intro k _ _ _ _ d hd σ hσ hirr
  set y : IrrGL (k := k) := IrrGL.of σ.ρ σ.smooth σ.irr with hy
  have hyc : y.IsCusp := IrrGL.isCusp_of.2 ⟨hd, hσ⟩
  let x : Fin 2 → IrrGL (k := k) := fun a => y.nu ((a : ℕ) : ℂ)
  have hx1 : ∀ a, (x a).1 = d := fun _ => rfl
  have hdx : ∑ a, (x a).1 = 2 * d := by
    simp only [hx1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  let φ : ∀ a : Fin 2, (segTerm σ.ρ 2 a).Equiv (x a).rep := fun a =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) _).trans (y.twEquiv _ _)
  have E1 := multiProdEquiv (consecBlocks 2 d) φ
  have hdd : ∑ _a : Fin 2, d = 2 * d := by simp
  have hE : consecBlocks 2 d = stdBlocks (fun _ : Fin 2 => d) hdd := by
    ext ⟨a, i⟩
    rw [consecBlocks_val, stdBlocks_val]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have h3 : (prodIrr x hdx).IsIrreducible := by
    have h4 := GlobalTheory.Parabolic.isIrreducible_of_equiv E1 hirr
    rw [hE] at h4
    exact h4
  have e : x = ![y, y.nu 1] := by
    funext a
    fin_cases a
    · simp [x]
    · simp [x]
  obtain ⟨hd', hiff⟩ := RedC.irr_congr e hdx
  exact h k y hyc (2 * d) hd' (hiff.1 h3)

end PositivityTheory.RgGu.NR
