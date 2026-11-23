module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenvectorHasSumAdicCompleteFrobeniusStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSeriesAcrisUntiltStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem exists_acris_Lam : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (y : ℕ → Fl l), 2 ≤ h → (∀ k, ‖sh (y k)‖ ≤ ‖(l : ℂ_[l])‖) → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = abelian₂ h j y := by
  intro l _ h y hh hy
  choose w hw hθ using fun k => GlobalTheory.T.exists_frobeniusSeries_acris_untilt l h (y k) hh (hy k)
  haveI : IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := (GlobalTheory.MemLoc.acris_basic l).1
  obtain ⟨W, hW, hsum⟩ := GlobalTheory.T.exists_eigenvector_hasSum_adicComplete_frobenius l (Acris l) (GlobalTheory.MemLoc.phiA l) h w hw
  refine ⟨W, hW, fun Θ hΘ htm j => ?_⟩
  set φ := GlobalTheory.MemLoc.phiA l
  have hS := hsum (Θ.comp (φ ^ j)) (fun a => hΘ _)
  simp only [RingHom.coe_comp, RingHom.coe_pow, Function.comp_apply] at hS
  unfold abelian₂
  rw [← hS.tsum_eq]
  congr 1
  funext k
  rw [hθ k Θ hΘ htm j]

end GlobalTheory.PSer
