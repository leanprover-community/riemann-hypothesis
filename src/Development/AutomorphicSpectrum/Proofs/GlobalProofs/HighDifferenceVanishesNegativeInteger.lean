module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem coneTerm_differentiable_in_s_alt {ι : Type} [Fintype ι] {r : ℕ} {a : ι → Fin r → ℝ} {b : ι → ℝ}
    (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) (m : Fin r → ℕ) :
    Differentiable ℂ (fun s => coneTerm a b s m) := by
  unfold GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm
  refine Differentiable.fun_finsetProd fun j _ => ?_
  refine Differentiable.const_cpow differentiable_neg (Or.inl ?_)
  have hpos : 0 < b j + ∑ i, a j i * (m i : ℝ) :=
    add_pos_of_pos_of_nonneg (hb j)
      (Finset.sum_nonneg fun i _ => mul_nonneg (ha j i).le (Nat.cast_nonneg _))
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

theorem DL_coneTerm_differentiable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ),
    (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (cs : List (Fin r)) (m : Fin r → ℕ),
      Differentiable ℂ (fun s => DL cs (coneTerm a b s) m) := by
  intro ι _ r a b ha hb cs
  induction cs with
  | nil => intro m; exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_differentiable_in_s_alt ha hb m
  | cons c cs ih =>
    intro m
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL, List.foldr_cons, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.fd] at ih ⊢
    exact (ih (m + Pi.single c 1)).sub (ih m)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
