module

public import Formalism.PeriodIntegrals.WeylProd
public import Formalism.LocalToGlobal.Columns.Inputs
public import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylProd
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

theorem weylDim_of_weylProd (h : PI.WeylProd) {n : ℕ} (lam : DomWeight n) : WeylDim lam := by
  unfold WeylDim
  rw [Formalism.L2.G.Model.card_ssIdx]
  have hnn : ∀ t, ((lam.natW t : ℕ) : ℤ) = lam.w t - lam.detShift := by
    intro t
    unfold DomWeight.natW
    apply Int.toNat_of_nonneg
    unfold DomWeight.detShift
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) t.isLt
    rw [dite_eq_left hn]
    have h1 : t ≤ (⟨n - 1, by omega⟩ : Fin n) := by
      rw [Fin.le_def]
      have := t.isLt
      show t.val ≤ n - 1
      omega
    have := lam.anti h1
    omega
  have hanti : Antitone (fun t => ((lam.natW t : ℕ) : ℤ)) := by
    intro a b hab
    have := lam.anti hab
    simp only [hnn]
    omega
  have h1 := Formalism.L2.G.Model.weylQ n _ hanti
  have h2 : _ = Formalism.LogVandermondeBounds.StandardLattice.dimVN (wSeq lam) n := h n (fun t => ((lam.natW t : ℕ) : ℤ)) lam.w lam.detShift hnn
  rw [← h2, ← h1, Rat.cast_natCast]

theorem weylDim_holds {n : ℕ} (lam : DomWeight n) : WeylDim lam := weylDim_of_weylProd weyl_product_formula lam


open Finset Formalism.LogVandermondeBounds.StandardLattice

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)


end Formalism.L2.Col
