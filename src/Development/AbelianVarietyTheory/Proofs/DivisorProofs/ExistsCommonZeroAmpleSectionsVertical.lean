module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleCodimOneZeroAmpleSectionFibreStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem GlobalTheory.HSAmp.common_zero_of_le_dim : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d : ℕ) (C : Set X) (e : Fin d → ℕ) (g : Fin d → X.functionField), ℓ.Prime → IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → (d : WithBot ℕ∞) ≤ topologicalKrullDim C → (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) → (C \ ⋃ j, NV P (e j) 0 (g j)).Nonempty := by
  intro k _ X _ p D hX P hA ℓ d
  induction d with
  | zero =>
    intro C e g hℓ hC hCc hCf hd hg
    obtain ⟨x, hx⟩ := hC.nonempty
    exact ⟨x, hx, by simp⟩
  | succ d ih =>
    intro C e g hℓ hC hCc hCf hd hg
    obtain ⟨C', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_irreducible_codim_one_zero_ample_section_fibre k X p D hX P hA ℓ d (e 0) C (g 0) hℓ hC hCc hCf
      (by exact_mod_cast hd) (hg 0).1 (hg 0).2
    obtain ⟨x, hxC', hx⟩ := ih C' (fun j => e j.succ) (fun j => g j.succ) hℓ h1 h2
      (h3.trans (Set.diff_subset.trans hCf)) h4 (fun j => hg j.succ)
    refine ⟨x, (h3 hxC').1, ?_⟩
    simp only [Set.mem_iUnion, not_exists] at hx ⊢
    intro j
    refine Fin.cases ?_ (fun j => hx j) j
    exact (h3 hxC').2
