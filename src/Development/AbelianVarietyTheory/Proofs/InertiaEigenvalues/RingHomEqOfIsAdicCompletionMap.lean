module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem ringHom_eq_of_isCompl (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C]
    (i : L →+* Q) (J : Ideal L) (JC : Ideal C) (hc : IsCompl i J) (hH : IsHausdorff JC C)
    (h h' : Q →+* C) (hJ : J.map (h.comp i) ≤ JC) (he : h.comp i = h'.comp i) : h = h' := by
  have mem : ∀ (g : Q →+* C), J.map (g.comp i) ≤ JC → ∀ (n : ℕ) (y : Q), y ∈ (J ^ n).map i → g y ∈ JC ^ n := by
    intro g hg n y hy
    have h1 : g y ∈ ((J ^ n).map i).map g := Ideal.mem_map_of_mem g hy
    rw [Ideal.map_map, Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hg n h1
  have hJ' : J.map (h'.comp i) ≤ JC := by rwa [← he]
  ext x
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  obtain ⟨a, ha⟩ := hc.surj x n
  have e1 : h x - h' x = h (x - i a) - h' (x - i a) := by
    have : h (i a) = h' (i a) := RingHom.congr_fun he a
    simp only [map_sub, this]; ring
  rw [SModEq.zero, e1, smul_eq_mul, Ideal.mul_top]
  exact Ideal.sub_mem _ (mem h hJ n _ ha) (mem h' hJ' n _ ha)

end GlobalTheory.BSP
