module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.SubFrame

theorem isFrameAt_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (q : Cpt ξ) (g n : ℕ) (b : Fin g → E) (ix : Fin n → Fin g), Function.Injective ix → LinearIndependent Ω b → L q = Submodule.span (regAt ξ q) (Set.range b) → V' = Submodule.span Ω (Set.range (b ∘ ix)) → (L.inter V').IsFrameAt (b ∘ ix) q := by
  intro X Ω _ ξ E _ _ L V' q g n b ix hix hb hL hV
  subst hV
  refine And.intro (hb.comp ix hix) ?_
  show L q ⊓ Submodule.restrictScalars (regAt ξ q) (Submodule.span Ω (Set.range (b ∘ ix))) = _
  rw [hL]
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have hx2' : x ∈ Submodule.span Ω (Set.range (b ∘ ix)) := hx2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx1
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hx2'
    have hc' : ∑ i, (c i : Ω) • b i = x := hc
    have hD : ∑ i, (∑ j, if ix j = i then d j else 0) • b i = x := by
      rw [← hd]
      simp only [Finset.sum_smul, ite_smul, zero_smul]
      rw [Finset.sum_comm]
      simp [Finset.sum_ite_eq]
    have key : ∀ i, (c i : Ω) = ∑ j, if ix j = i then d j else 0 := by
      have h0 := Fintype.linearIndependent_iff.1 hb
        (fun i => (c i : Ω) - ∑ j, if ix j = i then d j else 0) (by
          simp only [sub_smul, Finset.sum_sub_distrib]
          rw [hc', hD, sub_self])
      intro i
      exact sub_eq_zero.1 (h0 i)
    rw [← hc]
    apply Submodule.sum_mem
    intro i _
    by_cases h : ∃ j, ix j = i
    · obtain ⟨j, rfl⟩ := h
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simp only [not_exists] at h
      have hci : c i = 0 := by
        apply Subtype.ext
        rw [key i]
        simp [h]
      rw [hci, zero_smul]
      exact Submodule.zero_mem _
  · apply le_inf
    · exact Submodule.span_mono (Set.range_comp_subset_range _ _)
    · exact Submodule.span_le_restrictScalars _ _ _

end GlobalTheory.CompanionTheory.Ar.SubFrame
