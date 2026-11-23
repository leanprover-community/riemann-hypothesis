module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFunctionMapsOfCartierTwistSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisSectionsSplitStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem genericPoint_mem_of_mem_opens (Y : Scheme.{0}) [IsIntegral Y] (W : Y.Opens) {y : Y}
    (hy : y ∈ W) : genericPoint Y ∈ W :=
  ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr ⟨y, trivial, hy⟩

theorem ratsec_split_of_H1 : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (W₁ W₂ : Y.Opens),
    Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB D)) (W₁ ⊔ W₂) 1) →
    ∀ f : Y.functionField, (∀ y ∈ W₁ ⊓ W₂, D.RegularAt y f) →
    ∃ h₁ h₂ : Y.functionField, f = h₂ - h₁ ∧ (∀ y ∈ W₁, D.RegularAt y h₁) ∧
      ∀ y ∈ W₂, D.RegularAt y h₂ := by
  intro Y _ D W₁ W₂ hH f hf
  obtain ⟨ρ, hreg, hsurj, hres⟩ := GlobalTheory.T.exists_rationalFunction_maps_of_cartierTwistSections Y D
  by_cases g1 : genericPoint Y ∈ W₁
  · by_cases g2 : genericPoint Y ∈ W₂
    · have g12 : genericPoint Y ∈ W₁ ⊓ W₂ := ⟨g1, g2⟩
      obtain ⟨t, ht⟩ := hsurj (W₁ ⊓ W₂) f g12 hf
      obtain ⟨a, b, hab⟩ := GlobalTheory.T.mayer_vietoris_sections_split Y _ W₁ W₂ hH t
      refine ⟨ρ W₁ a, ρ W₂ b, ?_, fun y hy => hreg W₁ a y hy, fun y hy => hreg W₂ b y hy⟩
      rw [← ht, hab, map_sub, hres W₂ (W₁ ⊓ W₂) inf_le_right b g12,
        hres W₁ (W₁ ⊓ W₂) inf_le_left a g12]
    · refine ⟨ρ W₁ 0, f, by simp, fun y hy => hreg W₁ 0 y hy, fun y hy => ?_⟩
      exact absurd (genericPoint_mem_of_mem_opens Y W₂ hy) g2
  · refine ⟨-f, ρ W₂ 0, by simp, fun y hy => ?_, fun y hy => hreg W₂ 0 y hy⟩
    exact absurd (genericPoint_mem_of_mem_opens Y W₁ hy) g1

end GlobalTheory
