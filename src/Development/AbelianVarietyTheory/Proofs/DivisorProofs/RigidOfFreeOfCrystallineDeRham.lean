module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Published.AbelianDeRham

theorem rigid_of_free_of_crystallineDeRham : GlobalTheory.Published.AbelianDeRham.Free →
    GlobalTheory.Published.CrystallineDeRham → GlobalTheory.Published.AbelianDeRham.Rigid := by
  intro H H' R _ A _ g hA hg I κ hκ R₀ _ π hπ hI A₀ _ i h
  have := hA.smooth
  have := hA.proper
  obtain ⟨h₁, -⟩ := H' R I κ hκ R₀ π hπ hI _ _ (A.hom ≫ 𝟙 _) A₀.hom i inferInstance inferInstance
    inferInstance (by rw [Category.comp_id]; exact h.1) (liftMor κ h).isMor
  have hP := (H R A g hA hg).1
  refine ⟨fun c d e ↦ Subtype.ext (h₁.1 ?_), fun c ↦ ?_⟩
  · have := congrArg Subtype.val e
    simpa only [GrpMor.coe_pull] using this
  · obtain ⟨c', hc'⟩ := h₁.2 c.1
    have hm : c' ∈ prim (dp0 R) (𝟙 _) A := by
      rw [show prim (dp0 R) (𝟙 _) A = ⊤ from hP]; trivial
    exact ⟨⟨c', hm⟩, Subtype.ext (by rw [GrpMor.coe_pull]; exact hc')⟩

end GlobalTheory.Published.AbelianDeRham
