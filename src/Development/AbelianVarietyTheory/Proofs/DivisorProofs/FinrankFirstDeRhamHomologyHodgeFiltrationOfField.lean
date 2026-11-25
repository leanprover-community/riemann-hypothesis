module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory

theorem finrank_HdR_Fil_of_field (HF : GlobalTheory.Published.AbelianDeRham.Free)
    (HH : GlobalTheory.Published.AbelianDeRham.Hodge) (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    FiniteDimensional k (HdR A) ∧ Module.finrank k (HdR A) = 2 * g ∧
      Module.finrank k (Fil A) = g := by
  obtain ⟨hfin, -, hrk⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim HF hA hg
  obtain ⟨-, -, hfin1, -, hrk1⟩ := HH k A g hA hg
  have p : PrimeSpectrum k := IsLocalRing.closedPoint k
  have h1 : Module.finrank k (primDR A) = 2 * g := by
    have := hrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have h2 : Module.finrank k (PrimitiveSubmodule A) = g := by
    have := hrk1 p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hd : Module.finrank k (HdR A) = 2 * g := by
    change Module.finrank k (Module.Dual k (primDR A)) = 2 * g
    rw [Subspace.dual_finrank_eq, h1]
  refine ⟨?_, hd, ?_⟩
  · change FiniteDimensional k (Module.Dual k (primDR A))
    infer_instance
  · have := Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)
    rw [h2, h1] at this
    change Module.finrank k (PrimitiveSubmodule A).dualAnnihilator = g
    omega

end GlobalTheory
