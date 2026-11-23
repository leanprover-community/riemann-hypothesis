module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousForm
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

theorem _root_.GlobalTheory.T.thickening_section_homogeneous_form : ∀ {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1)),
    (∀ s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩,
      ∃ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
        t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ∧
        s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht) ∧
    (∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) →
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩) := by
  exact @GlobalTheory.CompanionTheory.GE.ker_thickι_chart
