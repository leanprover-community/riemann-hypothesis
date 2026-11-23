module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NerveCechDegreeZeroCompatible
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

theorem _root_.GlobalTheory.T.nerve_cech_degree_zero_compatible : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P),
    Function.Bijective e → ∃ ε : ∀ G : Pᵒᵖ ⥤ ModuleCat.{0} R, (nerveCx.obj G).X 0 ≅ ((cechOf e).obj G).X 0,
    (∀ {G G' : Pᵒᵖ ⥤ ModuleCat.{0} R} (φ : G ⟶ G'),
      (nerveCx.map φ).f 0 ≫ (ε G').hom = (ε G).hom ≫ ((cechOf e).map φ).f 0) ∧
    ∀ (G : Pᵒᵖ ⥤ ModuleCat.{0} R) (x : (nerveCx.obj G).X 0),
      ((nerveCx.obj G).d 0 1).hom x = 0 ↔ (((cechOf e).obj G).d 0 1).hom ((ε G).hom.hom x) = 0 := by
  exact @GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero.degZero
