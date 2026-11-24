module

public import Development.EtaleCohomology.EtaleTrace.LCoverCut
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def FSAffine : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k),
  ∀ (N d : ℕ) (ι : X ⟶ PN k N) (π : X ⟶ PN k d) (v : Fin (N + 1) → X.functionField) (w : Fin (d + 1) → X.functionField),
  IsClosedImmersion ι → Coord p ι v → Coord p π w →
  (∀ i, ∃ c : Fin (N + 1) → k, w i = ∑ j, kHom p (c j) * v j) →
  (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ loc X x) →
  IsAffineHom π

def FSDense : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k),
  ∀ (d : ℕ) (π : X ⟶ PN k d) (w : Fin (d + 1) → X.functionField), Coord p π w →
  (∀ (m : ℕ) (F : MvPolynomial (Fin (d + 1)) k), F.IsHomogeneous m → eval₂ (kHom p) w F = 0 → F = 0) →
  IsDominant π

theorem FinSurj_of (h1 : PNBasic) (hA : FSAffine) (hD : FSDense) : FinSurj := by
  intro k _ X _ p hp N d ι π v w hι hπ cv cw hlin hx hind
  have hsep : IsSeparated (PNto k d) := (h1 k d).2.1
  have : IsProper (π ≫ PNto k d) := by rw [hπ]; exact hp
  have : IsProper π := IsProper.of_comp π (PNto k d)
  have : IsAffineHom π := hA k p N d ι π v w hι cv cw hlin hx
  have : IsDominant π := hD k p d π w cw hind
  refine ⟨IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩, ?_⟩
  exact surjective_of_isDominant_of_isClosed_range π (π.isClosedMap.isClosed_range)
