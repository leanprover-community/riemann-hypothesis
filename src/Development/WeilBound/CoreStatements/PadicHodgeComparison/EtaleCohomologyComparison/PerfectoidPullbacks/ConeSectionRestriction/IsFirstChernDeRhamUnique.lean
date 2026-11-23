module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTwistingLineDataProjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistingSheafBaseChangeStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PowTop
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RestrictionBijectiveAboveDimension
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem isO1At_exists {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace R N) :
    ∃ D : E.LineData X, IsTautologicalLineAt D N i := GlobalTheory.T.exists_twisting_line_data_projective N i

theorem isO1_exists {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (hp : IsProjOver p) :
    ∃ D : E.LineData X, IsTautologicalLine p D := by
  obtain ⟨N, i, hi, hip⟩ := hp
  obtain ⟨D, hD⟩ := isO1At_exists N i
  exact ⟨D, N, i, hi, hip, hD⟩

theorem isTwistingSheaf_pullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}} (p : X ⟶ Sp R)
    (D : E.LineData X) (hD : IsTautologicalLine p D) :
    IsTautologicalLine (pullback.snd p (spMap φ)) (D.pb (pullback.fst p (spMap φ))) := GlobalTheory.T.twisting_sheaf_base_change φ p D hD

theorem isFirstChernDeRham_exists {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) :
    ∃ c : HdR q 2, IsFirstChernDeRham q D c := isFirstChernDeRham_exists_of q d D hD

theorem isO1_etale {R : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp R} {D : E.LineData X} (hD : IsTautologicalLine p D) :
    Etale D.f := by
  obtain ⟨N, i, -, -, h, -⟩ := hD
  exact h

theorem powK_ne_zero {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) (c : HdR q 2)
    (hc : IsFirstChernDeRham q D c) : powK q c d ≠ 0 := powK_ne_zero_main q d D hD c hc

end CrystallineSemistableComparison.Pb
