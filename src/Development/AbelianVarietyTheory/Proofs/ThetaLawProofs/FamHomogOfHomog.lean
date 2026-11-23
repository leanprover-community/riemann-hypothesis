module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyFamHomog

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

theorem famHomog_of_homog : ∀ (N : ℕ → ℕ) (κ : Rule), Homog N κ → FamHomog N κ := by
  intro N κ hH S _ _ _ P hg rig hr th hth v hv th' hth' v' hv' a M u u' ha hM hu hu'
  obtain ⟨Q, hg₁, rig₁, hr₁, th₁, hth₁, v₁, hv₁, th₁', hth₁', v₁', hv₁', M₁, h₁, h₂, ha₁, hN, hd⟩ :=
    KeyGalDesc.exists_keyPB_pair (algebraMap S (FractionRing S)) P hg rig hr th hth v hv th' hth' v' hv' a M ha hM
  have e := hH _ Q hg₁ rig₁ hr₁ th₁ hth₁ v₁ hv₁ th₁' hth₁' v₁' hv₁' _ M₁ ha₁ hN
  have hgQ : Q.g = P.g := KeyGalDesc.g_eq h₁
  rw [hu _ _ _ h₁, hu' _ _ _ h₂, hd] at e
  have hn : N Q.g = N P.g := congrArg N hgQ
  rw [hn] at e
  apply IsFractionRing.injective S (FractionRing S)
  simpa only [map_mul, map_pow] using e

end GlobalTheory.KeyFamHomog
