module

import Development.EtaleCohomology.EtaleSheaves.KummerSequence.TwLocGenPfSec
public import Development.EtaleCohomology.TateTwists.TwSecLocPfR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
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
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

theorem ZarPow_of (hA : AlgPow) : ZarPow := by
  apply LateralTheory.E.H2CurveOrder.TwLocGenPfSec.ZarPow_of <;> assumption

theorem TwSecLoc_of_alg (hA : AlgPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := TwSecLoc_of (ZarPow_of hA)

end LateralTheory.EtaleFoundations.TwSecLocPf
