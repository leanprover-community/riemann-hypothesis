module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem smallFam_pair_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (J : Type) (f : J → X.functionField) (w : J → ℝ), (∀ j, f j ∈ P.Bl 1 1 (Real.exp (-w j))) → SmallFam (P.L.tens P.A) f w := by
  intro k _ X _ p P J f w hf
  have e (c : (P.L.tens P.A).B.ι) (j : J) :
      f j * (((P.r c.1 * P.r' c.2 : X.functionFieldˣ)) : X.functionField) = P.loc 1 1 (f j) c.1 c.2 := by
    simp only [Pair.loc, Units.val_mul, zpow_one]; ring
  refine ⟨fun c => P.r c.1 * P.r' c.2, GlobalTheory.PtHtComb.isRatSec_tens P.hr P.hr', ?_, ?_⟩
  · intro x c hc j
    rw [e]
    exact (hf j).1 x c.1 c.2 hc.1 hc.2
  · intro σ y c hc j
    obtain ⟨hc₁, hc₂⟩ := mem_ptsIn_inf.1 hc
    have h := nu_eq k X p P 1 1 (f j) (hf j).1 σ y c.1 c.2 hc₁ hc₂
    have hb := (hf j).2 σ y
    rw [h] at hb
    rw [e]
    change _ * Real.exp (-((P.L.φ σ).φ c.1 y + (P.A.φ σ).φ c.2 y) / 2) ≤ _
    simpa using hb

end GlobalTheory.HSNef
