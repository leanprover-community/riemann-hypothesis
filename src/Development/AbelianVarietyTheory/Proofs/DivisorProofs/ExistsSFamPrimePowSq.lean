module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptySiegelFamilyOverArithmeticBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.SiegelTor

theorem exists_sFam_primePow_sq :
    ∀ g l : ℕ, 1 ≤ g → l.Prime → Odd l →
      ∃ j : ℕ, 1 ≤ j ∧ Nonempty (SFam g ((l ^ j) ^ 2) (zetaAway ((l ^ j) ^ 2))) := by
  intro g l hg hl _hodd
  obtain ⟨hLaws, hLaws2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam hLaws hLaws2 GlobalTheory.Moduli.cube_of_isLB
    GlobalTheory.thetaUnifAV_closed g l hg hl _hodd

  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  have hn : (l ^ max j₀ 1) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl.ne_zero)

  have key := hj₀ (max j₀ 1) (le_max_left _ _) (cycAway ((l ^ max j₀ 1) ^ 2)) (cycBase hn)
    (cycAway ((l ^ max j₀ 1) ^ 2)).subtype (arBase_cycAway _ hn)
  rwa [cycBase_ζ hn] at key

end GlobalTheory.SiegelTor
