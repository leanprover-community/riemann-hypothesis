module

public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDegreeSum
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GreenbergWiles

theorem sum_locDeg_eq_finrank : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime]
    (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) →
    ∑ v ∈ T, locDeg v = Module.finrank ℚ F := by
  intro F _ _ l _ T hT
  let _ : Fintype {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} := Fintype.subtype T hT
  rw [Finset.sum_subtype T hT]
  exact GlobalTheory.Proof.LocalDegreeSum.sum_locDeg F l

end GlobalTheory.CompanionTheory.GreenbergWiles
