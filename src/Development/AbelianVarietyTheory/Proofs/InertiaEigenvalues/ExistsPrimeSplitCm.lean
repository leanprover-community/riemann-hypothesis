module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDegreeOneAvoiding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDiscreteUOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitRealPrime

theorem exists_prime_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ p : ℕ, p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := by
  intro E _ _ _
  obtain ⟨p, hp, -, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E 0
  refine ⟨p, hp, fun w hw => ?_⟩
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
    rwa [map_natCast]
  obtain ⟨a, b, hab, ha, hb⟩ :=
    GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
  by_cases h : a = w
  · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
  · exact ⟨a, h, HeightOneSpectrum.ext ha⟩

end GlobalTheory.SplitRealPrime
