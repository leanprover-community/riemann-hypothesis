module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevOpenNormalIffDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Published

namespace GlobalTheory

theorem twist_front_inputs : PoitouTateDuality → LocalFiniteness → LocalTateDuality → LocalFinitenessK → LocalTateDualityK → LocalEulerCharK → GlobalArtinReciprocity → GlobalTheory.TwSys.Cheb ∧ ChebotarevDegreeOne ∧ ChebotarevOpenNormal ∧ PoitouTateTotallyComplex ∧ CohDimTwo ∧ TameLocal ∧ Formalism.MainNotions.BlochKatoReduction.Gen.ArchimedeanSignatureMatching ∧ RayCharacterArtin :=
  fun hP hF hT a b c hA => ⟨cheb_holds, chebotarevDegreeOne', cheb_holds, hP.totallyComplex, ⟨hP.cohDimTwoGlobal, cohDimTwoLocal_of_localFiniteness hF⟩, TameLocal_of_duality hT, (GlobalTheory.TateLimit.twist_cohomology_inputs hP a b c).1, hA.rayCharacterArtin⟩

end GlobalTheory
