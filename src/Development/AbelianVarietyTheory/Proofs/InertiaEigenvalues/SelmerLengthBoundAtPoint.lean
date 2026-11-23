module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.AdmissibleDesigns.KernelLengthHigherColumns
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthInvariantsNegTwistKmodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInvariantsLtTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityClassFieldFactsOfArtinTateEulerStatement
public import Formalism.AdmissibleDesigns.StatementOneBFromUnramified
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

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.SelmerBoundAtPoint

theorem finCore : Formalism.MainNotions.N.K.H0.FinCore :=
  ⟨fun {D} i r ρ π g2 w hw => GlobalTheory.FiniteTwistInvariants.main D i r ρ π g2 w hw,
   fun {D} i w hw e he => GlobalTheory.FinInvKO.finiteLength_invariants_negTwist_KmodO D i w hw e he⟩




theorem main : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.admBK i → LargeLevelLemmas.BlochKatoAnnihilators i → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → LargeLevelLemmas.tateH1FinitenessAtPlacesOver i → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → LargeLevelLemmas.adm51 i r ρ π → EmbeddingTypes.UnramifiedTrivialH1f i dc → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hA hT hE D i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin tie a51 unr hR hL hTB
  have : Fact ReciprocityTheory.ChartRestriction.T2.Core := ⟨GlobalTheory.T.local_duality_class_field_facts_of_artin_tate_euler hA hT hE⟩
  have : Fact Formalism.MainNotions.N.K.H0.FinCore := ⟨finCore⟩
  exact Formalism.MainNotions.N.K.Closed.theorem_n5_from_inputs i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin
    tie a51 (Formalism.MainNotions.N.K.StD.unramified_input_of_admitted i dc unr) hR hL hTB

end GlobalTheory.SelmerBoundAtPoint
