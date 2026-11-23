module

public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalArtinCompatible
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms


theorem _root_.GlobalTheory.T.local_global_artin_compatible : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) {Ωv : Type} [Field Ωv] [Algebra (w.adicCompletion E) Ωv]
    [IsSepClosure (w.adicCompletion E) Ωv] (j : Ω →+* Ωv),
    (∀ y : E, j (algebraMap E Ω y) = algebraMap (w.adicCompletion E) Ωv (algebraMap E (w.adicCompletion E) y)) →
    ∀ (a : (w.adicCompletion E)ˣ) (σ : G E Ω) (g : Ωv ≃ₐ[w.adicCompletion E] Ωv),
    (∀ x : Ω, g (j x) = j (σ x)) →
    (∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension (w.adicCompletion E) Ωv),
      ((localArtinMap (w.adicCompletion E) Ωv a ⟨y, hy⟩ : maximalAbelianExtension (w.adicCompletion E) Ωv) : Ωv) = g y) →
    ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
    PositivityTheory.FamInh.res L (toAb E Ω σ) = PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin | exact GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin | (intros; apply GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin <;> assumption)
