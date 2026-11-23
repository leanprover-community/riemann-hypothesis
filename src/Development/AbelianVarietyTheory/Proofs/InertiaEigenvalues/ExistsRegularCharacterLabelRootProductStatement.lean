module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRegularCharacterLabelRootProduct
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

theorem _root_.GlobalTheory.T.exists_regularCharacter_labelRoot_product : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (hn : 0 < n) (P : (ZMod g)[X])
    (hP : IsPrimeLab n P) (K : Type) [Field K] [Finite K] (hK : Nat.card K = g ^ n) (ι : K →+* Formalism.CyclotomicNorms.Fbar g),
    ∃ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ ∧
      (∃ x ∈ Formalism.CyclotomicNorms.rootsBar P, ∀ u : Kˣ, ((θ u : ℂˣ) : ℂ) = thetaOf L n x (ι u)) ∧
      ∀ u : Kˣ, ι u = L.gen n →
        ∏ j ∈ Finset.range n, (X - C ((θ (u ^ g ^ j) : ℂˣ) : ℂ)) = GlobalTheory.SerSys.TameGen.liftPoly L.teich P := by
  first | exact @GlobalTheory.RegLabelChar.exists_regularChar | exact GlobalTheory.RegLabelChar.exists_regularChar | (intros; apply GlobalTheory.RegLabelChar.exists_regularChar <;> assumption)
