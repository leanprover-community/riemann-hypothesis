module

public import Mathlib.RingTheory.RamificationInertia.Inertia
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertia
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

theorem _root_.GlobalTheory.T.frobenius_restrictScalars_pow_mod_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w → IsPlaceOver A v ∧ normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 E) ∧ (∀ ι ∈ Ine (F := K) A, ι.restrictScalars E ∈ Ine (F := E) A) ∧ ∀ (σ : G K Ω) (φ : G E Ω), IsFrob A (normV w) σ → IsFrob A (normV v) φ → σ.restrictScalars E * (φ ^ w.asIdeal.inertiaDeg (𝓞 E))⁻¹ ∈ Ine (F := E) A := by
  first | exact @GlobalTheory.FrobRestrict.frob_restrict | exact GlobalTheory.FrobRestrict.frob_restrict | (intros; apply GlobalTheory.FrobRestrict.frob_restrict <;> assumption)
