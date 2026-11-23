module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAbove
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

theorem _root_.GlobalTheory.T.prod_localValues_global_over_places_above : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (B : Type) [CommGroup B] (ψ1 : Ideles K →* B) (ψ2 : Ideles E →* B) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ v ∉ S, ∀ x, IsUnitAt v x → ψ2 (localIdele E v x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x, IsUnitAt w x → ψ1 (localIdele K w x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → ψ1 (localIdele K w x) = ψ2 (localIdele E v ϖ) ^ w.asIdeal.inertiaDeg (𝓞 E)) → ∀ a : Kˣ, ∃ (TK : Finset (HeightOneSpectrum (𝓞 K))) (TE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∈ TK, ∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) ∧ (∀ w ∉ TK, (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) → ψ1 (locUnit K w a) = 1) ∧ (∀ v ∈ TE, v ∉ S) ∧ (∀ v ∉ TE, v ∉ S → ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) = 1) ∧ ∏ w ∈ TK, ψ1 (locUnit K w a) = ∏ v ∈ TE, ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) := by
  first | exact @GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm | exact GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm | (intros; apply GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm <;> assumption)
