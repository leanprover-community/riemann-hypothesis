module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ChiDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAe
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.eventually_block_val_at_and_exists_inv_eq : ∀ {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ) (μ η : HChar E), AlmostIn ε μ → η.ValuesIn (1 / 2) ε → ∀ {r : ℕ}, Odd r → ∀ (μH ηH : Formalism.L2.NC.HC E), μH.χ = (μ : Ideles E →* ℂˣ) → ηH.χ = (η : Ideles E →* ℂˣ) → ∀ᶠ v in Filter.cofinite, (μH * ηH⁻¹).At v ((((block μ η r).val v : ℂˣ) : ℂ) * (Real.sqrt (normV v) : ℂ) ^ (-(r : ℤ))) ∧ ∃ y : K, ε y = (((block μ η r).val v : ℂˣ) : ℂ)⁻¹ := by
  first | exact @GlobalTheory.BlockVal.block_val_ae | exact GlobalTheory.BlockVal.block_val_ae | (intros; apply GlobalTheory.BlockVal.block_val_ae <;> assumption)
