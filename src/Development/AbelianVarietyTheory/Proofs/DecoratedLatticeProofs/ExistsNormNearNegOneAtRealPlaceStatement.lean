module

public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipB
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormNearNegOneAtRealPlace
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.exists_norm_near_neg_one_at_real_place : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (j : K →+* ℂ), NumberField.ComplexEmbedding.IsReal j → ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (M : ℕ) (W : Set (Ideles E)), W ∈ nhds (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E (InfinitePlace.mk (j.comp (algebraMap E K))) (-1)) → ∃ a : Kˣ, (∀ w ∈ T, w.valuation K ((a : K) - 1) ≤ WithZero.exp (-(M : ℤ))) ∧ Units.map (ReciprocityTheory.Neutral.Bridge.HCFR.infPart E) (diagUnits E (Units.map (Algebra.norm E (S := K)) a)) ∈ W := by
  first | exact @GlobalTheory.NormSign.exists_norm_sign | exact GlobalTheory.NormSign.exists_norm_sign | (intros; apply GlobalTheory.NormSign.exists_norm_sign <;> assumption)
