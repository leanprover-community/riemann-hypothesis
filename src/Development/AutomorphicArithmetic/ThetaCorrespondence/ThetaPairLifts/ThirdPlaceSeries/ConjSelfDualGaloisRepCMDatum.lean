module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

abbrev _root_.GlobalTheory.T.ConjSelfDualGaloisRepCMDatumThirdPlace : Prop :=  ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 μ hμ) = X - C c
end
end
