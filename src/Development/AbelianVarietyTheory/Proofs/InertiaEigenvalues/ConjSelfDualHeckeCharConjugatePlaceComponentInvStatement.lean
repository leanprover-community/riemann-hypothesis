module

public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSelfDualHeckeCharConjugatePlaceComponentInv
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL

theorem _root_.GlobalTheory.T.conjSelfDual_heckeChar_conjugatePlace_component_inv : ∀ {R : Ranks} (Hs : Host R) (μ : HChar Hs.E), IsCSD Hs μ → ∀ (w w' : HeightOneSpectrum (𝓞 Hs.E)), IsConjPl Hs w w' → ∃ i : w.adicCompletion Hs.E ≃+* w'.adicCompletion Hs.E, Continuous i ∧ (∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x)) ∧ ∀ x, μ.loc w' (Units.map i.toRingHom.toMonoidHom x) = (μ.loc w x)⁻¹ := by
  first | exact @GlobalTheory.ConjLocCsd.main | exact GlobalTheory.ConjLocCsd.main | (intros; apply GlobalTheory.ConjLocCsd.main <;> assumption)
