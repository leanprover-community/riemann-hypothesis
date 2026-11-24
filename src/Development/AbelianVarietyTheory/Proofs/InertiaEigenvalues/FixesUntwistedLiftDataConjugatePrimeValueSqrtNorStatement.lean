module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedLiftDataConjugatePrimeValueSqrtNor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.fixesUntwistedLiftData_conjugatePrime_value_sqrtNorm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (PP : Pl D.host.E), FixBase T R i τ → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → τ ((((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)) = (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.ConjFix.fixBase_split_conj | exact GlobalTheory.ConjFix.fixBase_split_conj | (intros; apply GlobalTheory.ConjFix.fixBase_split_conj <;> assumption)
