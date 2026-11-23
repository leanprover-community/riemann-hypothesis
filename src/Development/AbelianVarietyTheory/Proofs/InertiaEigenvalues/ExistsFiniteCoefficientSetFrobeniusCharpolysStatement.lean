module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolys
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.exists_finite_coefficient_set_frobenius_charpolys : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (Formalism.ConjugateSelfDual.G E Ω)) (p : Formalism.ConjugateSelfDual.G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, ι.symm z ∈ K) → ∀ ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep ρ → (∀ σ ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) → ∃ Pm : GL (Fin a) (Qbar l), ∀ g s t, ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  first | exact @GlobalTheory.FrobSysCoef.main | exact GlobalTheory.FrobSysCoef.main | (intros; apply GlobalTheory.FrobSysCoef.main <;> assumption)
