module

public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicModularFormsIrreducibleDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.algebraicModularForms_irreducible_decomposition : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j), ∃ (ι : Type) (_ : Finite ι) (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), (∀ P, NG.IsIrrRep Mr.wt.ρ (F P)) ∧ (∀ P P', NG.IsoRep (F P) (F P') → P = P') ∧ (∀ S', NG.IsIrrRep Mr.wt.ρ S' → (NG.isoTyp Mr.wt.ρ S').comap Mr.real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') ∧ (∀ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real ≠ ⊥) ∧ iSupIndep (fun P => (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real) ∧ ⨆ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real = ⊤ := by
  first | exact @GlobalTheory.AutReps.mtReal_decomp | exact GlobalTheory.AutReps.mtReal_decomp | (intros; apply GlobalTheory.AutReps.mtReal_decomp <;> assumption)
