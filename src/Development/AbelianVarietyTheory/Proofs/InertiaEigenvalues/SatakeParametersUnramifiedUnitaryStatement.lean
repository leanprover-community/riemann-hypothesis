module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParametersUnramifiedUnitary
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Formalism.AlgebraicWeights.IsAlgWeight
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.satake_parameters_unramified_unitary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)) (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), Formalism.UG.IsUnramInv ϖ s q → ∀ p : locU n w →* Formalism.UG.GU s n, Function.Surjective p → ∀ σ : SmIrr (Formalism.UG.GU s n), IsCompAlong U (locU n w) p σ.ρ → ∀ α0 : Fin (n / 2) → ℂˣ, GlobalTheory.LFun.HasSatU ϖ q σ.ρ α0 → ∀ φ ∈ U, (∀ x : locU n w, p x ∈ Formalism.UG.KU s n → RU L n x.val φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU s n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU s n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU ϖ q h (fun i => (α0 i : ℂ)) • φ := by
  first | exact @GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed | exact GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed | (intros; apply GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed <;> assumption)
