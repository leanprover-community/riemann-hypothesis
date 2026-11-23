module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalHeckeMatrixIntermediateLattice
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix


theorem _root_.GlobalTheory.T.exists_localHeckeMatrix_intermediateLattice : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k n : ℕ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D)
    (Λ M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (T C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)),
    IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    (∀ x, s (π (finPart D x)) = e * x) → (∀ a, π (finPart D (s a)) = a) →
    (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    (∀ x : D.host.F, π (finPart D (incA D (algebraMap D.host.F D.host.E x))) =
      algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) x) →
    Λ.FG → Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) = ⊤ →
    P.asIdeal • Λ ≤ M → M ≤ Λ → M.toAddSubgroup.relIndex Λ.toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    t ≠ 0 →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) ↔
      ∀ i, ((t • T.1) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
      ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    ∃ Z : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), (∀ i j, Z.1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      (∀ i j, π (finPart D (incA D (ϖ : D.host.E))) * (Z⁻¹).1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      Valued.v Z.1.det = Valued.v (π (finPart D (incA D (ϖ : D.host.E)))) ^ k ∧
      ∀ y : Fin n → GlobalTheory.SplitPlace.RF D, (finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
        ∀ i, (((Z⁻¹).1 * (t • T.1)) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) := by
  first | exact @GlobalTheory.HeckeLocMatrix.exists_local_matrix | exact GlobalTheory.HeckeLocMatrix.exists_local_matrix | (intros; apply GlobalTheory.HeckeLocMatrix.exists_local_matrix <;> assumption)
