module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeElementIdempotentPartSplitPlaceLattic
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
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField


theorem _root_.GlobalTheory.T.exists_heckeElement_idempotentPart_splitPlace_lattice : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ ∀ v ∈ latG V g,
      (finPart D e • finVec V v ∈ latGHat V (g * a₀) ↔
        finPart D e • finVec V v ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E))) := by
  first | exact @GlobalTheory.HeckeLocLift.exists_hecke_ePart | exact GlobalTheory.HeckeLocLift.exists_hecke_ePart | (intros; apply GlobalTheory.HeckeLocLift.exists_hecke_ePart <;> assumption)
