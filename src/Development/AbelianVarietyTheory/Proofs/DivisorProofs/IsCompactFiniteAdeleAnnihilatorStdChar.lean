module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAnnihilatorOpenSubgroupFiniteAdeles
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.AnnCompactStdChar

theorem isCompact_annihilator_of_isStdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
      IsCompact {x : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F | ∀ y ∈ L, ψ (pairA D.host.F 0 (x ⬝ᵥ y)) = 1} := by
  intro D ψ hψ κ _ L hL
  exact GlobalTheory.AnnCompactStd.isCompact_annihilator D.host.F ψ (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) κ L hL

end GlobalTheory.AnnCompactStdChar
