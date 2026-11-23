module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransportCovolumeOneHaar
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory


theorem _root_.GlobalTheory.T.darbouxCoords_transport_covolumeOne_haar : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) →
    ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
    letI : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
    ∃ (lam : MeasureTheory.Measure ((κ → AF D.host.F) × (κ → AF D.host.F)))
      (𝓖 : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
      lam.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) 𝓖 lam ∧
      lam 𝓖 = 1 ∧ ∀ g : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
        ∫ w in 𝓕, g (e w) ∂ν = ∫ p in 𝓖, g p ∂lam := by
  first | exact @GlobalTheory.DarbouxMeasure.transport_covol_one | exact GlobalTheory.DarbouxMeasure.transport_covol_one | (intros; apply GlobalTheory.DarbouxMeasure.transport_covol_one <;> assumption)
