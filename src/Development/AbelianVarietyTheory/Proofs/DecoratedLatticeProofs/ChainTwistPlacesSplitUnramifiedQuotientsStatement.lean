module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesSplitUnramifiedQuotients
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.chainTwistPlaces_split_unramifiedQuotients : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → (∀ v, v ∈ c.S ↔ v ∈ w.S₀ ∨ ∃ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) ∧ (∀ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ w.S₀) ∧ Set.InjOn (fun PP : Pl D.host.E => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) w.Q ∧ (∀ PP ∈ w.Q, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ∧ Ideal.absNorm ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal = Ideal.absNorm PP.asIdeal ∧ ∃ PP' : Pl D.host.E, PP' ≠ PP ∧ (∀ P : Pl D.host.E, P.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ↔ P = PP ∨ P = PP') ∧ Ideal.absNorm PP'.asIdeal = Ideal.absNorm PP.asIdeal ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP' = (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP)⁻¹) ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.UnrOff (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w.S₀ := by
  first | exact @GlobalTheory.ChainTw.twist_places | exact GlobalTheory.ChainTw.twist_places | (intros; apply GlobalTheory.ChainTw.twist_places <;> assumption)
