module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentMemLevelOfReduction
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

theorem _root_.GlobalTheory.T.principalPlace_component_mem_level_of_reduction : ∀ (D : D7) (S : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank), L.P.H = ⊥ → ∀ (g : GA D S), ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → (∀ PP' ∈ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.St βS → Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) → Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g))) = 1 → gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG S βS L := by
  first | exact @GlobalTheory.LevAssembly.gAt_mem_levG_of_red | exact GlobalTheory.LevAssembly.gAt_mem_levG_of_red | (intros; apply GlobalTheory.LevAssembly.gAt_mem_levG_of_red <;> assumption)
