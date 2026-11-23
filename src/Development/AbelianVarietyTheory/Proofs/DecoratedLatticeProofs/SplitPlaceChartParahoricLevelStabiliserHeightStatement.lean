module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChartParahoricLevelStabiliserHeight
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

theorem _root_.GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal ∧ (∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl) ∧ (∀ k < D.R.m, ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, ((∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chS (k + 1) x)) ∨ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chT (k + 1) x))) → LiftsChar φ PP μ (w.ξ PP)) ∧ ∀ ι, IsChart s j φ ι → (∃ e : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) ∧ (∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _) ∧ ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y)) ∧ (∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) _ _) ∧ ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) _ _, ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.ChartTwist.chart_dict | exact GlobalTheory.ChartTwist.chart_dict | (intros; apply GlobalTheory.ChartTwist.chart_dict <;> assumption)
