module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockDoubleCosetOperatorKeepsLevelCharacter
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

theorem _root_.GlobalTheory.T.lowerBlockDoubleCosetOperator_keeps_levelCharacter : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ (ξl : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s j φ ι → ∀ (ϖ : (Fv D.host.F v)ˣ) (e : Blocks j D.R.t → ℤ) (R : Finset (GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v))) (d : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) → (Fv D.host.F v)ˣ), GlobalTheory.ParHecke.IsReps (GlobalTheory.ZonalCellDecomposition.mtor ϖ e) R d → ∀ F : GA D s.V → ℂ, (∀ κ ∈ Lev.levG s.V s.β s.L, ∀ g, F (g * κ) = Lev.levChi s.V s.β s.L κ * F g) → ∀ κ ∈ Lev.levG s.V s.β s.L, ∀ g, ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * κ * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) = Lev.levChi s.V s.β s.L κ * ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) := by
  first | exact @GlobalTheory.LowerBlockHecke.hecke_level | exact GlobalTheory.LowerBlockHecke.hecke_level | (intros; apply GlobalTheory.LowerBlockHecke.hecke_level <;> assumption)
