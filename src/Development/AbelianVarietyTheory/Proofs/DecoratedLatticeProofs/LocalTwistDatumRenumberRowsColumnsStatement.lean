module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalTwistDatumRenumberRowsColumns
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (phiQ linOm)

theorem _root_.GlobalTheory.T.local_twist_datum_renumber_rows_columns : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (r a b : ℕ) (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (ε : Fin r ⊕ A ≃ Fin a) (ε' : Fin r ⊕ B ≃ Fin b), (∀ i, (ε (.inl i) : ℕ) = i) → (∀ i, (ε' (.inl i) : ℕ) = i) → (∀ ξ : (Fv D.host.F v)ˣ →* ℂˣ, (phiQ v r ξ = fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => datum ξ (z.submatrix ε' ε)) ∧ (GlobalTheory.SplitWeil.IsTame ξ → datum ξ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v)))) ∧ (∀ u : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ, u ∈ GlobalTheory.SplitWeil.SB _ ↔ (fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => u (z.submatrix ε' ε)) ∈ GlobalTheory.SplitWeil.SB _) ∧ (∀ (μS μT : (Fv D.host.F v)ˣ →* ℂˣ) (g : GL (Fin r ⊕ A) (Fv D.host.F v)) (h : GL (Fin r ⊕ B) (Fv D.host.F v)) (u : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ), (u ∈ GlobalTheory.SplitWeil.SB _ → GlobalTheory.ParHecke.omTwo μS μT g h u ∈ GlobalTheory.SplitWeil.SB _) ∧ ∀ (G : GL (Fin a) (Fv D.host.F v)) (H : GL (Fin b) (Fv D.host.F v)), G.1.submatrix ε ε = g.1 → H.1.submatrix ε' ε' = h.1 → (fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => GlobalTheory.ParHecke.omTwo μS μT g h u (z.submatrix ε' ε)) = (((μT (GeneralLinearGroup.det G))⁻¹ * μS (GeneralLinearGroup.det H) : ℂˣ) : ℂ) • linOm v G H fun z => u (z.submatrix ε' ε)) ∧ ∀ [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v)), ν.IsAddHaarMeasure → ∀ u u' : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ, GlobalTheory.SplitWeil.ip ν (fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => u (z.submatrix ε' ε)) (fun z => u' (z.submatrix ε' ε)) = GlobalTheory.SplitWeil.ip ν u u' := by
  first | exact @GlobalTheory.Reidx.renumber | exact GlobalTheory.Reidx.renumber | (intros; apply GlobalTheory.Reidx.renumber <;> assumption)
