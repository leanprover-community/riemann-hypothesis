module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MovedOfSplitPl
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplit
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

@[expose] public section

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rationalUnitary_move_selfDual_to_split : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (H : Geo.Tor.Host D.host.E) (N : ℕ), 0 < N → ∀ Λ : GenLat D.host.E V.rank, Λ.Unimod → Λ.TrivAt N → ∃ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ ∧ (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) i j : 𝓞 D.host.E) : D.host.E)) ∧ h ∈ GfC V ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V h).1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.actLat γ Λ = GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h)) := by
  first | exact @GlobalTheory.SplitMove.exists_move_to_split | exact GlobalTheory.SplitMove.exists_move_to_split | (intros; apply GlobalTheory.SplitMove.exists_move_to_split <;> assumption)
