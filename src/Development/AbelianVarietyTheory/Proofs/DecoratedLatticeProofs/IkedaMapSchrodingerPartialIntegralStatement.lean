module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaMapSchrodingerPartialIntegral
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

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.ikedaMap_schrodinger_partialIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (ν : Measure (WO A T)) (𝓨 : Set (WO A T)), IsCovolOne (ratL T A) ν 𝓨 → ∀ (ν' : Measure (WO A T')) (𝓨' : Set (WO A T')), IsCovolOne (ratL T' A) ν' 𝓨' → ∀ (μ₁ : Measure (Mx D t (dblSp A).rank)) (𝓕₁ : Set (Mx D t (dblSp A).rank)), IsCovolOne (ratMx D t (dblSp A).rank) μ₁ 𝓕₁ → ∀ (μ₂ : Measure (Mx D t A.rank)) (𝓕₂ : Set (Mx D t A.rank)), IsCovolOne (ratMx D t A.rank) μ₂ 𝓕₂ → ∀ φ, IsThetaFunO ψ (dblSp A) T φ → IsThetaFunO ψ (dblSp A) T' (ikeda ψ d μ₁ 𝓕₁ φ) ∧ sch ψ A T' ν' 𝓨' (ikeda ψ d μ₁ 𝓕₁ φ) = ikS d μ₂ (sch ψ A T ν 𝓨 φ) := by
  first | exact @GlobalTheory.IkedaSch.sch_ikeda | exact GlobalTheory.IkedaSch.sch_ikeda | (intros; apply GlobalTheory.IkedaSch.sch_ikeda <;> assumption)
