module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationThetaIntegral
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weil_representation_theta_integral : ∀ {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (b₀ : HermE D r) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib) (Φ : schwartzA θ V.rank n) (g : G D n), Wz M m ψ b₀ (fun g => (ω g Φ).1 0) g = ∫ x, (ω g Φ).1 (jn hn x 0) ∂fib := by
  exact @GlobalTheory.CompanionTheory.WzFib.wz_eq_fib
