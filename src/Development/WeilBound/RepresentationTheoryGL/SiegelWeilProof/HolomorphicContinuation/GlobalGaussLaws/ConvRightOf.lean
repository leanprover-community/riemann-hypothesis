module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
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

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem convRight_of (hE : EisStrong) : ConvRight := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR
  have hn : 0 < n := by
    obtain ⟨h1, h2, -⟩ := hR
    omega
  obtain ⟨𝓕, h𝓕⟩ := hS.hμ
  have hsec : IsSection χ (s0 V n) (fun g : G D n => (ω g Φ).1 0) :=
    GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μ 𝓕 h𝓕 ω hS.hω l hS.hl s hS.hs Φ
      hS.hΦ
  obtain ⟨U, d, E, σ, -, -, -, -, -, -, -, hconv⟩ :=
    hE D n hn χ V.rank hS.hχ hS.hη H hS.hH (s0 V n) _ hsec (s0 V n)
  refine ⟨σ, fun z hz g => ?_⟩
  obtain ⟨u, hu, hb⟩ := (hconv z hz).1 {g} isCompact_singleton
  exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hb g rfl q) hu

end PositivityTheory.Rg.Sw.Glob
