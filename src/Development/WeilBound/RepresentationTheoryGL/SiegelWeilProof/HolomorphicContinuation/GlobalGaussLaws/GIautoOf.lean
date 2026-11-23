module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RealParExplicit
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

theorem gIauto_of (hT : PositivityTheory.PfSWUS.ThetaAuto) (hM : TensMem) : GIauto := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC Ψ hΨ
  have hm := hM D n V θ l s τ ε fr hC.hθ (lNZ D ψ θ l hC.hψ hC.hθ hC.hl) hC.hs hC.hfr Ψ hΨ 1
  have hphi : (phiS θ τ fr (cLoc l τ) Ψ 1).1 = tens θ τ fr (fP (cLoc l τ) 1) Ψ := by
    unfold phiS
    rw [dite_eq_left hm.1]
  have hStd : PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ 1) :=
    ⟨hC.hψ, hC.hχ, hC.hη, hC.hθ, hC.hμ, hC.hω, hC.hH, hC.hl, hC.hs, hC.hν, by rw [hphi]; exact hm.2⟩
  obtain ⟨h1, h2⟩ := hT D n V ψ χ θ μ ω H l s ν _ hStd hC.hr
  exact ⟨h1, fun γ hγ g => h2 γ hγ g⟩

end PositivityTheory.Rg.Sw.Glob
