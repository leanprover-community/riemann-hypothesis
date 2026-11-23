module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAllHeisenbergTranslatesOfOrthRealLatticeVacuStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthRealHeisenbergTranslatesVacuumOfOrthFockStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunEqZeroOfOrthHeisenbergTranslatesStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockTotal

theorem eq_zero_of_orth_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → f = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf hlat horth
  have hne : vac ≠ 0 := by
    intro h0
    have h1 := hvac.2.norm.2 (v.μ, v.𝓕) v.covol
    simp [h0, nrm2] at h1
  exact GlobalTheory.T.thetaFun_eq_zero_of_orth_heisenbergTranslates D ψ hvac.1 S T v f vac hf hvac.2.theta hne
    (GlobalTheory.T.orth_allHeisenbergTranslates_of_orth_real_latticeVacuum D ψ θ hθ S T x y hx hy vac hvac v f hf hlat
      (GlobalTheory.T.orth_realHeisenbergTranslates_vacuum_of_orth_fock D ψ θ hθ S T x y hx hy vac hvac v f hf horth))

end GlobalTheory.FockTotal
