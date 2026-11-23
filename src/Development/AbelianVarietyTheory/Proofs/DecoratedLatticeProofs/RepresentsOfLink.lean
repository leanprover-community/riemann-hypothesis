module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.UnimodularTower
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalDefiniteSpaceH
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LiftsCart
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower
open GlobalTheory.ChainOnto (Com PiLocalization₂)
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSawCompare

variable {D : D7} {u : D.what₂.Word}

theorem defSp_is {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) {S : D.what₂.Tau → SPar} (M : DSModel V S) (x : DefSp V)
    (h1 : x.s = cart M) (h2 : x.B = onb M) (h3 : IsSelfDualC V x.L) : x.Is := by
  have hs' : ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 := fun τ => by
    have := hs (tauE D τ)
    rw [hp (tauE D τ)] at this
    exact this
  have hJ : ∀ τ, Formalism.REAL.Jm (M.ε τ) = 1 := fun τ => by
    have := signs_pos_of_frame_gram_posdef (M.ε τ) (M.fr τ) _ (M.fr_gram τ) (hs' τ)
    unfold Formalism.REAL.Jm; simp [this]
  have hd := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ τ, x.s τ = 1 := fun τ => by rw [h1, cart, hJ, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd τ)]
  refine ⟨hs, Inh.coCpt_of_isDefinite hs fun τ => Or.inl (hp τ), fun τ => ?_, fun τ => Or.inl (hc τ), fun τ => ?_, h3⟩
  · rw [hc]
    exact ⟨by simp, by simp, by simpa using Formalism.IndefR.Fin.Lifts.posDef_of_sig _ (hs' τ)⟩
  · refine ⟨V.rank, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, by simp [hc]⟩
    rw [h2, onb, ← M.fr_gram τ, hJ, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (hd τ), Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_nonsing_inv _ (hd τ)]
    simp

abbrev Live (D : D7) (u : D.what₂.Word) : Type := ∀ j, Submodule ℂ (Fn D u j)

variable (W : Live D u) {c : Com D}


variable {σ j : ℕ} {N : Node c u (σ + 1) j} {N' : Node c u σ (j + 1 + 1)} (d : Dbl N N')



variable {j : ℕ} {N : Node c u 0 j} {T : HSp D} {top : RowOn T} (e : Fin2 N top)


variable {W}


variable {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)} {k : ColStep A A'} {vol : Vol X}


end GlobalTheory.SeeSawCompare

end
