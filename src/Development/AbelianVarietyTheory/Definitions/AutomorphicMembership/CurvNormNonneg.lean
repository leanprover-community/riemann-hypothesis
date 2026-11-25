module

public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HPInvEqForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open scoped ComplexOrder ContDiff

namespace GlobalTheory.HodgeDomain

section Norms

variable {ι n : Type} [Fintype ι] [Fintype n]

def nsq (M : ι → Matrix n n ℂ) (v : ι → n → ℂ) : ℝ := ∑ τ, (star (v τ) ⬝ᵥ M τ *ᵥ v τ).re

def ratios (h h0 : ι → Matrix n n ℂ) : Set ℝ := {t | ∃ v, v ≠ 0 ∧ t = nsq h v / nsq h0 v}

def eigLo (h h0 : ι → Matrix n n ℂ) : ℝ := sInf (ratios h h0)

def eigUp (h h0 : ι → Matrix n n ℂ) : ℝ := sSup (ratios h h0)

variable {h h0 : ι → Matrix n n ℂ}

end Norms

section Calculus

variable {ι : Type} [Fintype ι] {p q : ℕ}

abbrev Pt (ι : Type) (p q : ℕ) : Type := ι → Matrix (Fin p) (Fin q) ℂ

def dR (f : Pt ι p q → ℂ) (z ξ : Pt ι p q) : ℂ := fderiv ℝ (fun v => f (unflat v)) (flat z) (flat ξ)

def dHol (f : Pt ι p q → ℂ) (z ξ : Pt ι p q) : ℂ := (dR f z ξ - Complex.I * dR f z (Complex.I • ξ)) / 2

def dAnti (f : Pt ι p q → ℂ) (z η : Pt ι p q) : ℂ := (dR f z η + Complex.I * dR f z (Complex.I • η)) / 2

def ddc (f : Pt ι p q → ℝ) (z ξ : Pt ι p q) : ℝ :=
  (dHol (fun w => dAnti (fun u => (f u : ℂ)) w ξ) z ξ).re / Real.pi

def SmoothOn (f : Pt ι p q → ℂ) : Prop := ContDiffOn ℝ ∞ (fun v => f (unflat v)) (DomFlat ι p q)

variable {n : Type} [Fintype n] [DecidableEq n]

def connMat (M : Pt ι p q → ι → Matrix n n ℂ) (z ξ : Pt ι p q) (τ : ι) : Matrix n n ℂ :=
  (M z τ)⁻¹ * Matrix.of fun a b => dHol (fun w => M w τ a b) z ξ

def curvMat (M : Pt ι p q → ι → Matrix n n ℂ) (z ξ η : Pt ι p q) (τ : ι) : Matrix n n ℂ :=
  Matrix.of fun a b => -dAnti (fun w => connMat M w ξ τ a b) z η

def connNorm (h h0 : Pt ι p q → ι → Matrix n n ℂ) (β : Pt ι p q → Pt ι p q → ℝ) (z : Pt ι p q) : ℝ :=
  sSup {t | ∃ ξ v, β z ξ ≤ 1 ∧ nsq (h0 z) v ≤ 1 ∧
    t = Real.sqrt (nsq (h0 z) fun τ => (connMat h z ξ τ - connMat h0 z ξ τ) *ᵥ v τ)}

def curvNorm (h : Pt ι p q → ι → Matrix n n ℂ) (β : Pt ι p q → Pt ι p q → ℝ) (z : Pt ι p q) : ℝ :=
  sSup {t | ∃ ξ η v, β z ξ ≤ 1 ∧ β z η ≤ 1 ∧ nsq (h z) v ≤ 1 ∧
    t = Real.sqrt (nsq (h z) fun τ => curvMat h z ξ η τ *ᵥ v τ)}

end Calculus

section Boundary

variable {ι : Type} [Fintype ι] {p q : ℕ}

structure BdData (ι : Type) [Fintype ι] (p q : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)) where

  m : ℕ

  nrm : Fin m → Pt ι p q → ℝ
  nrm_pos : ∀ i, ∀ z ∈ DomI ι p q, 0 < nrm i z
  nrm_le : ∀ i, ∀ z ∈ DomI ι p q, nrm i z ≤ 1
  nrm_smooth : ∀ i, SmoothOn fun z => (nrm i z : ℂ)
  nrm_inv : ∀ i, ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, nrm i (moebI γ z) = nrm i z

  kae : Pt ι p q → Pt ι p q →ₗ[ℂ] Pt ι p q →ₗ⋆[ℂ] ℂ
  kae_herm : ∀ z ∈ DomI ι p q, ∀ ξ η, kae z η ξ = starRingEnd ℂ (kae z ξ η)
  kae_pos : ∀ z ∈ DomI ι p q, ∀ ξ, ξ ≠ 0 → 0 < (kae z ξ ξ).re
  kae_smooth : ∀ ξ η, SmoothOn fun z => kae z ξ η
  kae_inv : ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, ∀ ξ η,
    kae (moebI γ z) (fun τ => tanAct (γ τ) (z τ) (ξ τ)) (fun τ => tanAct (γ τ) (z τ) (η τ)) = kae z ξ η

  cst : ℝ
  cst_pos : 0 < cst
  cst_small : ∀ i, ∀ z ∈ DomI ι p q, ∀ ξ,
    2 * m * cst * |ddc (fun w => Real.exp 1 - Real.log (nrm i w ^ 2)) z ξ| ≤ Real.exp 1 * (kae z ξ ξ).re

  metW : Pt ι p q → ι → Matrix (Fin p) (Fin p) ℂ

  metOm : Pt ι p q → ι → Matrix (Fin q) (Fin q) ℂ
  metW_pos : ∀ z ∈ DomI ι p q, ∀ τ, (metW z τ).PosDef
  metOm_pos : ∀ z ∈ DomI ι p q, ∀ τ, (metOm z τ).PosDef
  metW_smooth : ∀ τ a b, SmoothOn fun z => metW z τ a b
  metOm_smooth : ∀ τ a b, SmoothOn fun z => metOm z τ a b
  metW_inv : ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, ∀ τ,
    (jW (γ τ) (z τ))ᴴ * metW (moebI γ z) τ * jW (γ τ) (z τ) = metW z τ
  metOm_inv : ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, ∀ τ,
    (kapQ (γ τ) (z τ))ᴴ * metOm (moebI γ z) τ * kapQ (γ τ) (z τ) = metOm z τ

def hodgeI (c : ι → ℝ) (z : Pt ι p q) (τ : ι) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := hodge (c τ) (z τ)

namespace BdData

variable {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (B : BdData ι p q Γ)

def ri (i : Fin B.m) (z : Pt ι p q) : ℝ := Real.exp 1 - Real.log (B.nrm i z ^ 2)

def r (z : Pt ι p q) : ℝ := Real.exp 1 - Real.log ((∏ i, B.nrm i z) ^ 2)

def beta (z ξ : Pt ι p q) : ℝ := (B.kae z ξ ξ).re - B.cst * ∑ i, ddc (fun w => Real.log (B.ri i w)) z ξ

def met (z : Pt ι p q) (τ : ι) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := blkMet (B.metW z τ) (B.metOm z τ)

end BdData

def detNorm (c : ι → ℝ) (s : ℂ) (z : Pt ι p q) (τ : ι) : ℝ := ‖s‖ * Real.sqrt (hodgeI c z τ).det.re

def onQuot {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (f : Pt ι p q → ℝ) (x : XCc ι p q Γ) : ℝ :=
  f (Quot.out x : DomI ι p q)

end Boundary

end GlobalTheory.HodgeDomain
