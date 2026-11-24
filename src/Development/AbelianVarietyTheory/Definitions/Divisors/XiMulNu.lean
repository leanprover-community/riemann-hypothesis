module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import Mathlib.RingTheory.WittVector.Compare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open WittVector Ideal Matrix

namespace GlobalTheory.Sandwich

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

abbrev Ainf : Type := WittVector p (PreTilt O p)

def phiInv : Ainf p O →+* Ainf p O :=
  WittVector.map ((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p)

def ofPadic : ℤ_[p] →+* Ainf p O :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt O p))).comp (WittVector.equiv p).symm.toRingHom

def padicToO : ℤ_[p] →+* O := (fontaineTheta O p).comp (ofPadic p O)

variable {p O}

def root (ε : PreTilt O p) : PreTilt O p := (_root_.frobeniusEquiv (PreTilt O p) p).symm ε

def mu (ε : PreTilt O p) : Ainf p O := teichmuller p ε - 1

def nu (ε : PreTilt O p) : Ainf p O := teichmuller p (root ε) - 1

def xi (ε : PreTilt O p) : Ainf p O := ∑ i ∈ Finset.range p, teichmuller p (root ε) ^ i

open WittVector Ideal Matrix in
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
variable {p O} in
theorem _root_.GlobalTheory.Sandwich.xi_mul_nu (ε : PreTilt O p) :
    _root_.GlobalTheory.Sandwich.xi ε * _root_.GlobalTheory.Sandwich.nu ε = _root_.GlobalTheory.Sandwich.mu ε := by
  unfold _root_.GlobalTheory.Sandwich.xi _root_.GlobalTheory.Sandwich.nu _root_.GlobalTheory.Sandwich.mu
  rw [geom_sum_mul, ← map_pow]
  congr 2
  unfold _root_.GlobalTheory.Sandwich.root
  rw [← frobenius_def, frobenius_apply_frobeniusEquiv_symm]

open WittVector Ideal Matrix in
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
variable {p O} in
theorem _root_.GlobalTheory.Sandwich.phiInv_mu (ε : PreTilt O p) :
    _root_.GlobalTheory.Sandwich.phiInv p O (_root_.GlobalTheory.Sandwich.mu ε) = _root_.GlobalTheory.Sandwich.nu ε := by
  unfold _root_.GlobalTheory.Sandwich.phiInv _root_.GlobalTheory.Sandwich.mu _root_.GlobalTheory.Sandwich.nu
  rw [map_sub, map_one, WittVector.map_teichmuller]
  rfl

structure Datum (ε : PreTilt O p) (h : ℕ) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] where

  F : Matrix (Fin h) (Fin h) (Ainf p O)

  G : Matrix (Fin h) (Fin h) (Ainf p O)

  Ψ : Matrix (Fin h) (Fin h) (Ainf p O)

  Ψ' : Matrix (Fin h) (Fin h) (Ainf p O)

  ρT : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]

  ρM : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O)
  G_mul_F : G * F = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))
  F_eq : F = Ψ * F.map (phiInv p O)
  Ψ_mul : Ψ * Ψ' = xi ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))
  F_act : ∀ a, F * (ρT a).map (ofPadic p O) = ρM a * F

def etale (ε : PreTilt O p) (h : ℕ) : Datum ε h ℤ_[p] where
  F := 1
  G := mu ε • 1
  Ψ := 1
  Ψ' := xi ε • 1
  ρT := Algebra.ofId _ _
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (algebraMap _ _)
  G_mul_F := by simp
  F_eq := by simp
  Ψ_mul := by simp
  F_act := by intro a; simp [Algebra.ofId_apply]

namespace Datum

variable {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)

def al : (Fin h → O) →ₗ[O] (Fin h → O) := Matrix.toLin' (D.F.map (fontaineTheta O p))

def bb : (Fin h → O) →ₗ[O] (Fin h → O) := Matrix.toLin' (D.G.map (fontaineTheta O p))

def Fil : Submodule O (Fin h → O) := LinearMap.ker D.bb

def Lie : Submodule O (Fin h → O) := LinearMap.range D.bb

def Tsub (τ : Λ →+* O) : Submodule O (Fin h → O) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((D.ρT a).map (padicToO p O))) (τ a)

def Hsub (τ : Λ →+* O) : Submodule O (Fin h → O) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((D.ρM a).map (fontaineTheta O p))) (τ a)

def W (τ : Λ →+* O) : Submodule O (Fin h → O) := D.Tsub τ ⊓ LinearMap.ker D.al

end Datum

end GlobalTheory.Sandwich
