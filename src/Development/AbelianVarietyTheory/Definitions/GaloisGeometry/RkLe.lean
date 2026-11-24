module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Realises
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

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem rkS {j : ℕ} (hN : RankTie X D j) : (X.Pj j).m + 1 = D.R.N j := (rankJ X j).trans hN.1.symm

theorem rkT {j : ℕ} (hN : RankTie X D j) : (X.Pj (j + 1)).m + 1 = D.R.N (j + 1) := (rankJ X (j + 1)).trans hN.2.symm

theorem rk_le {j : ℕ} (hN : RankTie X D j) : D.R.N j ≤ D.R.N (j + 1) := by
  rw [hN.1, hN.2]; exact NN_le X j

def zT {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  if IsOddPos (pos.symm τ).2 then ((f τ)⁻¹).transpose.submatrix id Fin.rev else f τ

def dfr {j : ℕ} (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ :=
  (d τ * f' τ).submatrix id (Fin.castLE (rk_le X D hN))

def evD {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) : DA X Kc j →+* Kc :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.eval fun y : Var (X.Pj (j + 1)) =>
      ι (zT X D pos f' (pos ⟨y.1, y.2.1⟩) (Fin.cast (rkT X D hN) y.2.2.1) (Fin.cast (rkT X D hN) y.2.2.2)))
    (fun z : X.ZA j => ι (d (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1) (Fin.cast hN.2.symm z.2.2.2)))

def valZ (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  MvPolynomial.eval (fun y : Var (X.Pj i) => zT X D pos f (posJ X D pos i ⟨y.1, y.2.1⟩) (Fin.cast h y.2.2.1) (Fin.cast h y.2.2.2)) R

def eT (i : ℕ) (τ : D.what₂.Tau) : ℤ := eAt (X.Pj i) ((posJ X D pos i).symm τ).1 ((posJ X D pos i).symm τ).2

def cT1 (j : ℕ) (τ : D.what₂.Tau) : ℤ := cMu X j (pos.symm τ).1 (pos.symm τ).2

end GlobalTheory.TwV.DelA

end
