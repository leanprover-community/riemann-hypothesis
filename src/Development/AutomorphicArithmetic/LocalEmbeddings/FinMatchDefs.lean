module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.Grid GlobalTheory.ChainFr
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW)

namespace GlobalTheory.FinMatch

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def HalfEl (P : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (t₀ : ∀ v : P, E →ₐ[F] Fv F v) (z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : Prop :=
  (∀ u : AF F, (∀ v ∈ P, GlobalTheory.AdelicU.evFin F v u = 0) → u • z = 0) ∧ ∀ v : P, piW (t₀ v) z = 0

end Generic

variable {D : D7}

def piF {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) : EAf D →+* Fv D.host.F v :=
  (Algebra.TensorProduct.lift t (evalV D.host.F v) fun _ _ => Commute.all _ _).toRingHom

theorem piF_toEAf {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : AE D) :
    piF t (toEAf D z) = piW t z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => exact mul_comm _ _

structure IsPair (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
    (M : Model D.sp.cm.sig Vs Ws) : Prop where

  base : Bs.IsGood D.sp.cm.sig

  psi : Bs.ψ = ψ

  JV : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram

  JW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e

  herm : ∃ r s, Vs.IsHerm D.sp.cm.sig Bs r s

  skew : ∃ r s, Ws.IsSkew D.sp.cm.sig Bs r s

  good : M.IsGood Bs.ψ

def IsLat {S X : HSp D} {d : ℕ} (e : Fin d ≃ Fin X.rank) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)) : Prop :=
  (∀ y, y ∈ Vs.L ↔ star y ∈ ΛS) ∧ ∀ y, y ∈ Ws.L ↔ (fun k => y (e.symm k)) ∈ GlobalTheory.SkewLat.scLat D.host.AA ΛX

def IsCart (ε : Bool) {S X : HSp D} (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin d ≃ Fin X.rank) (Bs : Base D.host.F D.host.E)
    (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d) : Prop :=
  ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
    Ws.θ w = ((B.cart τ).submatrix e e).map conj

end GlobalTheory.FinMatch

end
