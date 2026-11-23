module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseTripleSpacesOfSeesaw
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.exists_placewise_triple_spaces_of_seesaw : ∀ (D : D7) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ p q : ℕ, (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) (W.rank - p) p ∧ Formalism.UG.HasSignature (gramAt D W₁ τ) (W₁.rank - q) q ∧
      Formalism.UG.HasSignature (gramAt D X τ) (X.rank - (p + q)) (p + q)) →
    ∀ (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    (∀ w, ∃ τ, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) →
    ∃ (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (V' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank)
      (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E (W.rank + W₁.rank)),
      V.J = (1 : D.host.E) • W.gram ∧ V'.J = (-1 : D.host.E) • W₁.gram ∧ Ws.J = D.host.xi0 • reindex e e X.gramᵀ ∧
      V.IsHerm D.sp.cm.sig Bs (W.rank - p) p ∧ V'.IsHerm D.sp.cm.sig Bs q (W₁.rank - q) ∧
      Ws.IsSkew D.sp.cm.sig Bs (W.rank + W₁.rank - (p + q)) (p + q) ∧
      ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ V.θ w = A.cart τ ∧ V'.θ w = -A₁.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.PlaceSpaces.spaces_of_triple | exact GlobalTheory.PlaceSpaces.spaces_of_triple | (intros; apply GlobalTheory.PlaceSpaces.spaces_of_triple <;> assumption)
