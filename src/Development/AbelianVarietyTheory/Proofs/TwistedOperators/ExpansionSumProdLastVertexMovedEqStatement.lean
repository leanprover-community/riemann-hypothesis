module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionSumProdLastVertexMovedEq
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.expansion_sumProd_lastVertex_moved_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.grid D.R.m D.R.m), finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl → ∀ cc cr : ℂ,
    colShift S t (finEmb G.sp.topDec k) (S.Z.vac (.top t (lastIx D))) = cc • S.Z.vac (.top t (lastIx D)) →
    rowShift S k (S.Z.vac (.chi (lastIx D) D.R.m)) = cr • S.Z.vac (.chi (lastIx D) D.R.m) →
    ∀ (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (τ.sum fun d a => a *
      (∏ j, Function.update (fun j => (d.1 j).fn) (lastIx D)
        (cc • moveFn (colPt S t (finEmb G.sp.topDec k)) (d.1 (lastIx D)).fn) j (x j)) *
      ∏ i, Function.update (fun i => (d.2 i).fn) (lastIx D) (cr • moveFn (rowPt S k) (d.2 (lastIx D)).fn) i (y i)) =
    τ.sum fun d a => a * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i) := by
  first | exact @GlobalTheory.LastVertexLoc.sum_prod_moved_eq | exact GlobalTheory.LastVertexLoc.sum_prod_moved_eq | (intros; apply GlobalTheory.LastVertexLoc.sum_prod_moved_eq <;> assumption)
