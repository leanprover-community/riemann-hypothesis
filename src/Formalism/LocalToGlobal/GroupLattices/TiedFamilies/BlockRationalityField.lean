module

public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieEvR
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

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG Formalism.L2.G.Cmp Matrix

namespace Formalism.L2.G

def BlockRationalityField : Prop :=
  ∀ {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL] (h : P.m + 1 = n)
    (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G M : Tau → Matrix (Fin n) (Fin n) ℂ) (embLL : LL →+* ℂ)
    (lam : Tau → DomWeight n), WtTie P h pos lam → (∀ τ, ∃ M0 : GL (Fin n) LL, M τ = M0.1.map embLL) →
    BlockRational P h pos G M embLL lam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}



theorem blkRatRec_of_stmt (hS : BlockRationalityField) (X : Formalism.L2.Herm.Herm0 D) (Gt : GatTies D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    BlockRationalityAtPlace X Gt u w hg B := by
  refine hS (D.gat u w hg).P (locAt X u w hg B).rk (Gt.gat_pos u w hg) _ _ D.what₂.embLL ((D.fm u).lam 0) ?_ ?_
  · intro v s i
    exact Gt.gat_lam u w hg v s i
  · intro τ
    refine ⟨bc (tEL D τ) ((locAt X u w hg B).B)⁻¹, ?_⟩
    ext a b
    exact (tEL_emb D τ _).symm

end Formalism.L2.G
