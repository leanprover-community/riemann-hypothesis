module

public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsBranchingCoordinatesIff
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT.PendExample

open Formalism.BasicNotions Classical NumberField GlobalTheory.MemberTorsor
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

variable (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)

variable {D lam}


variable {g : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ}


variable (K : Type) [Field K] [NumberField K] [StarRing K] (κ : Type) [Fintype κ] [DecidableEq κ]

variable {K κ}


variable (D : D7) (u : D.what₂.Word) (T : ℕ) [Fact T.Prime]


theorem nfAll_pos {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ≠ 0) : 0 < (nfAll l p p).re := by
  unfold nfAll
  simp only [fockF_self_eq (extremal ℂ n _)]
  rw [← Complex.ofReal_prod, Complex.div_ofReal_re]
  refine div_pos (fockF_self_pos hp) (Finset.prod_pos fun τ _ => ?_)
  have := fockF_self_pos (f := extremal ℂ n (l τ)) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (l τ).natW)
  rwa [fockF_self_eq, Complex.ofReal_re] at this

end GlobalTheory.LvT.PendExample
