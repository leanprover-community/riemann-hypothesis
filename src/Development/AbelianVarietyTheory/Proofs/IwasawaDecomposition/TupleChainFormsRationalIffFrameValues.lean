module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EWtApply
public import Formalism.LocalToGlobal.HermitianForms.TiedTwPGen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.RowTie

theorem ptEmb_iff_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ z : (I.per l u a).Wrow, (∃ x, (I.fm l u a).ptEmb x = z) ↔ z ∈ (I.fm l u a).ptC ∧ ∀ c, ∃ Pc ∈ RatSpan (I.rec7 l Z) (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) 1 Pc := by
  intro B X I hI hP l Z u a z
  have hsg : sgTG (D := I.rec7 l Z) (I.fm l u a) = (I.perIn u a).sgT := by
    funext τ
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (k + 1) := by
      rw [hk, show B.R.m * (2 * k + 1 + 1) = 2 * (B.R.m * (k + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = k + 1 := by omega
    show Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) =
      GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := congrArg shiftOf hsg
  exact rat_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT (l.fmL u a).famP (VV_shW B.wts.sgW _) hsh z

end GlobalTheory.Mem.Col2.TwP

end
