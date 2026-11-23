module

public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.Col2.EMt

theorem eMtTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch) (C : ColsTiedSym (I.rec7 l Z)) (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)), (∀ u F G, inner ℂ ((I.rec7 l Z).eMt u F) ((I.rec7 l Z).eMt u G) = I.ipMt l u I.mu0 F G) → (∀ u (a : (I.rec7 l Z).what₂.Tup), a ≠ (I.rec7 l Z).what₂.mu0 → ∀ F G, inner ℂ ((I.rec7 l Z).eMtTw u a F) ((I.rec7 l Z).eMtTw u a G) = I.ipMt l u a F G) → Formalism.L2.Rows.EMtTied (I.rec7 l Z) C t := by
  intro B X I hOk hP l Z l0 nch tp C t h0 h1
  refine ⟨fun u F G => ?_, fun u a ha F G => ?_⟩
  · rw [h0 u F G]
    exact (GlobalTheory.Mem.Col2.IpMt.ipMt_tie I hOk hP l Z u I.mu0 (C.forms u).jM (C.forms u).per.2.1 (C.forms u).per.2.2).1 F G
  · rw [h1 u a ha F G]
    exact (GlobalTheory.Mem.Col2.IpMt.ipMt_tie I hOk hP l Z u a (t.ptE.jM u a) (t.ptE.per u a ha).2.1 (t.ptE.per u a ha).2.2).1 F G

end GlobalTheory.Mem.Col2.EMt

end
