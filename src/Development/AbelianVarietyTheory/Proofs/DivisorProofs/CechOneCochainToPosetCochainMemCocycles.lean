module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
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

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem cechOneCochainToPosetCochain_mem_cocycles : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toPos s U hU hinf c ∈ Z1 (capF s U hU hinf) := by
  intro I _ X R _ s U hU hinf c hc T T' T'' φ ψ
  have h1 : T.unop.set ⊆ T'.unop.set := NE.le_iff.1 (leOfHom φ.unop)
  have h2 : T'.unop.set ⊆ T''.unop.set := NE.le_iff.1 (leOfHom ψ.unop)
  have ha : T.unop.pt ∈ T''.unop.set := h2 (h1 T.unop.pt_mem)
  have hb : T'.unop.pt ∈ T''.unop.set := h2 T'.unop.pt_mem
  have ha' : T.unop.pt ∈ T'.unop.set := h1 T.unop.pt_mem
  have hW : cap U T''.unop ≤ U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt :=
    le_inf (le_inf (cap_le U ha) (cap_le U hb)) (cap_le U T''.unop.pt_mem)
  have hT' : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt := le_inf (cap_le U ha') (cap_le U T'.unop.pt_mem)
  have h23 : cap U T''.unop ≤ cap U T'.unop := cap_mono U (leOfHom ψ.unop)
  have key := congrArg (fun x => rsT x (cap U T''.unop)) (hc T.unop.pt T'.unop.pt T''.unop.pt)
  simp only [GlobalTheory.KS.rsT_add] at key
  have e1 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T.unop.pt ⊓ U T'.unop.pt := inf_le_left
  have e2 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T'.unop.pt ⊓ U T''.unop.pt :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have e3 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T.unop.pt ⊓ U T''.unop.pt :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [GlobalTheory.KS.rsT_rsT e1 hW, GlobalTheory.KS.rsT_rsT e2 hW, GlobalTheory.KS.rsT_rsT e3 hW] at key
  apply (cv s U hU hinf T'').injective
  rw [map_add (f := _), cv_toPos, cv_mp, cv_toPos, cv_toPos, GlobalTheory.KS.rsT_rsT hT' h23]
  exact key.symm

end GlobalTheory.CechCmp
