module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ringHom_eq_on_adjoin_simple {E : Type} [Field E] [Algebra ℚ E] (f g : E →+* ℂ) (s : E) (h : f s = g s) (x : E)
    (hx : x ∈ IntermediateField.adjoin ℚ ({s} : Set E)) : f x = g x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h
  | algebraMap q => simp
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

theorem overK_iff_sqrt {D : D7} (σ : D.what₂.LL →+* ℂ) :
    OverK σ ↔ σ (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD) :=
  ⟨fun h => h _ (IntermediateField.mem_adjoin_simple_self ℚ D.host.sqrtMinusD),
    fun h x hx => ringHom_eq_on_adjoin_simple (σ.comp D.embE) (D.what₂.embLL.comp D.embE) D.host.sqrtMinusD h x hx⟩

theorem overK_iff_good_of_pins {D : D7} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (ha : AlgTie T) (hp : T.Q.Pins)
    (σ : D.what₂.LL →+* ℂ) : OverK σ ↔ GoodEmb T.Q.c (res T σ) := by
  have e0 := res_embLL T ha hp.2.2.1
  have h1 : D.what₂.embLL (D.embE D.host.sqrtMinusD) = T.Q.H.rt0 :=
    (RingHom.congr_fun D.embE_φ₀ D.host.sqrtMinusD).trans hp.1.2.2.1.symm
  have h2 : GoodEmb T.Q.c (res T D.what₂.embLL) := e0 ▸ T.toCore.good_σ₀
  have hx : D.embE D.host.sqrtMinusD = algebraMap T.Q.c.F D.what₂.LL
      (IntermediateField.inclusion T.Q.c.le (ReciprocityTheory.ChartRestriction.G.Geo.Tor.baseKA T.Q.l).ρ) :=
    D.what₂.embLL.injective (h1.trans (Eq.symm h2))
  refine (overK_iff_sqrt σ).trans ⟨fun h => ?_, fun h => ?_⟩
  · exact (congrArg σ hx).symm.trans (h.trans h1)
  · exact (congrArg σ hx).trans (Eq.trans h h1.symm)

end GlobalTheory.GalLift
