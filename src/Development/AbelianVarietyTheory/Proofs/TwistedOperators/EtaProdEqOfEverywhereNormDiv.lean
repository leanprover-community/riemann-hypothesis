module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlmostNormFinDiag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlmostNormEtaProdEqNegOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBasisOfIsQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEverywhereNormDivOfEtaProdEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexTwoOfFiniteReal
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

theorem eta_eq_of_div_mem {K L : Type} [Field K] [Field L] [Algebra K L] {A : Type} [CommRing A]
    [Algebra K A] {a b : Aˣ} (h : a / b ∈ normGroup K L A) : eta K L A a = eta K L A b := by
  have hiff : a ∈ normGroup K L A ↔ b ∈ normGroup K L A := by
    have := (normGroup K L A).mul_mem_cancel_left (x := a / b) (y := b) h
    rwa [div_mul_cancel] at this
  by_cases hb : b ∈ normGroup K L A
  · rw [eta_eq_one_iff.2 hb, eta_eq_one_iff.2 (hiff.2 hb)]
  · rw [eta_eq_neg_one_iff.2 hb, eta_eq_neg_one_iff.2 (fun ha => hb (hiff.1 ha))]

theorem etaProd_eq_of_everywhereNorm_div {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    {x x' : FinFam K} {y y' : InfFam K} (h : EverywhereNorm K L (x / x') (y / y')) :
    etaProd K L x y = etaProd K L x' y' := by
  unfold etaProd
  congr 1
  · exact finprod_congr fun v => eta_eq_of_div_mem (h.1 v)
  · exact Finset.prod_congr rfl fun w _ => eta_eq_of_div_mem (h.2 w)

theorem exactSequence (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] : ExactSequence K L := by
  refine ⟨almostNorm_finDiag K L, fun t => (normTheorem K L t).symm, fun x y hx => ⟨?_, ?_⟩,
    exists_almostNorm_etaProd_eq_neg_one K L⟩
  · rintro ⟨t, ht⟩
    rw [etaProd_eq_of_everywhereNorm_div ht]
    exact (productFormula K L t).2
  · exact exists_everywhereNorm_div_of_etaProd_eq_one K L x y hx

end GlobalTheory.QuadSymbol

namespace GlobalTheory.Published

open GlobalTheory.QuadSymbol

theorem quadraticClassFieldTheory_holds : QuadraticClassFieldTheory :=
  ⟨fun K L _ _ _ _ _ _ =>
    ⟨localCharacters K L, normTheorem K L, exactSequence K L, productFormula K L⟩,
   fun F E K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => baseChange F E K L h⟩

end GlobalTheory.Published
