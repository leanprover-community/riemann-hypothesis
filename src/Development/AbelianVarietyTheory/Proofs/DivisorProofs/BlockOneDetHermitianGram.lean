module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.MVEtale

theorem mv_etale_mid : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∀ (n i : ℤ) (x : Ht q (sp (Localization.Away f)) n i) (y : Ht q (sp A') n i), pull _ (spMap (Localization.awayMap (algebraMap A A') f)) _ _ x = pull _ (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) _ _ y → ∃ b : Ht q (sp A) n i, pull _ (spMap (algebraMap A (Localization.Away f))) _ _ b = x ∧ pull _ (spMap (algebraMap A A')) _ _ b = y := by
  intro q A A' _ _ _ _ f h1 h2 n i x y hxy
  obtain ⟨w, hS⟩ := chains_shortExact (ZMod q) A A' f h1 h2
  obtain ⟨d, hd, -⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective (ZMod q) (res (ZMod q) (tw q i)) (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)).2.1
  obtain ⟨e1, -, -⟩ := hd _ hS n
  have hb := cpull_biprod_bijective (ZMod q) ((chains (ZMod q)).obj (sp (Localization.Away f)))
    ((chains (ZMod q)).obj (sp A')) (res (ZMod q) (tw q i))
  obtain ⟨P, hP⟩ := (hb n).2 (x, y)
  have h0 : cpull (biprod.lift ((chains (ZMod q)).map (spMap (Localization.awayMap (algebraMap A A') f)))
      (-(chains (ZMod q)).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))))
      (res (ZMod q) (tw q i)) n P = 0 := by
    rw [cpull_lift_neg]
    have hP1 := congrArg Prod.fst hP
    have hP2 := congrArg Prod.snd hP
    simp only at hP1 hP2
    rw [hP1, hP2]
    exact sub_eq_zero.2 hxy
  obtain ⟨b, hb'⟩ := (e1 P).1 h0
  refine ⟨b, ?_, ?_⟩
  · have := congrArg Prod.fst (cpull_desc_pair ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A'))) (res (ZMod q) (tw q i)) n b)
    simp only at this
    have hb1 : cpull (biprod.desc ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A')))) (res (ZMod q) (tw q i)) n b = P := hb'
    rw [hb1] at this
    exact this.symm.trans (congrArg Prod.fst hP)
  · have := congrArg Prod.snd (cpull_desc_pair ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A'))) (res (ZMod q) (tw q i)) n b)
    simp only at this
    have hb1 : cpull (biprod.desc ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A')))) (res (ZMod q) (tw q i)) n b = P := hb'
    rw [hb1] at this
    exact this.symm.trans (congrArg Prod.snd hP)

end GlobalTheory.EtC.MVEtale
