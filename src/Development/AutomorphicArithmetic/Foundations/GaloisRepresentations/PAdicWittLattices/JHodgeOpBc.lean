module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV GlobalTheory.HodgeCoh UpperTheory.Gal.G3 UpperTheory.Gal.Int.Geo
universe u v

private theorem hodgeTrace_pull_congr {F : Type} [Field F] {Y Z : Scheme.{0}} (s t : Y ⟶ Z) [IsFinite s] [Etale s]
    (p : Z ⟶ sp F) {q q' : Y ⟶ sp F} (e : q = q') (h₁ : s ≫ p = q) (h₂ : t ≫ p = q) (h₁' : s ≫ p = q') (h₂' : t ≫ p = q')
    (a b : ℕ) (x : hodgeH p a b) :
    hodgeTrace h₁ a b (hodgePull h₂ a b x) = hodgeTrace h₁' a b (hodgePull h₂' a b x) := by
  subst e; rfl

theorem UpperTheory.Gal.G3.jHodgeOpBc :
    BcSplits → HodgeTr → TrBc.{0} → HodgeOpBc := by
  intro hBc hTr hTrBc k F _ _ φ H g _ _ a b
  letI : Algebra k F := φ.toAlgebra
  obtain ⟨hF, hE, -⟩ := hBc (Spec.map (CommRingCat.ofHom φ)) H.q (H.s g ≫ H.q) (H.s g ≫ H.q) (H.s g) rfl
    (H.s g) rfl PEmpty (fun e => e.elim) (fun e => e.elim)
  refine ⟨hF, hE, hodgeTrace (bcMap_snd _ (H.s g) rfl) a b, ?_, ?_⟩
  · exact hTrBc (hodge F a b) _ H.q (H.s g ≫ H.q) (H.s g) rfl _ (hTr F a b _ _ _ (bcMap_snd _ _ _))
  · intro hF' hE' x
    exact @hodgeTrace_pull_congr _ _ _ _ _ _ hF' hE' _ _ _
      (bcMap_snd (Spec.map (CommRingCat.ofHom φ)) (H.s g) rfl) _ _ _ _ a b x
