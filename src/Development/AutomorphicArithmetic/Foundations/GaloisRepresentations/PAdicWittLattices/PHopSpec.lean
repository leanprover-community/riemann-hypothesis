module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem l_unit (l : ℕ) {k : Type} [Field k] (hl : (l : k) ≠ 0) (Ω : Type) [Field Ω] [Algebra k Ω] :
    IsUnit (l : Γ(sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := by
    intro h
    apply hl
    apply (algebraMap k Ω).injective
    rw [map_natCast, h, map_zero]
  have h2 : IsUnit (l : Ω) := isUnit_iff_ne_zero.mpr h1
  have h3 := h2.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm
  simpa using h3

theorem UpperTheory.Gal.G3.pHopSpec :
    EtGood → BcGood.{1} → GalClos → OpEx.{1} → OpTr.{1} → OpEt → OpBc.{1} → BcSplits → HopSpec := by
  intro hEt hBc hClos hEx hTr hOpEt hOpBc hSpl l _ k _ hl H Ω _ _ g d hd
  obtain ⟨_, _, hcard⟩ := hd
  have gs : GalSplit (H.s g) := hClos (H.s g) d hcard
  let g₀ : sp Ω ⟶ sp k := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  have hT : (et l (sp Ω)).Good := hEt l (sp Ω) (l_unit l hl Ω)
  have hT' : ((et l (sp Ω)).bc g₀).Good := hBc _ g₀ hT
  have hs : H.sΩ Ω g = bcMap g₀ (H.s g) rfl := rfl
  have ht : H.tΩ Ω g = bcMap g₀ (H.t g) (H.comm g) := rfl
  have hfe := hSpl g₀ H.q (H.s g ≫ H.q) H.q (H.s g) rfl (𝟙 _) (Category.id_comp _) PEmpty (fun j => j.elim) (fun j => j.elim)
  obtain ⟨_, _, -⟩ := hfe
  have hEq := hOpEt l (pullback.snd H.q g₀) (pullback.snd H.q g₀) (bcMap g₀ (H.s g) rfl) (bcMap g₀ (H.t g) (H.comm g))
    ((bcMap_snd g₀ (H.t g) (H.comm g)).trans (bcMap_snd g₀ (H.s g) rfl).symm)
  have toCorr : ∀ A, ((et l (sp Ω)).bc g₀).IsOp H.q H.q (H.s g) (H.t g) A → IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) A := by
    intro A hA
    have h1 := hOpBc (et l (sp Ω)) g₀ H.q (H.s g ≫ H.q) H.q (H.s g) (H.t g) rfl (H.comm g) A hA
    exact (hEq A).1 h1
  have hex : ∃ A, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) A := by
    obtain ⟨A, hA, -⟩ := (hEx _ hT' H.q H.q (H.s g) (H.t g) (H.comm g)).1 gs
    exact ⟨A, toCorr A hA⟩
  have hspec : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (hop l H Ω g) := by
    unfold hop
    rw [dite_eq_left hex]
    exact hex.choose_spec
  refine ⟨hspec, fun tr htr => ?_⟩
  have hA := ((hTr _ hT' H.q (H.s g ≫ H.q) H.q (H.s g) (H.t g) rfl (H.comm g) tr htr) _).2 gs rfl
  have hcorr := toCorr _ hA
  obtain ⟨tr', htr'⟩ := hT.tr (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀) (bcMap g₀ (H.s g) rfl) (bcMap_snd _ _ _)
  have key := fun A => hTr _ hT (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀) (pullback.snd H.q g₀)
    (bcMap g₀ (H.s g) rfl) (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _) (bcMap_snd _ _ _) tr' htr' A
  have e1 := (key _).1 ((hEq _).2 hspec)
  have e2 := (key _).1 ((hEq _).2 hcorr)
  exact e1.trans e2.symm
