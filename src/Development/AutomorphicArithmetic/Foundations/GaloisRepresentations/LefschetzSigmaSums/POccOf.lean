module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
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

open UpperTheory.Gal.LocalSmoothExtension


open AlgebraicGeometry CategoryTheory Limits GlobalTheory.HodgeCoh in
theorem UpperTheory.Gal.LocalSmoothExtension.occOf_of :
    MemOp → UpperTheory.Gal.G3.HodgeGood → UpperTheory.Gal.G3.HodgeTr → UpperTheory.Gal.G3.BcGood.{0} → UpperTheory.Gal.G3.OpBc.{0} → UpperTheory.Gal.G3.OpTr.{0} → UpperTheory.Gal.G3.BcSplits → OccOf := by
  intro memop hg htr bcg opbc optr bcs p _ D G L R _ _ gb k T N J g τ θ a b x hx hxe
  letI : Algebra R ℂ := τ.toAlgebra
  refine ⟨b, x, hx, fun j => ?_⟩
  obtain ⟨-, hfin, het, hop⟩ := memop p D G L R gb k T N J g j
  haveI := hfin
  haveI := het
  have hΘ := bcg (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (hg ℂ a b)
  have hs : (T.tower N g).s j ≫ (T.tower N g).q = (T.tower N g).s j ≫ (T.tower N g).q := rfl
  have h2 := opbc (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q
    ((T.tower N g).s j ≫ (T.tower N g).q) (T.tower N g).q ((T.tower N g).s j) ((T.tower N g).t j) hs
    ((T.tower N g).comm j) _ (hop _ hΘ)
  obtain ⟨hf', he', -⟩ := bcs (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q
    ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j) hs
    ((T.tower N g).s j) hs PEmpty (fun e => e.elim) (fun e => e.elim)
  haveI := hf'
  haveI := he'
  have ht' : UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).t j) ((T.tower N g).comm j) ≫
      pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ)) =
      UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs ≫
      pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ)) := by
    unfold UpperTheory.Gal.G3.bcMap
    rw [pullback.lift_snd, pullback.lift_snd]
  have htr' := htr ℂ a b (pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ))) _
    (UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs) rfl
  have hA := (optr (UpperTheory.Gal.G3.hodge ℂ a b) (hg ℂ a b) _ _ _ _ _ rfl ht' _ htr' _).1 h2
  have e1 : (UpperTheory.Gal.Int.Geo.bcAlong (T.tower N g) τ).s j =
      UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs := rfl
  refine ⟨e1 ▸ hf', e1 ▸ he', Eq.trans ?_ (hxe j)⟩
  rw [hA]
  rfl
