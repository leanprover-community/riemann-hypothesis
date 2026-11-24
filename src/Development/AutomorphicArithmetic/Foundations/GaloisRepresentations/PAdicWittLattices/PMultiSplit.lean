module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
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
import Mathlib.Tactic.Linter.HaveILetI
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

theorem UpperTheory.Gal.G3.pMultiSplit :
    FEtBasic → SplitsBasic → GalClosD → MultiSplit := by
  intro hF hS hG Z n
  induction n with
  | zero =>
    intro Y s d _
    exact ⟨Z, 𝟙 Z, 1, one_pos, UpperTheory.Gal.Int.Geo.fEt_id Z, fun i => i.elim0⟩
  | succ n ih =>
    intro Y s d hs
    obtain ⟨W, c, e, he, hc, hspl⟩ := ih (fun i => Y i.castSucc) (fun i => s i.castSucc)
      (fun i => d i.castSucc) (fun i => hs i.castSucc)
    have hP : FEt (pullback.snd (s (Fin.last n)) c) (d (Fin.last n)) :=
      hF.1 (pullback.fst _ _) (pullback.snd _ _) (s (Fin.last n)) c _
        (IsPullback.of_hasPullback _ _) (hs _)
    obtain ⟨W2, c2, G, _, _, a, σ, hgal, hσ⟩ := hG (pullback.snd (s (Fin.last n)) c) _ hP
    have hc2 : FEt c2 (Nat.card G) := hF.2.2 c2 G a hgal
    refine ⟨W2, c2 ≫ c, e * Nat.card G, Nat.mul_pos he Nat.card_pos,
      hF.2.1 c2 c e (Nat.card G) hc2 hc, ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_)
    · haveI := (hs (Fin.last n)).1
      haveI := (hs (Fin.last n)).2.1
      exact ⟨fun j => σ j ≫ pullback.fst _ _,
        (hS.2 (pullback.fst _ _) (pullback.snd _ _) (s (Fin.last n)) c
          (IsPullback.of_hasPullback _ _) c2 (Fin (d (Fin.last n))) σ hσ.1).mp hσ⟩
    · obtain ⟨τ, hτ⟩ := hspl i
      haveI := (hs i.castSucc).1
      haveI := (hs i.castSucc).2.1
      exact ⟨fun j => c2 ≫ τ j, hS.1 (s i.castSucc) c _ τ c2 hτ⟩
