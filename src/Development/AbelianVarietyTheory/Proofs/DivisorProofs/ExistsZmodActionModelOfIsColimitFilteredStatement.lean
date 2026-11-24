module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFiltered
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)),
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) →
    ∃ (k : J) (B : Type) (_ : CommRing B) (_ : Algebra (F.obj k) B)
      (_ : Algebra.FinitePresentation (F.obj k) B)
      (actB : Multiplicative (ZMod q) →* (B ≃ₐ[F.obj k] B)),
      letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra;
      ∃ e : c.pt ⊗[F.obj k] B ≃ₐ[c.pt] D, ∀ (g : Multiplicative (ZMod q)) (x : c.pt ⊗[F.obj k] B),
        e (GlobalTheory.TorsorColim.bcAct c.pt actB g x) = act g (e x) := by
  first | (exact @GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_action_model_of_isColimit  <;> assumption)
