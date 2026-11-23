module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapEqMk
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraZmodTorsorBijective
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

open scoped TensorProduct

theorem _root_.GlobalTheory.T.kummerAlgebra_zmod_torsor_bijective : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) → Function.Bijective (Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ))) (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := by
  first | exact @GlobalTheory.KummerTorsor.bijective | exact GlobalTheory.KummerTorsor.bijective | (intros; apply GlobalTheory.KummerTorsor.bijective <;> assumption)
