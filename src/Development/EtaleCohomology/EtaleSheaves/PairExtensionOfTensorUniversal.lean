module

public import Development.EtaleCohomology.EtaleSheaves.LeafPairExtPf
public import Development.EtaleCohomology.EtaleSheaves.LeafTwTensExPf
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
public import Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPf

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafPairExtPf2
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafPairExtPf LateralTheory.E.LeafTwPairExistsPf

def pre {R : Type} [CommRing R] {I' I J K : Cx R} (μ : Pair I J K) (f : I' ⟶ I) : Pair I' J K where
  mul U s t w h := (μ.mul U s t w h).comp ((f.f s).hom.app (op U)).hom
  nat g s t w h a b := by
    change Sec.res g (μ.mul _ s t w h (Sec.map (f.f s) a) b) = μ.mul _ s t w h (Sec.map (f.f s) (Sec.res g a)) (Sec.res g b)
    rw [μ.nat, res_map]
  leibniz U s t w h a b := by
    change Sec.map (K.d w (w + 1)) (μ.mul U s t w h (Sec.map (f.f s) a) b) =
      μ.mul U (s + 1) t (w + 1) _ (Sec.map (f.f (s + 1)) (Sec.map (I'.d s (s + 1)) a)) b +
      s.negOnePow • μ.mul U s (t + 1) (w + 1) _ (Sec.map (f.f s) a) (Sec.map (J.d t (t + 1)) b)
    rw [μ.leibniz, map_map, map_map, f.comm]

def LeafTensUP : Prop := ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ μ : Pair I J K,
  ∃ u : T ⟶ K, ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (u.f w) (τ.mul U s t w h a b) = μ.mul U s t w h a b

def LeafExtTens : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  ∀ u : S ⟶ res _ (tw q i), ∃ g : T ⟶ res _ (tw q i), ι ≫ g = u

theorem LeafExtAlongAug_of (hup : LeafTensUP) (hext : LeafExtTens) : LeafExtAlongAug := by
  intro q _ i lam
  let σ := LateralTheory.E.LeafTwTensExPf.tau (sgl (tw q 0)) (res _ (tw q i))
  let τ := LateralTheory.E.LeafTwTensExPf.tau (res _ (tw q 0)) (res _ (tw q i))
  have hσ : σ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  have hτ : τ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  obtain ⟨u, hu⟩ := hup _ σ hσ lam
  obtain ⟨ι, hι⟩ := hup _ σ hσ (pre τ (resAug (tw q 0)))
  obtain ⟨g, hg⟩ := hext q i σ τ hσ hτ ι hι u
  refine ⟨post τ g, fun U t x b => ?_⟩
  have e : Sec.map (ι.f t) (σ.mul U 0 t t (zero_add t) x b) =
      τ.mul U 0 t t (zero_add t) (Sec.map ((resAug (tw q 0)).f 0) x) b := hι U 0 t t (zero_add t) x b
  rw [post_mul, ← e, map_map, ← HomologicalComplex.comp_f, hg, hu]

end LateralTheory.E.LeafPairExtPf2
