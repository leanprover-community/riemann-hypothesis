module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section
namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem prS_finGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (k : GL (Fin a) (Af E)) :
    prS S a (finGL E a k) = finGL E a (prSf S a k) := by
  have hI : ∀ y, idemS S * sFin E y = sFin E (idemSf S * y) := fun y => Prod.ext (mul_zero _) rfl
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      + idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
        + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
      + sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - idemSf S * (1 : Matrix (Fin a) (Fin a) (Af E)) i j
        + idemSf S * k i j)
  generalize idemS S = I at hI ⊢
  generalize idemSf S = J at hI ⊢
  simp only [Matrix.one_apply]
  split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add (f := _), mul_add, mul_sub, hI, sub_zero,
    zero_sub, zero_add] <;> ring

theorem prO_finGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (k : GL (Fin a) (Af E)) :
    prO S a (finGL E a k) = finGL E a (prOf S a k) := by
  have hI : ∀ y, (1 - idemS S) * sFin E y = sFin E ((1 - idemSf S) * y) := fun y => Prod.ext (mul_zero _) rfl
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      + (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
        + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
      + sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - (1 - idemSf S) * (1 : Matrix (Fin a) (Fin a) (Af E)) i j
        + (1 - idemSf S) * k i j)
  generalize (1 - idemS S) = I at hI ⊢
  generalize (1 - idemSf S) = J at hI ⊢
  simp only [Matrix.one_apply]
  split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add (f := _), mul_add, mul_sub, hI, sub_zero,
    zero_sub, zero_add] <;> ring

theorem continuous_cornerGL_idemHom (a : ℕ) (e : Af E) (he : IsIdempotentElem e) :
    Continuous (cornerGL a (idemHom e he)) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => 1 - matN a (idemHom e he) 1 + matN a (idemHom e he) x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_const.mul continuous_id : Continuous fun x : Af E => e * x).comp
      ((continuous_apply j).comp (continuous_apply i))

theorem continuous_prSf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : Continuous (prSf S a) :=
  continuous_cornerGL_idemHom a _ _

theorem continuous_prOf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : Continuous (prOf S a) :=
  continuous_cornerGL_idemHom a _ _

end GlobalTheory.SchurExt

theorem GlobalTheory.SchurExt.eventually_prS_prO_finGL :
    ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := by
  intro E _ _ a S V V' hV hV'
  have h1 := (continuous_prSf S a).tendsto 1
  have h2 := (continuous_prOf S a).tendsto 1
  rw [map_one] at h1 h2
  filter_upwards [h1 hV, h2 hV'] with k hk hk'
  exact ⟨⟨_, hk, prS_finGL S a k⟩, _, hk', prO_finGL S a k⟩
