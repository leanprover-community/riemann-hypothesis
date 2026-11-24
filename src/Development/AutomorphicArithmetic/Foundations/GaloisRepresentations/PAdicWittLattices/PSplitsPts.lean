module

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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem exists_factor {W : Scheme.{0}} {J : Type} (Ω : Type) [Field Ω]
    (p : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : J => W)) :
    ∃ (j : J) (x : UpperTheory.Gal.G3.sp Ω ⟶ W), p = x ≫ Sigma.ι (fun _ : J => W) j := by
  haveI : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have pt : ↑(UpperTheory.Gal.G3.sp Ω) := show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (p pt) = q := ⟨_, rfl⟩
  have hy : Sigma.ι (fun _ : J => W) j y = p pt := by
    rw [← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]
  refine ⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) p ?_,
    (IsOpenImmersion.lift_fac _ _ _).symm⟩
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = pt := Subsingleton.elim _ _
  exact ⟨y, hy⟩

theorem UpperTheory.Gal.G3.pSplitsPts :
    IsoPts → SplitsPts := by
  intro hIso Z Y W s _ _ c J _ σ hσ hpts
  refine ⟨hσ, ?_⟩
  let e := Limits.Sigma.desc (fun j : J =>
    pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))
  have hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e =
      pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) :=
    fun j => Sigma.ι_desc _ _
  have hlift : ∀ j, Etale (pullback.lift (σ j) (𝟙 W)
      (by rw [Category.id_comp]; exact hσ j) : W ⟶ pullback s c) := by
    intro j
    haveI : Etale (pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) ≫
        pullback.snd s c) := by
      rw [pullback.lift_snd]; infer_instance
    exact Etale.of_comp _ (pullback.snd s c)
  haveI : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  haveI : Etale e := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hlift
  show IsIso e
  apply hIso e
  intro Ω _ _ z
  obtain ⟨j, hj, huniq⟩ := hpts Ω (z ≫ pullback.snd s c) (z ≫ pullback.fst s c)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have hz : (z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j ≫ e = z := by
    rw [hι]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc]
      exact hj
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  refine ⟨(z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j,
    by rw [Category.assoc]; exact hz, fun q hq => ?_⟩
  obtain ⟨j', x', rfl⟩ := exists_factor Ω q
  rw [Category.assoc, hι] at hq
  have hs := congrArg (· ≫ pullback.snd s c) hq
  have hf := congrArg (· ≫ pullback.fst s c) hq
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hs hf
  have hjj : j' = j := huniq j' (by rw [← hs]; exact hf)
  rw [hjj, hs]
