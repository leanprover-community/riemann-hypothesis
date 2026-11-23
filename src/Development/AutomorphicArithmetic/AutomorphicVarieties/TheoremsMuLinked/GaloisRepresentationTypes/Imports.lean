module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.EigChp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.FElMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Lam0
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open UpperTheory.V UpperTheory.V.Th
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev

theorem UpperTheory.V.Th.split :
    Split := by
  intro l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D b y x al E hn hgen hmap hJ ⟨t₀, ht₀, hEt⟩ hPL heig
  haveI : Module.Finite B b.M := by
    letI : Algebra (abelian₂ O Empty D) B := b.lam.toRingHom.toAlgebra
    haveI : IsScalarTower (abelian₂ O Empty D) B b.M := ⟨fun a c m => by
      rw [b.smul_lam, ← mul_smul]; rfl⟩
    haveI := b.fin
    exact Module.Finite.of_restrictScalars_finite (abelian₂ O Empty D) B b.M
  obtain ⟨lam, m₀, hlam, hm₀⟩ := Sp.lam0 O B b.M x ((b.supp _ (RingHom.ker_isPrime x)).2 hJ)
  obtain ⟨F, hF, hev⟩ := Sp.eig l L G0 T n O y al hPL heig
  refine ⟨x t₀ ^ 2 * lam m₀ * F ^ (3 * E + 6), mul_ne_zero (mul_ne_zero (pow_ne_zero _ ht₀) hm₀) (pow_ne_zero _ hF), fun m => ?_⟩
  filter_upwards [hev, eventually_ge_atTop m] with N ⟨α, hα, hd⟩ hN A hA
  exact ⟨α, Sp.one l L G0 _ (T.h N) n O r B u J D b T.q N A y x _ _ _ E α t₀ lam m₀ m _ hn hgen hmap hEt hlam
    (fun j => Subtype.ext (T.ta_ker N j)) hα hA hN (mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hd _))⟩
