module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleFrobDual

theorem charpoly_smul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (h : M * N = 1) (m : Multiset ℂ) (c : ℂ)
    (hM : M.charpoly = (m.map fun β => X - C β).prod) :
    (c • M).charpoly = (m.map fun β => X - C (c * β)).prod := by
  have h1 := GlobalTheory.ConjPoly.charpoly_smul_inv M N h m 1 hM
  have h2 := GlobalTheory.ConjPoly.charpoly_smul_inv N M (mul_eq_one_comm.1 h) (m.map (·⁻¹)) c
    (by rw [one_smul] at h1; rw [h1, Multiset.map_map]; simp)
  rw [h2, Multiset.map_map]
  simp

theorem cyclotomicChar_frobenius_eq_normPlace {D : D7} (i : D.ntw.Tw) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : v ∉ placesOver D.host.E (D.ntw.l i)) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver (F := D.host.E) A v)
    {σ : Gen.GE D.nd} (hσ : IsFrob (F := D.host.E) A (normV v) σ) :
    ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
  have h := cycZ_of_isFrob hv hA hσ
  change algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i) ((cycZ D.host.E D.nd.Om (D.ntw.l i) σ : ℤ_[D.ntw.l i]ˣ) : _) = _
  rw [h, map_natCast]

theorem rd_injective {D : D7} (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) :
    Function.Injective (rd i ι) :=
  ι.injective.comp (IsFractionRing.injective _ _)

end GlobalTheory.TripleFrobDual
