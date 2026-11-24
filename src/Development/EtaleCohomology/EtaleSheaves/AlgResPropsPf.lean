module

public import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
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

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.AlgResPropsPf
open LateralTheory.E.t_E3Cut

theorem cancel {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : AlgRes (f ≫ g)) : AlgRes g := by
  intro Q hQ c
  obtain ⟨p, ⟨n, hn⟩, hp⟩ := h Q hQ c
  refine ⟨p.map f.hom, ⟨n, ?_⟩, ?_⟩
  · rw [Polynomial.coeff_map]; simpa using hn
  · rw [Polynomial.eval₂_map]; simpa using hp

theorem integral {A B : CommRingCat.{0}} (f : A ⟶ B) (h : f.hom.IsIntegral) : AlgRes f := by
  intro Q hQ c
  obtain ⟨p, hm, hp⟩ := h c
  refine ⟨p, ⟨p.natDegree, ?_⟩, ?_⟩
  · rw [← Polynomial.leadingCoeff, hm.leadingCoeff, map_one]
    exact fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
  · rw [hp]; exact Q.zero_mem

theorem loc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] :
    AlgRes (CommRingCat.ofHom (algebraMap A B)) := by
  intro Q hQ c
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S c
  refine ⟨Polynomial.C (s : A) * Polynomial.X - Polynomial.C a, ⟨1, ?_⟩, ?_⟩
  · have hu : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
    intro hm
    apply hQ.ne_top
    apply Q.eq_top_of_isUnit_mem hm
    simpa [Polynomial.coeff_C, Polynomial.coeff_X] using hu
  · have := IsLocalization.mk'_spec B a s
    simp only [CommRingCat.hom_ofHom, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
    rw [mul_comm, this, sub_self]; exact Q.zero_mem

def Comp : Prop :=
  ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes f → AlgRes g → AlgRes (f ≫ g)

def Push : Prop :=
  ∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D), IsPushout f g u v → AlgRes f → AlgRes v

def EtAlg : Prop := ∀ {A B : CommRingCat.{0}} (f : A ⟶ B), Et f → AlgRes f

theorem AlgResProps_of (h1 : Comp) (h2 : Push) (h3 : EtAlg) : LateralTheory.E.t_E3Cut.AlgResProps :=
  ⟨fun f g hf hg => h1 f g hf hg, fun f g h => cancel f g h, fun f g u v h hf => h2 f g u v h hf,
    fun f h => h3 f h, fun f h => integral f h, fun A B _ _ _ S _ => loc A B S⟩

end LateralTheory.E.AlgResPropsPf
