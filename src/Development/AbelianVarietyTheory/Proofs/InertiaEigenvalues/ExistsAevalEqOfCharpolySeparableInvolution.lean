module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZero
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem exists_aeval_eq_of_charpoly_separable {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) (a : A) :
    ∃ f : E[X], a = aeval g f := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hint : IsIntegral E g := Algebra.IsIntegral.isIntegral g
  have hm0 : minpoly E g ≠ 0 := minpoly.ne_zero hint
  have hf : aeval (LinearMap.mulLeft E g) (minpoly E g) = 0 := by
    have := aeval_algHom_apply (Algebra.lmul E A) g (minpoly E g)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hn : 0 < Module.finrank E A := Module.finrank_pos
  have h1 := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank _ _ hf
  have h2 : (LinearMap.mulLeft E g).charpoly ∣ minpoly E g :=
    (hP.squarefree.dvd_pow_iff_dvd hn.ne').1 h1
  have h3 : Module.finrank E A ≤ (minpoly E g).natDegree := by
    have := natDegree_le_of_dvd h2 hm0
    rwa [LinearMap.charpoly_natDegree] at this
  have hli := linearIndependent_pow (K := E) g
  have h4 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h4
  haveI : Nonempty (Fin (minpoly E g).natDegree) := ⟨⟨0, by omega⟩⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin]; omega)
  have hle : Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin E {g}) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hg : g ∈ Algebra.adjoin E {g} := Algebra.subset_adjoin (Set.mem_singleton g)
    exact Subalgebra.pow_mem (Algebra.adjoin E {g}) hg (i : ℕ)
  have ha : a ∈ Algebra.adjoin E {g} := by
    have : a ∈ Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) := by
      rw [htop]; trivial
    exact hle this
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨f, hf⟩ := ha
  exact ⟨f, hf.symm⟩

theorem InvAlg.exists_aeval_eq_of_separable :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f :=
  fun _ B hP a => exists_aeval_eq_of_charpoly_separable B.g hP a

end GlobalTheory.UnitLemma
