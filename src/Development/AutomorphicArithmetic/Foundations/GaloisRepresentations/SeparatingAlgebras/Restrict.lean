module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
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

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.restrict_pf :
    UpperTheory.Gal.Gen.Restrict := by
  classical
  intro k _ _ J J' i θ S h ε hε
  obtain ⟨s, c, hs, hc⟩ := h ε hε
  refine ⟨s.image (fun x => x ∘ i), fun ζ => ∑ η ∈ s with η ∘ i = ζ, c η, ?_, ?_⟩
  · intro ζ hζ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hζ
    obtain ⟨η, hη, rfl⟩ := hζ
    exact ⟨η, hs hη, rfl⟩
  · intro P
    have key : ∀ η : J' → k,
        MvPolynomial.aeval (η ∘ i) P = MvPolynomial.aeval η (MvPolynomial.rename i P) := by
      intro η
      rw [MvPolynomial.aeval_rename]
    calc _ = ‖MvPolynomial.aeval θ (MvPolynomial.rename i P)
          - ∑ η ∈ s, c η * MvPolynomial.aeval η (MvPolynomial.rename i P)‖ := by
          congr 2
          · exact key θ
          · rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image (fun x => x ∘ i))
              (g := fun x => x ∘ i) (fun η hη => Finset.mem_image_of_mem _ hη)]
            refine Finset.sum_congr rfl fun ζ _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun η hη => ?_
            rw [← (Finset.mem_filter.1 hη).2, key]
      _ ≤ ε := hc _
