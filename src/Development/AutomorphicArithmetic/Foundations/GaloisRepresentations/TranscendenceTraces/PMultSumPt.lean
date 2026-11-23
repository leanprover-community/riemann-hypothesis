module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.multSumPt_of :
    StalkSum → MultSec → PtLift → PtOne → FibFin → MultSumPt := by
  intro hS hM hL hO hF V Ω _ _ r _
  have hI : IsIntegralHom r := inferInstance
  have hbij : Set.BijOn (fun z : gp Ω ⟶ V => pt z) (fib r (𝟙 (gp Ω))) Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · intro z hz z' hz' h
      exact hO Ω r Ω (𝟙 (gp Ω)) z z' hz hz' h
    · intro v _
      have hv : r v = pt (𝟙 (gp Ω)) := by
        have h1 := pt_eq (𝟙 (gp Ω)) (r v)
        simpa using h1
      obtain ⟨z, hz, hzv⟩ := hL r Ω (𝟙 (gp Ω)) v hv
      exact ⟨z, hz, hzv⟩
  have hfin : Finite V := by
    have hu : (Set.univ : Set V).Finite := by
      rw [← hbij.image_eq]
      exact (hF r Ω (𝟙 (gp Ω))).image _
    exact Set.finite_univ_iff.mp hu
  show (∑ᶠ (z : gp Ω ⟶ V) (_ : z ∈ fib r (𝟙 (gp Ω))), mult r Ω z) = _
  rw [finsum_mem_eq_of_bijOn (fun z : gp Ω ⟶ V => pt z) hbij
    (g := fun v : V => ((Module.length (V.presheaf.stalk v) (V.presheaf.stalk v)).toNat : ℤ))
    (fun z hz => hM Ω r z hz), finsum_mem_univ, ← Nat.cast_finsum, hS Ω r]
