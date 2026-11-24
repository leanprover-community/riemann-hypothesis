module

public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAdjoinBaseChangeImage
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

open TensorProduct

theorem _root_.GlobalTheory.T.etale_adjoin_baseChange_image' : ∀ (R S B : Type) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] (A₀ : Subalgebra R S) (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.Etale A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀) (S' : Subalgebra R S), A₀ ≤ S' → ∃ (_ : Algebra S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))) (_ : IsScalarTower R S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))), Algebra.Etale S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))) := by
  first | exact @GlobalTheory.etale_adjoin_baseChange_image | exact GlobalTheory.etale_adjoin_baseChange_image | (intros; apply GlobalTheory.etale_adjoin_baseChange_image <;> assumption)
