module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLocallyConstantComapAlgClosureTensorOfH
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.bijective_locallyConstant_comap_algClosure_tensor_of_henselian : ∀ (Λ : Type) (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], Function.Bijective (fun φ : LocallyConstant (PrimeSpectrum B) Λ => φ.comap ⟨PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom, PrimeSpectrum.continuous_comap _⟩) := by
  first | exact @GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor | exact GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor | (intros; apply GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor <;> assumption)
