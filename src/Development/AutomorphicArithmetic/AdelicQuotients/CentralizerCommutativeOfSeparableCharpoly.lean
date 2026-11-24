module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem coord_comm {F R : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) F) (φ : R →ₗ[F] F) (s : Matrix (Fin n) (Fin n) R)
    (hs : s * γ.map (algebraMap F R) = γ.map (algebraMap F R) * s) :
    Commute (s.map φ) γ := by
  have hl : ∀ (r : R) (x : F), φ (r * algebraMap F R x) = φ r * x := by
    intro r x
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hr : ∀ (r : R) (x : F), φ (algebraMap F R x * r) = x * φ r := by
    intro r x
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  show s.map φ * γ = γ * s.map φ
  ext a c
  have h := congrArg φ (congrFun (congrFun hs a) c)

  simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, hl, hr] using h

private theorem coord_sum {F R ι : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (b : Module.Basis ι F R) (B : Finset ι) (s : Matrix (Fin n) (Fin n) R)
    (hB : ∀ a c, (b.repr (s a c)).support ⊆ B) :
    s = ∑ i ∈ B, b i • (s.map (b.coord i)).map (algebraMap F R) := by
  ext a c
  rw [Matrix.sum_apply]
  conv_lhs => rw [← b.linearCombination_repr (s a c)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hB a c) _ (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.smul_def, mul_comm]

private theorem sum_comm_of {F R ι : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (e : ι → R) (B : Finset ι) (S T : ι → Matrix (Fin n) (Fin n) F)
    (h : ∀ i j, S i * T j = T j * S i) :
    (∑ i ∈ B, e i • (S i).map (algebraMap F R)) * (∑ j ∈ B, e j • (T j).map (algebraMap F R)) =
      (∑ j ∈ B, e j • (T j).map (algebraMap F R)) * (∑ i ∈ B, e i • (S i).map (algebraMap F R)) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (e i), ← Matrix.map_mul, ← Matrix.map_mul, h]

private theorem comm_alg {F R : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) F) (hγ : γ.charpoly.Separable) (s t : Matrix (Fin n) (Fin n) R)
    (hs : s * γ.map (algebraMap F R) = γ.map (algebraMap F R) * s)
    (ht : t * γ.map (algebraMap F R) = γ.map (algebraMap F R) * t) : s * t = t * s := by
  classical
  let b := Module.Basis.ofVectorSpace F R
  let B := Finset.univ.biUnion fun a => Finset.univ.biUnion fun c =>
    (b.repr (s a c)).support ∪ (b.repr (t a c)).support
  have hsB : ∀ a c, (b.repr (s a c)).support ⊆ B := fun a c i hi =>
    Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _,
      Finset.mem_union_left _ hi⟩⟩
  have htB : ∀ a c, (b.repr (t a c)).support ⊆ B := fun a c i hi =>
    Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _,
      Finset.mem_union_right _ hi⟩⟩
  have h := sum_comm_of (R := R) (fun i => b i) B (fun i => s.map (b.coord i))
    (fun i => t.map (b.coord i)) fun i j =>
      (UpperTheory.V.Z.Tf.Orb.centComm F n γ _ _ hγ (coord_comm γ _ s hs) (coord_comm γ _ t ht)).eq
  rwa [← coord_sum b B s hsB, ← coord_sum b B t htB] at h

theorem UpperTheory.centralizer_commutative_of_separable_charpoly :
    CentComm := by
  intro F R _ _ _ f n γ hγ s t hs ht
  letI : Algebra F R := f.toAlgebra
  exact comm_alg γ hγ s t hs ht
