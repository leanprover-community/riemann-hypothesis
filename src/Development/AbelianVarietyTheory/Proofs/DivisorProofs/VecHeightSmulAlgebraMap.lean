module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmulStatement
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

namespace GlobalTheory.Adelic

theorem vecHeight_smul_algebraMap (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hw : Submodule.span F (Set.range w.col) = ⊤) (hA : ∀ σ, (A σ).det ≠ 0)
    (Ω : Type) [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
    (y : Fin N → K) (c : Ω) (hy : y ≠ 0) (hc : c ≠ 0) :
    vecHeight w A (c • fun j => algebraMap K Ω (y j)) = pointHeight w A y := by
  set z : Fin N → Ω := c • fun j => algebraMap K Ω (y j) with hz
  let L : IntermediateField K Ω := IntermediateField.adjoin K {c}
  have hcK : IsIntegral K c := ((Algebra.IsAlgebraic.isAlgebraic (R := F) c).tower_top K).isIntegral
  haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hcK
  haveI : NumberField L := NumberField.of_module_finite K L
  have hcL : c ∈ L := IntermediateField.mem_adjoin_simple_self K c
  have hle : coordField F z ≤ L.restrictScalars F := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨j, rfl⟩
    exact mul_mem hcL (L.algebraMap_mem (y j))
  let ι : coordField F z →ₐ[F] L := IntermediateField.inclusion hle
  letI : Algebra (coordField F z) L := ι.toRingHom.toAlgebra
  haveI : IsScalarTower F (coordField F z) L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  let z' : Fin N → coordField F z := fun j => ⟨z j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩
  let c' : L := ⟨c, hcL⟩
  have hc' : c' ≠ 0 := fun h => hc (congrArg Subtype.val h)
  have hyL : (fun j => algebraMap K L (y j)) ≠ 0 := fun h => hy (funext fun j =>
    (algebraMap K L).injective ((congrFun h j).trans (map_zero _).symm))
  have he : (fun j => algebraMap (coordField F z) L (z' j)) = c' • fun j => algebraMap K L (y j) :=
    funext fun j => Subtype.ext rfl
  have hz' : z' ≠ 0 := fun h => smul_ne_zero hc' hyL (by
    rw [← he, h]; exact funext fun j => map_zero _)
  have h1 := GlobalTheory.T.normalizedPointHeightLattice_algebraMap F (coordField F z) N n w A hw hA L z' hz'
  have h2 := GlobalTheory.T.normalizedPointHeightLattice_smul F L N n w A hw hA _ c' hyL hc'
  have h3 := GlobalTheory.T.normalizedPointHeightLattice_algebraMap F K N n w A hw hA L y hy
  rw [he, h2, h3] at h1
  exact h1.symm

end GlobalTheory.Adelic
