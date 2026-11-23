module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.ExpEqOfHasDerivAt

@[expose] public section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

theorem UpperTheory.finiteDimensional_span_maximalCompact_translates_of_fix :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (f : G1 K n → ℂ), Continuous f → D.Fix f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K n => fun m => f (m * k))) := by
  intro K _ _ n D f hf hfix
  obtain ⟨-, -, 𝒜, hfd, -, hA⟩ := typeFin D
  haveI := hfd
  obtain ⟨O, hO, hUO⟩ := D.isOpen
  haveI : CompactSpace (KG K n) :=
    isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 n).1
  let W : Subgroup (KG K n) := D.U.subgroupOf (KG K n)
  have hWo : IsOpen (W : Set (KG K n)) := by
    have hW : (W : Set (KG K n)) = (fun k : KG K n => ((k : G1 K n) : AdelicGLn.AdelicGL K n)) ⁻¹' O := by
      ext k
      exact ⟨fun h => ((hUO k).1 h).1, fun h => (hUO k).2 ⟨h, k.2⟩⟩
    rw [hW]
    exact hO.preimage (continuous_subtype_val.comp continuous_subtype_val)
  haveI : Finite (KG K n ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWo
  let B := Module.finBasis ℂ 𝒜
  let x : G1 K n → 𝒜 := fun m => ⟨fun u : D.U => f (m * u), hA f hf hfix m⟩
  let c : Fin (Module.finrank ℂ 𝒜) × (KG K n ⧸ W) → G1 K n → ℂ :=
    fun p m => B.repr (x (m * ((Quotient.out p.2 : KG K n) : G1 K n))) p.1
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range c)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul W k
  set q : KG K n ⧸ W := (k : KG K n ⧸ W) with hq
  let u : D.U := ⟨(((h : KG K n)⁻¹ : KG K n) : G1 K n), Subgroup.mem_subgroupOf.1 (W.inv_mem h.2)⟩
  have hk : (k : G1 K n) = ((Quotient.out q : KG K n) : G1 K n) * u := by
    have : k = Quotient.out q * (h : KG K n)⁻¹ := by
      rw [hh]; simp
    exact congrArg Subtype.val this
  have e : (fun m => f (m * k)) = ∑ i, ((B i : 𝒜) : D.U → ℂ) u • c (i, q) := by
    funext m
    have h1 := congrArg (fun y : 𝒜 => (y : D.U → ℂ) u)
      (B.sum_repr (x (m * ((Quotient.out q : KG K n) : G1 K n))))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk, ← mul_assoc]
    change _ = ∑ i, ((B i : 𝒜) : D.U → ℂ) u * B.repr (x (m * ((Quotient.out q : KG K n) : G1 K n))) i
    simp only [mul_comm (((B _ : 𝒜) : D.U → ℂ) u)]
    exact h1.symm
  change (fun m => f (m * (k : G1 K n))) ∈ Submodule.span ℂ (Set.range c)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, q), rfl⟩)
