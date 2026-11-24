module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGL
public import GroundTheory.AutomorphicForms.FourierWhittaker.UMatColXEqFromBlocks
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionSmoothRightInvariant
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGL, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGLStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlaces, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlacesStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericChar, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericCharStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlaces, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlacesStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtension, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtensionStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOne, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOneStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGLStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApply, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApplyStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionCompactSupportModuloUnipotent, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionWhittakerEquivariant, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplementStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGL =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGL", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) : idemS S * sInf E x = sInf E x :=
  Prod.ext (one_mul _) (mul_zero _)

theorem one_sub_idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) :
    (1 - idemS S) * sInf E x = 0 := by
  rw [sub_mul, one_mul, idemS_mul_sInf, sub_self]

theorem prS_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prS S a (infGL E a y) = infGL E a y := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) + sInf E (y i j)
  rw [mul_add, mul_sub, idemS_mul_sInf, idemS_mul_sInf]
  ring

theorem prO_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prO S a (infGL E a y) = 1 := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
  rw [mul_add, mul_sub, one_sub_idemS_mul_sInf, one_sub_idemS_mul_sInf]
  ring

theorem prS_prO_mul_infGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)),
    prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := by
  intro E _ _ _ a S g y
  refine ⟨?_, ?_⟩
  · rw [map_mul, prS_infGL]
  · rw [map_mul, prO_infGL, mul_one]

end GlobalTheory.SchurExt
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGL =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGLStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGLStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGL\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGLStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlaces =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlaces", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem fst_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : (idemS S : Ad E).1 = 1 := rfl

open Classical in
theorem pLoc_pFin_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) :
    pLoc E w (pFin E (idemS S)) = if w ∈ S then 1 else 0 := rfl

theorem prS_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (g : GA E a) (i j : Fin a) :
    (prS S a g : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
        idemS S * (g : Matrix (Fin a) (Fin a) (Ad E)) i j := rfl

theorem prO_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (g : GA E a) (i j : Fin a) :
    (prO S a g : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
        (1 - idemS S) * (g : Matrix (Fin a) (Fin a) (Ad E)) i j := rfl

theorem pLoc_pFin_idemS_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) :
    pLoc E w (pFin E (idemS S)) = 0 := by
  classical
  rw [pLoc_pFin_idemS]; simp [hw]

theorem pLoc_pFin_one_sub_idemS_of_mem {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S) :
    pLoc E w (pFin E (1 - idemS S)) = 0 := by
  classical
  rw [map_sub, map_sub, map_one, map_one, pLoc_pFin_idemS]; simp [hw]

theorem one_sub_idemS_mul_eq_zero {S : Finset (HeightOneSpectrum (𝓞 E))} {x : Ad E}
    (h : ∀ w ∉ S, pLoc E w (pFin E x) = 0) : (1 - idemS S) * x = 0 := by
  refine Prod.ext ?_ (Subtype.ext (funext fun w => ?_))
  · change (1 - (idemS S : Ad E).1) * x.1 = 0
    rw [fst_idemS, sub_self, zero_mul]
  · change pLoc E w (pFin E ((1 - idemS S) * x)) = pLoc E w (pFin E 0)
    rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hw : w ∈ S
    · rw [pLoc_pFin_one_sub_idemS_of_mem hw, zero_mul]
    · rw [h w hw, mul_zero]

theorem pLoc_pFin_one_apply (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (i j : Fin a) :
    pLoc E w (pFin E ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem pLoc_pFin_apply_of_mem_supS {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E a}
    (hg : g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) (i j : Fin a) :
    pLoc E w (pFin E ((g : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
  have h := congrArg (fun x : GL (Fin a) (w.adicCompletion E) => (x : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) (hg w hw)
  exact h

theorem one_sub_idemS_mul_sub_eq_zero {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E a}
    (hg : g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) (i j : Fin a) :
    (1 - idemS S) * ((g : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 : Matrix (Fin a) (Fin a) (Ad E)) i j) = 0 :=
  one_sub_idemS_mul_eq_zero fun w hw => by
    rw [map_sub, map_sub, pLoc_pFin_apply_of_mem_supS hg hw, pLoc_pFin_one_apply, sub_self]

theorem prS_prO_supS (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  refine ⟨fun g hg => ⟨?_, ?_⟩, fun g w hw => ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [prS_apply]
    linear_combination (-1 : Ad E) * one_sub_idemS_mul_sub_eq_zero hg i j
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [prO_apply]
    change _ = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
    linear_combination (one_sub_idemS_mul_sub_eq_zero hg i j)
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change pLoc E w (pFin E ((prS S a g : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
    rw [prS_apply, map_add (f := _), map_sub, map_mul, map_mul, map_add (f := _), map_sub, map_mul, map_mul,
      pLoc_pFin_idemS_of_not_mem hw, pLoc_pFin_one_apply]
    ring

end GlobalTheory.SchurExt
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlaces =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlacesStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlacesStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlaces\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlacesStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericChar =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericChar", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem coe_cornerGL_idemHom_apply {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a (idemHom e he) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j =
      (1 : Matrix (Fin a) (Fin a) R) i j - e * (1 : Matrix (Fin a) (Fin a) R) i j + e * (g : Matrix (Fin a) (Fin a) R) i j :=
  rfl

theorem cornerGL_idemHom_mem_NA {a : ℕ} (e : Ad E) (he : IsIdempotentElem e) {u : GA E a}
    (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := a)) : cornerGL a (idemHom e he) u ∈ GlobalTheory.JSW.NA (E := E) (a := a) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_cornerGL_idemHom_apply, hu.1 i j hij, Matrix.one_apply_ne (ne_of_lt hij).symm]
    ring
  · rw [coe_cornerGL_idemHom_apply, hu.2 i, Matrix.one_apply_eq]
    ring

theorem cornerGL_idemHom_add_apply {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) {i j : Fin a} (hij : i ≠ j) :
    ((cornerGL a (idemHom e he) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j +
      ((cornerGL a (idemHom (1 - e) he.one_sub) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j =
      (g : Matrix (Fin a) (Fin a) R) i j := by
  rw [coe_cornerGL_idemHom_apply, coe_cornerGL_idemHom_apply, Matrix.one_apply_ne hij]
  ring

theorem superDiag_cornerGL_idemHom_add {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) :
    GlobalTheory.Whittaker.superDiag (cornerGL a (idemHom e he) g) +
      GlobalTheory.Whittaker.superDiag (cornerGL a (idemHom (1 - e) he.one_sub) g) = GlobalTheory.Whittaker.superDiag g := by
  unfold GlobalTheory.Whittaker.superDiag
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j.val = i.val + 1 := (Finset.mem_filter.1 hj).2
  have hij : i ≠ j := fun h => by rw [h] at hj'; omega
  exact cornerGL_idemHom_add_apply e he g hij

theorem prS_prO_NA_psiN :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
      ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := a), prS S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧ prO S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧
        GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := by
  intro E _ _ _ a S u hu
  refine ⟨cornerGL_idemHom_mem_NA _ _ hu, cornerGL_idemHom_mem_NA _ _ hu, ?_⟩
  unfold GlobalTheory.JSW.psiN
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  exact congrArg (fun x => ((GroundTheory.Global.adelicChar E x : Circle) : ℂ))
    (superDiag_cornerGL_idemHom_add (idemS S) (isIdempotentElem_idemS S) u)

end GlobalTheory.SchurExt
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericChar =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericCharStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericCharStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericChar\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericCharStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlaces =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlaces", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem blockGL_mem_supS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S := by
  intro E _ _ m r S h hh w hw
  have hmap : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E))
      (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1)
        (Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) h) :=
    Units.ext (GroundTheory.Automorphic.FourierWhittaker.map_blockMat _ _ (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)))
  rw [hmap, hh w hw, map_one]

end GlobalTheory.SchurExt
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlaces =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlacesStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlacesStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlaces\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.blockDiagGL_mem_adelicGLSupportedAtFinitePlaces : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S := by
  first | (exact @GlobalTheory.SchurExt.blockGL_mem_supS)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlacesStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtension =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtension", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt.SmoothPart

section Calc

variable {K : Type} [NormedCommRing K] [NormedAlgebra ℝ K] [CompleteSpace K]
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X}

theorem ent_mul {p k q : ℕ} {f : X → Matrix (Fin p) (Fin k) K} {g : X → Matrix (Fin k) (Fin q) K}
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) s) :
    ∀ i j, ContDiffOn ℝ ∞ (fun x => (f x * g x) i j) s := by
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (hf i l).mul (hg l j)

theorem ent_sub {p q : ℕ} {f g : X → Matrix (Fin p) (Fin q) K}
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) s) :
    ∀ i j, ContDiffOn ℝ ∞ (fun x => (f x - g x) i j) s := fun i j => (hf i j).sub (hg i j)

theorem det_sm {p : ℕ} {f : X → Matrix (Fin p) (Fin p) K} (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) :
    ContDiffOn ℝ ∞ (fun x => (f x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hf _ _)

theorem ent_inv {p : ℕ} {f : X → Matrix (Fin p) (Fin p) K} (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s)
    (hu : ∀ x ∈ s, IsUnit (f x).det) : ∀ i j, ContDiffOn ℝ ∞ (fun x => (f x)⁻¹ i j) s := by
  intro i j
  have hd := det_sm hf
  have hi : ContDiffOn ℝ ∞ (fun x => Ring.inverse (f x).det) s := fun x hx => by
    obtain ⟨u, hu'⟩ := hu x hx
    have h1 : ContDiffAt ℝ ∞ Ring.inverse (u : K) := contDiffAt_ringInverse ℝ u
    rw [hu'] at h1
    exact h1.comp_contDiffWithinAt x (hd x hx)
  have ha : ContDiffOn ℝ ∞ (fun x => (f x).adjugate i j) s := by
    simp only [Matrix.adjugate_apply]
    refine det_sm fun k l => ?_
    by_cases hk : k = j
    · subst hk; simp only [Matrix.updateRow_self]; exact contDiffOn_const
    · simp only [Matrix.updateRow_ne hk]; exact hf k l
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  exact hi.mul ha

end Calc

section Maps

variable {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) {m r : ℕ}

theorem map_inv_of {k : ℕ} (N : Matrix (Fin k) (Fin k) R) (h : IsUnit N.det) : N⁻¹.map p = (N.map p)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one _ (map_zero p) (map_one p)]

theorem map_Xof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    (Xof M).map p = Xof (M.map p) := by
  rw [Xof, Xof, Matrix.map_mul, map_inv_of p _ h]; rfl

theorem map_Yof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    (Yof M).map p = Yof (M.map p) := by
  rw [Yof, Yof, Matrix.map_mul, map_inv_of p _ h]; rfl

theorem map_Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    (Scof M).map p = Scof (M.map p) := by
  rw [Scof, Scof, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, map_inv_of p _ h]; rfl

theorem map_Dof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (Dof M).map p = Dof (M.map p) := rfl

theorem det_Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (hM : IsUnit M.det)
    (hD : IsUnit (Dof M).det) : IsUnit (Scof M).det := by
  letI := (blk M).toBlocks₂₂.invertibleOfIsUnitDet hD
  have h1 : M.det = (Dof M).det * (Scof M).det := by
    rw [← Matrix.det_submatrix_equiv_self (eqv m r).symm M]
    have := Matrix.det_fromBlocks₂₂ (blk M).toBlocks₁₁ (blk M).toBlocks₁₂ (blk M).toBlocks₂₁ (blk M).toBlocks₂₂
    rw [Matrix.fromBlocks_toBlocks] at this
    rw [show M.submatrix (eqv m r).symm (eqv m r).symm = blk M from rfl, this, Matrix.invOf_eq_nonsing_inv]
    rfl
  rw [h1] at hM
  exact isUnit_of_mul_isUnit_right hM

end Maps

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem isUnit_ad_iff (a : Ad E) : IsUnit a ↔ IsUnit (pInf E a) ∧ IsUnit (pFin E a) := by
  change IsUnit a ↔ IsUnit ((infEq E).symm a.1) ∧ IsUnit a.2
  rw [isUnit_map_iff]
  exact Prod.isUnit_iff (x := (a : InfiniteAdeleRing E × Af E))

theorem mkGL_split {k : ℕ} (N : Matrix (Fin k) (Fin k) (Ad E)) (h : IsUnit N.det) :
    mkGL N = infGL E k (mkGL (N.map (pInf E))) * finGL E k (mkGL (N.map (pFin E))) := by
  have hi : IsUnit (N.map (pInf E)).det := by rw [show (N.map _).det = _ from (RingHom.map_det _ N).symm]; exact h.map _
  have hf : IsUnit (N.map (pFin E)).det := by rw [show (N.map _).det = _ from (RingHom.map_det _ N).symm]; exact h.map _
  refine ga_ext ?_ ?_
  · rw [map_mul, pInf_infGL, pInf_finGL, mul_one]
    apply Units.ext
    change (mkGL N : Matrix (Fin k) (Fin k) (Ad E)).map (pInf E) = _
    rw [coe_mkGL h, coe_mkGL hi]
  · rw [map_mul, pFin_infGL, pFin_finGL, one_mul]
    apply Units.ext
    change (mkGL N : Matrix (Fin k) (Fin k) (Ad E)).map (pFin E) = _
    rw [coe_mkGL h, coe_mkGL hf]

theorem apply_mkGL {k : ℕ} (φ : GA E k → ℂ) (N : Matrix (Fin k) (Fin k) (Ad E)) (h : IsUnit N.det) :
    φ (mkGL N) = chart φ (finGL E k (mkGL (N.map (pFin E)))) (toL (N.map (pInf E))) := by
  have hi : IsUnit (N.map (pInf E)).det := by rw [show (N.map _).det = _ from (RingHom.map_det _ N).symm]; exact h.map _
  rw [mkGL_split N h, infGL_comm, ← chart_val φ (finGL E k _) (mkGL (N.map (pInf E))), coe_mkGL hi]

theorem psi_split (a : Ad E) :
    psi a = GlobalTheory.WhitBump.psiInf (pInf E a) * GlobalTheory.WhitBump.psiFin (pFin E a) := by
  have e : a = sInf E (pInf E a) + sFin E (pFin E a) := by
    refine ad_ext ?_ ?_
    · rw [map_add (f := _)]
      change pInf E a = (infEq E).symm (infEq E (pInf E a)) + (infEq E).symm 0
      simp
    · rw [map_add (f := _)]
      change pFin E a = 0 + pFin E a
      simp
  rw [psi]
  conv_lhs => rw [e]
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]
  rfl

theorem contDiff_psiInf : ContDiff ℝ ∞ (GlobalTheory.WhitBump.psiInf (E := E)) := by
  let T : Cinf E →+ ℝ := (GroundTheory.Global.infiniteTrace E).comp (infEq E).toAddMonoidHom
  have hT : Continuous T := (GroundTheory.Global.continuous_infiniteTrace E).comp (continuous_infEq E)
  let L := AddMonoidHom.toRealLinearMap T hT
  have e : ∀ z, GlobalTheory.WhitBump.psiInf z = Complex.exp (((2 * Real.pi * (-(L z)) : ℝ) : ℂ) * Complex.I) := fun z => by
    change ((GroundTheory.Global.adelicChar E ((infEq E z, 0) : InfiniteAdeleRing E × Af E)) : ℂ) = _
    rw [GroundTheory.Global.adelicChar_infinite, Real.fourierChar_apply]
    rfl
  rw [show GlobalTheory.WhitBump.psiInf (E := E) = fun z => Complex.exp (((2 * Real.pi * (-(L z)) : ℝ) : ℂ) * Complex.I) from funext e]
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul L.contDiff.neg)).mul contDiff_const)

theorem continuous_pInf_sm : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

variable {m r : ℕ}

theorem chart_schurF_eq (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ)
    (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (g : GA E (m + r + 1 + 1)) (x : Lie E (m + r + 1 + 1)) (hx : IsUnit (Matrix.of x))
    (hD : IsUnit (Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x)).det)
    (hDf : IsUnit (Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E))).det) :
    chart (schurF β b₁ χ) g x =
      GlobalTheory.WhitBump.psiInf (Xof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) (Fin.last m) 0) *
      GlobalTheory.WhitBump.psiFin (Xof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) (Fin.last m) 0) *
      chart β (finGL E _ (mkGL (Scof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)))))
        (toL (Scof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x))) *
      chart b₁ (finGL E _ (mkGL (Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)))))
        (toL (Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x))) *
      ((χ (fun i j => Yof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) i j) : ℂ) *
        (open Classical in if ∀ i j, Yof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) i j ∈
          GroundTheory.Global.integralFiniteAdeles (𝓞 E) E then 1 else 0)) := by
  set M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E) :=
    ((g * infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hMdef
  have hMi : M.map (pInf E) = (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x := by
    have h1 : ((infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) = Matrix.of x :=
      (congrArg Units.val (pInf_infGL hx.unit)).trans hx.unit_spec
    rw [hMdef, Units.val_mul, Matrix.map_mul, h1]
  have hMf : M.map (pFin E) = (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E) := by
    have h1 : ((infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E) = 1 :=
      congrArg Units.val (pFin_infGL hx.unit)
    rw [hMdef, Units.val_mul, Matrix.map_mul, h1, Matrix.mul_one]
  have hDM : IsUnit (Dof M).det := by
    rw [isUnit_ad_iff, RingHom.map_det, RingHom.map_det]
    exact ⟨by rw [RingHom.mapMatrix_apply, map_Dof, hMi]; exact hD,
      by rw [RingHom.mapMatrix_apply, map_Dof, hMf]; exact hDf⟩
  have hSM : IsUnit (Scof M).det :=
    det_Scof M ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)) hDM
  rw [chart, dite_eq_left hx]
  change schurF β b₁ χ (g * infGL E _ hx.unit) = _
  rw [schurF]
  rw [if_pos hDM, psi_split, apply_mkGL β _ hSM, apply_mkGL b₁ _ hDM, chiF]
  have e1 : pInf E (Xof M (Fin.last m) 0) = Xof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) (Fin.last m) 0 := by
    rw [← hMi, ← map_Xof _ M hDM, Matrix.map_apply]
  have e2 : pFin E (Xof M (Fin.last m) 0) = Xof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) (Fin.last m) 0 := by
    rw [← hMf, ← map_Xof _ M hDM, Matrix.map_apply]
  have e3 : (Scof M).map (pFin E) = Scof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) := by
    rw [map_Scof _ M hDM, hMf]
  have e4 : (Scof M).map (pInf E) = Scof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) := by
    rw [map_Scof _ M hDM, hMi]
  have e5 : (Dof M).map (pFin E) = Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) := by
    rw [map_Dof, hMf]
  have e6 : (Dof M).map (pInf E) = Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) := by
    rw [map_Dof, hMi]
  have e7 : (fun i j => pInf E (Yof M i j)) = fun i j => Yof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) i j := by
    funext i j; rw [← hMi, ← map_Yof _ M hDM, Matrix.map_apply]
  have e8 : ∀ i j, pFin E (Yof M i j) = Yof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) i j := by
    intro i j; rw [← hMf, ← map_Yof _ M hDM, Matrix.map_apply]
  have e9 : (∀ i j, pFin E (Yof M i j) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) =
      (∀ i j, Yof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) i j ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) :=
    propext (forall_congr' fun i => forall_congr' fun j => by rw [e8])
  rw [e1, e2, e3, e4, e5, e6, e7]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd (e9 ▸ h1) h2
  · exact absurd (e9 ▸ h2) h1
  · ring

theorem chart_schurF_zero (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ)
    (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ) (C : Set (GA E (r + 1)))
    (hC : ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C)
    (g : GA E (m + r + 1 + 1)) (x : Lie E (m + r + 1 + 1)) (hx : IsUnit (Matrix.of x))
    (hK : (Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x)).det ∉
      (fun c : GA E (r + 1) => pInf E (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)).det) '' C) :
    chart (schurF β b₁ χ) g x = 0 := by
  set M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E) :=
    ((g * infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hMdef
  have hMi : M.map (pInf E) = (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x := by
    have h1 : ((infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) = Matrix.of x :=
      (congrArg Units.val (pInf_infGL hx.unit)).trans hx.unit_spec
    rw [hMdef, Units.val_mul, Matrix.map_mul, h1]
  rw [chart, dite_eq_left hx]
  change schurF β b₁ χ (g * infGL E _ hx.unit) = 0
  rw [schurF]
  split_ifs with hDM
  · have hb : b₁ (mkGL (Dof M)) = 0 := by
      by_contra hne
      obtain ⟨u, hu, hc⟩ := hC _ hne
      apply hK
      refine ⟨_, hc, ?_⟩
      have hu1 : (u : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)).det = 1 := by
        rw [Matrix.det_of_upperTriangular (fun i j h => hu.1 i j h)]
        exact Finset.prod_eq_one fun i _ => hu.2 i
      have hu2 : ((u⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)).det = 1 := by
        have := congrArg Matrix.det (congrArg Units.val (inv_mul_cancel u))
        rw [Units.val_mul, Matrix.det_mul, hu1, mul_one, Units.val_one, Matrix.det_one] at this
        exact this
      change pInf E ((u⁻¹ * mkGL (Dof M) : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)).det = _
      rw [Units.val_mul, Matrix.det_mul, hu2, one_mul, coe_mkGL hDM, RingHom.map_det, RingHom.mapMatrix_apply,
        map_Dof, hMi]
    rw [hb]; ring
  · rfl

end GlobalTheory.SchurExt.SmoothPart

namespace GlobalTheory.SchurExt


open GlobalTheory.SchurExt.SmoothPart in
theorem contDiffOn_chart_schurF : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ)
    (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ),
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) → (∀ g, ContDiffOn ℝ ∞ (chart b₁ g) (invSet E (r + 1))) →
    (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) →
    ContDiff ℝ ∞ χ → ∀ g, ContDiffOn ℝ ∞ (chart (schurF β b₁ χ) g) (invSet E (m + r + 1 + 1)) := by
  intro E _ _ _ m r β b₁ χ hβ hb hC hχ g
  set Gi := (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) with hGi
  set Gf := (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E) with hGf
  by_cases hDf : IsUnit (Dof Gf).det
  swap
  · refine (contDiffOn_const (c := (0 : ℂ))).congr fun x hx0 => ?_
    have hx : IsUnit (Matrix.of x) := hx0
    rw [chart, dite_eq_left hx]
    change schurF β b₁ χ (g * infGL E _ hx.unit) = 0
    rw [schurF, if_neg]
    intro hDM
    apply hDf
    have h1 : ((infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E) = 1 :=
      congrArg Units.val (pFin_infGL hx.unit)
    have := ((isUnit_ad_iff _).1 hDM).2
    rwa [RingHom.map_det, RingHom.mapMatrix_apply, map_Dof, Units.val_mul, Matrix.map_mul, h1, Matrix.mul_one] at this
  obtain ⟨C, hCc, hCp⟩ := hC
  set K := (fun c : GA E (r + 1) => pInf E (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)).det) '' C with hK
  have hKc : IsCompact K := hCc.image (continuous_pInf_sm.comp (Continuous.matrix_det Units.continuous_val))
  have hKu : ∀ z ∈ K, IsUnit z := by
    rintro _ ⟨c, -, rfl⟩
    exact ((Matrix.isUnit_iff_isUnit_det _).1 c.isUnit).map _
  have hf0 : ∀ i j, ContDiffOn ℝ ∞ (fun x : Lie E (m + r + 1 + 1) => (Gi * Matrix.of x) i j) Set.univ :=
    ent_mul (fun _ _ => contDiffOn_const) (fun i j => ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i)).contDiffOn)
  set φ := fun x : Lie E (m + r + 1 + 1) => (Dof (Gi * Matrix.of x)).det with hφ
  have hφc : Continuous φ := (contDiffOn_univ.1 (det_sm fun i j => hf0 _ _)).continuous
  have hGu : IsUnit Gi.det := by
    rw [hGi, show (Gi).det = _ from (RingHom.map_det _ _).symm]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).map _
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  by_cases hu : IsUnit (φ x)
  · refine ⟨{x | IsUnit (φ x)}, Units.isOpen.preimage hφc, hu, ?_⟩
    set s := invSet E (m + r + 1 + 1) ∩ {x | IsUnit (φ x)} with hs
    have hf : ∀ i j, ContDiffOn ℝ ∞ (fun x : Lie E (m + r + 1 + 1) => (Gi * Matrix.of x) i j) s :=
      fun i j => (hf0 i j).mono (Set.subset_univ _)
    have hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => Aof (Gi * Matrix.of x) i j) s := fun i j => hf _ _
    have hB : ∀ i j, ContDiffOn ℝ ∞ (fun x => Bof (Gi * Matrix.of x) i j) s := fun i j => hf _ _
    have hCm : ∀ i j, ContDiffOn ℝ ∞ (fun x => Cof (Gi * Matrix.of x) i j) s := fun i j => hf _ _
    have hD : ∀ i j, ContDiffOn ℝ ∞ (fun x => Dof (Gi * Matrix.of x) i j) s := fun i j => hf _ _
    have hDi := ent_inv hD fun x hx => hx.2
    have hX := ent_mul hB hDi
    have hS := ent_sub hA (ent_mul (ent_mul hB hDi) hCm)
    have hY := ent_mul hDi hCm
    have t1 : ContDiffOn ℝ ∞ (fun x => GlobalTheory.WhitBump.psiInf (Xof (Gi * Matrix.of x) (Fin.last m) 0)) s :=
      contDiff_psiInf.comp_contDiffOn (hX _ _)
    have t2 : ContDiffOn ℝ ∞ (fun x => chart β (finGL E _ (mkGL (Scof Gf))) (toL (Scof (Gi * Matrix.of x)))) s :=
      (hβ _).comp (contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => hS i j) fun x hx' => by
        show IsUnit (Scof (Gi * Matrix.of x))
        rw [Matrix.isUnit_iff_isUnit_det]
        refine det_Scof _ ?_ hx'.2
        rw [Matrix.det_mul]
        exact hGu.mul ((Matrix.isUnit_iff_isUnit_det _).1 hx'.1)
    have t3 : ContDiffOn ℝ ∞ (fun x => chart b₁ (finGL E _ (mkGL (Dof Gf))) (toL (Dof (Gi * Matrix.of x)))) s :=
      (hb _).comp (contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => hD i j) fun x hx' =>
        (Matrix.isUnit_iff_isUnit_det _).2 hx'.2
    have t4 : ContDiffOn ℝ ∞ (fun x => (χ (fun i j => Yof (Gi * Matrix.of x) i j) : ℂ)) s :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        (hχ.comp_contDiffOn (contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => hY i j))
    refine ((((t1.mul (contDiffOn_const (c := GlobalTheory.WhitBump.psiFin (Xof Gf (Fin.last m) 0)))).mul t2).mul t3).mul
      (t4.mul (contDiffOn_const (c := (open Classical in
        if ∀ i j, Yof Gf i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E then (1 : ℂ) else 0))))).congr fun x hx' => ?_
    exact chart_schurF_eq β b₁ χ g x hx'.1 hx'.2 hDf
  · refine ⟨φ ⁻¹' Kᶜ, hKc.isClosed.isOpen_compl.preimage hφc, fun hk => hu (hKu _ hk), ?_⟩
    exact (contDiffOn_const (c := (0 : ℂ))).congr fun x hx' => chart_schurF_zero β b₁ χ C hCp g x hx'.1 hx'.2

end GlobalTheory.SchurExt
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtension =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtensionStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtensionStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtension\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtensionStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOne =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOne", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section
namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem prS_finGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (k : GL (Fin a) (Af E)) :
    prS S a (finGL E a k) = finGL E a (prSf S a k) := by
  have hI : ∀ y, idemS S * sFin E y = sFin E (idemSf S * y) := fun y => Prod.ext (mul_zero _) rfl
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      + idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
        + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
      + sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - idemSf S * (1 : Matrix (Fin a) (Fin a) (Af E)) i j
        + idemSf S * k i j)
  generalize idemS S = I at hI ⊢
  generalize idemSf S = J at hI ⊢
  simp only [Matrix.one_apply]
  split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add (f := _), mul_add, mul_sub, hI, sub_zero,
    zero_add] <;> ring

theorem prO_finGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (k : GL (Fin a) (Af E)) :
    prO S a (finGL E a k) = finGL E a (prOf S a k) := by
  have hI : ∀ y, (1 - idemS S) * sFin E y = sFin E ((1 - idemSf S) * y) := fun y => Prod.ext (mul_zero _) rfl
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      + (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
        + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
      + sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - (1 - idemSf S) * (1 : Matrix (Fin a) (Fin a) (Af E)) i j
        + (1 - idemSf S) * k i j)
  generalize (1 - idemS S) = I at hI ⊢
  generalize (1 - idemSf S) = J at hI ⊢
  simp only [Matrix.one_apply]
  split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add (f := _), mul_add, mul_sub, hI, sub_zero,
    zero_add] <;> ring

theorem continuous_cornerGL_idemHom (a : ℕ) (e : Af E) (he : IsIdempotentElem e) :
    Continuous (cornerGL a (idemHom e he)) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => 1 - matN a (idemHom e he) 1 + matN a (idemHom e he) x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_const.mul continuous_id : Continuous fun x : Af E => e * x).comp
      ((continuous_apply j).comp (continuous_apply i))

theorem continuous_prSf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : Continuous (prSf S a) :=
  continuous_cornerGL_idemHom a _ _

theorem continuous_prOf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : Continuous (prOf S a) :=
  continuous_cornerGL_idemHom a _ _

end GlobalTheory.SchurExt

theorem GlobalTheory.SchurExt.eventually_prS_prO_finGL :
    ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := by
  intro E _ _ a S V V' hV hV'
  have h1 := (continuous_prSf S a).tendsto 1
  have h2 := (continuous_prOf S a).tendsto 1
  rw [map_one] at h1 h2
  filter_upwards [h1 hV, h2 hV'] with k hk hk'
  exact ⟨⟨_, hk, prS_finGL S a k⟩, _, hk', prO_finGL S a k⟩
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOne =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOneStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOneStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOneStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGLStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGLStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGL\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGLStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApply =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApply", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.UMatColXEqFromBlocks\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem schurSquareMatrixToBlocks_blockDiagonal_one {R : Type} [CommRing R] (m r : ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    blk (GroundTheory.Automorphic.FourierWhittaker.blockMat (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      Matrix.fromBlocks h 0 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blk, eqv, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, Matrix.one_apply, Fin.ext_iff]
  all_goals
    have hi := i.isLt
    have hj := j.isLt
    try intro
    split_ifs <;> first | rfl | (exfalso; omega)

theorem schurF_blockGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ)
    (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (h : GA E (m + 1)) :
    schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      β h * b₁ 1 * (χ 0 : ℂ) := by
  classical
  have hb := schurSquareMatrixToBlocks_blockDiagonal_one (R := Ad E) m r (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))
  have hD : Dof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 1 := by
    rw [Dof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₂]
  have hA : Aof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = h := by
    rw [Aof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₁]
  have hB : Bof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Bof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₂]
  have hC : Cof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Cof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₁]
  have hmk : mkGL (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) = h :=
    Units.ext (coe_mkGL (Matrix.isUnits_det_units h))
  have hmk1 : mkGL (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) = 1 :=
    Units.ext (by rw [coe_mkGL (by simp)]; rfl)
  have hpsi : psi (0 : Ad E) = 1 := by
    simp [psi]
  have hchi : chiF (m := m) (r := r) χ 0 = (χ 0 : ℂ) := by
    have h0 : (fun i j => pInf E ((0 : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) i j)) = 0 := by
      funext i j; simp
    rw [chiF, h0]
    simp [zero_mem]
  rw [schurF, if_pos (by rw [hD]; simp), Xof, Scof, Yof, hA, hB, hC, hD]
  simp only [inv_one, Matrix.mul_one, Matrix.mul_zero, sub_zero, Matrix.zero_apply]
  rw [hpsi, hmk, hmk1, hchi, one_mul]

end GlobalTheory.SchurExt
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApply =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApplyStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApplyStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.UMatColXEqFromBlocks\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApply\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.schurComplementExtensionFunction_blockDiag_apply : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), ∀ h : GA E (m + 1), schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h * b₁ 1 * (χ 0 : ℂ) := by
  first | (exact @GlobalTheory.SchurExt.schurF_blockGL)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApplyStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionCompactSupportModuloUnipotent =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionCompactSupportModuloUnipotent", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExtCpt

open Matrix

section Mat

variable {R : Type} [CommRing R] {m r : ℕ}

theorem eqv_symm_inl_val (a : Fin (m + 1)) : (((eqv m r).symm (Sum.inl a)) : ℕ) = a := by simp [eqv]

theorem eqv_symm_inr_val (b : Fin (r + 1)) : (((eqv m r).symm (Sum.inr b)) : ℕ) = m + 1 + b := by simp [eqv]

theorem unblk_mul (P Q : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    unblk P * unblk Q = unblk (P * Q) := by
  unfold unblk; exact Matrix.submatrix_mul_equiv P Q _ _ _

theorem unblk_one : (unblk (1 : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R)) = 1 := by
  unfold unblk; exact Matrix.submatrix_one_equiv _

theorem fromBlocks_decomp {a b : ℕ} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin b) R)
    (C : Matrix (Fin b) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) (uA cA : Matrix (Fin a) (Fin a) R)
    (uD cD : Matrix (Fin b) (Fin b) R) (hD : IsUnit D.det) (hA : uA * cA = A - B * D⁻¹ * C) (hD' : uD * cD = D) :
    fromBlocks uA (B * D⁻¹ * uD) 0 uD * fromBlocks cA 0 (cD * (D⁻¹ * C)) cD = fromBlocks A B C D := by
  rw [fromBlocks_multiply]
  have h1 : B * D⁻¹ * uD * (cD * (D⁻¹ * C)) = B * D⁻¹ * C := by
    rw [Matrix.mul_assoc (B * D⁻¹) uD, ← Matrix.mul_assoc uD, hD', Matrix.mul_nonsing_inv_cancel_left _ _ hD]
  have h2 : B * D⁻¹ * uD * cD = B := by
    rw [Matrix.mul_assoc (B * D⁻¹) uD, hD', Matrix.nonsing_inv_mul_cancel_right _ _ hD]
  have h3 : uD * (cD * (D⁻¹ * C)) = C := by
    rw [← Matrix.mul_assoc, hD', Matrix.mul_nonsing_inv_cancel_left _ _ hD]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, h1, h2, h3, hD', hA, sub_add_cancel]

end Mat

variable {E : Type} [Field E] [NumberField E] {m r : ℕ}

def gEl (a : GA E (m + 1)) (d : GA E (r + 1)) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) : GA E (m + r + 1 + 1) where
  val := unblk (fromBlocks (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0 ((d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) * Y) d)
  inv := unblk (fromBlocks ((a⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0
    (-(Y * ((a⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)))) ((d⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)))
  val_inv := by
    rw [unblk_mul, fromBlocks_multiply, ← unblk_one, ← fromBlocks_one]
    congr 1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Units.mul_inv, Matrix.mul_neg, Matrix.mul_assoc,
      add_neg_cancel, neg_zero]
  inv_val := by
    rw [unblk_mul, fromBlocks_multiply, ← unblk_one, ← fromBlocks_one]
    congr 1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Units.inv_mul, Matrix.neg_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc ((d⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) (d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)),
      Matrix.mul_one, Matrix.one_mul, neg_add_cancel]

theorem coe_gEl (a : GA E (m + 1)) (d : GA E (r + 1)) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) :
    ((gEl a d Y : GA E (m + r + 1 + 1)) : Matrix _ _ (Ad E)) =
      unblk (fromBlocks (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0 ((d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) * Y) d) := rfl

theorem continuous_gEl :
    Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => gEl z.1 z.2.1 z.2.2 := by
  rw [Units.continuous_iff]
  have ha : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.1 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := Units.continuous_val.comp continuous_fst
  have ha' : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.1⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := Units.continuous_coe_inv.comp continuous_fst
  have hd : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.2.1 : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_snd)
  have hd' : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.2.1⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_snd)
  have hY : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => z.2.2 :=
    continuous_snd.comp continuous_snd
  have h0 : Continuous fun _ : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      (0 : Matrix (Fin (m + 1)) (Fin (r + 1)) (Ad E)) := continuous_const
  constructor
  · exact (Continuous.matrix_fromBlocks ha h0 (hd.matrix_mul hY) hd).matrix_submatrix _ _
  · exact (Continuous.matrix_fromBlocks ha' h0 (hY.matrix_mul ha').neg hd').matrix_submatrix _ _

theorem mem_NA_of_blocks (uA : GA E (m + 1)) (uD : GA E (r + 1)) (huA : uA ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)))
    (huD : uD ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1))) (X : Matrix (Fin (m + 1)) (Fin (r + 1)) (Ad E)) (u : GA E (m + r + 1 + 1))
    (hu : (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) =
      unblk (fromBlocks (uA : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) X 0 (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)))) :
    u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩ <;> rw [hu]
  · obtain ⟨x, rfl⟩ := (eqv m r).symm.surjective i
    obtain ⟨y, rfl⟩ := (eqv m r).symm.surjective j
    simp only [unblk, submatrix_apply, Equiv.apply_symm_apply]
    rw [Fin.lt_iff_val_lt_val] at hij
    rcases x with a | a <;> rcases y with b | b
    · simp only [eqv_symm_inl_val] at hij
      rw [fromBlocks_apply₁₁]; exact huA.1 a b (Fin.lt_iff_val_lt_val.2 hij)
    · simp only [eqv_symm_inl_val, eqv_symm_inr_val] at hij
      exact absurd hij (by have := a.isLt; omega)
    · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    · simp only [eqv_symm_inr_val] at hij
      rw [fromBlocks_apply₂₂]; exact huD.1 a b (Fin.lt_iff_val_lt_val.2 (by omega))
  · obtain ⟨x, rfl⟩ := (eqv m r).symm.surjective i
    simp only [unblk, submatrix_apply, Equiv.apply_symm_apply]
    rcases x with a | a
    · rw [fromBlocks_apply₁₁]; exact huA.2 a
    · rw [fromBlocks_apply₂₂]; exact huD.2 a

variable [_root_.NumberField.IsTotallyComplex E]

def adOf (z : (Fin (r + 1) → Fin (m + 1) → Cinf E) × (Fin (r + 1) → Fin (m + 1) → Af E)) :
    Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) :=
  fun i j => ((infEq E (z.1 i j), z.2 i j) : InfiniteAdeleRing E × Af E)

theorem continuous_adOf : Continuous (adOf (E := E) (m := m) (r := r)) := by
  refine continuous_matrix fun i j => ?_
  exact ((continuous_infEq E).comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))).prodMk
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

end GlobalTheory.SchurExtCpt


open Matrix GlobalTheory.SchurExtCpt in
theorem GlobalTheory.SchurExtCpt.exists_compact_support : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → HasCompactSupport χ → ∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), schurF β b₁ χ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C := by
  intro E _ _ _ m r S β b₁ χ ⟨Cβ, hCβ, hβ⟩ ⟨C₁, hC₁, hb⟩ hχ
  let K : Set (Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) := adOf ''
    (tsupport χ ×ˢ Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)))
  have hK : IsCompact K := (hχ.isCompact.prod (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    GroundTheory.Global.isCompact_integralFiniteAdeles E)).image continuous_adOf
  refine ⟨(fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => gEl z.1 z.2.1 z.2.2) ''
    (Cβ ×ˢ C₁ ×ˢ K), (hCβ.prod (hC₁.prod hK)).image continuous_gEl, ?_⟩
  intro p hp hF
  by_cases hD : IsUnit (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det
  swap
  · exact absurd (by unfold schurF; rw [if_neg hD]) hF
  unfold schurF at hF
  rw [if_pos hD] at hF
  obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := (mul_ne_zero_iff.1 hF) |>.imp (mul_ne_zero_iff.1) id |>.imp (fun h => h.imp mul_ne_zero_iff.1 id) id

  have hdet : IsUnit (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
    haveI : Invertible (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).toBlocks₂₂ :=
      Matrix.invertibleOfIsUnitDet _ hD
    have he : (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det =
        (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det *
          (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
      rw [← Matrix.det_submatrix_equiv_self (eqv m r).symm (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))]
      change (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det = _
      rw [← Matrix.fromBlocks_toBlocks (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))),
        Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
      rfl
    have hu := Matrix.isUnits_det_units p
    rw [he] at hu
    exact isUnit_of_mul_isUnit_right hu

  have hsup : mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
    intro w hw
    have hpw := congrArg Units.val (hp.1 w hw)
    apply Units.ext
    change (mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map ((pLoc E w).comp (pFin E)) = 1
    change (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map ((pLoc E w).comp (pFin E)) = 1 at hpw
    rw [coe_mkGL hdet]
    have hbl : (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 1 := by
      rw [show (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        blk ((p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map ((pLoc E w).comp (pFin E))) from rfl, hpw]
      exact Matrix.submatrix_one_equiv _
    have hA : (Aof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 1 := by
      rw [show (Aof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        ((blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E))).toBlocks₁₁ from rfl,
        hbl, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]
    have hB : (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 0 := by
      rw [show (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        ((blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E))).toBlocks₁₂ from rfl,
        hbl, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂]
    unfold Scof
    rw [Matrix.map_sub _ (map_sub ((pLoc E w).comp (pFin E))), Matrix.map_mul, Matrix.map_mul, hA, hB]
    simp
  obtain ⟨uA, huA, hcA⟩ := hβ _ hsup h2
  obtain ⟨uD, huD, hcD⟩ := hb _ h3

  have hY : Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) ∈ K := by
    unfold chiF at h4
    obtain ⟨h41, h42⟩ := mul_ne_zero_iff.1 h4
    have hint : ∀ i j, pFin E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
      by_contra hc
      rw [if_neg hc] at h42
      exact h42 rfl
    refine ⟨(fun i j => pInf E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j),
      fun i j => pFin E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)), ⟨subset_tsupport _ ?_, ?_⟩, ?_⟩
    · intro h
      apply h41
      rw [h]
      simp
    · simp only [Set.mem_univ_pi]
      exact fun i j => hint i j
    · funext i j
      refine ad_ext ?_ rfl
      show (infEq E).symm (infEq E _) = _
      exact RingEquiv.symm_apply_apply _ _
  refine ⟨p * (gEl (uA⁻¹ * mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
    (uD⁻¹ * mkGL (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
    (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))⁻¹, ?_, ⟨(_, _, _), ⟨hcA, hcD, hY⟩, ?_⟩⟩
  · refine mem_NA_of_blocks uA uD huA huD (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) *
      (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ * (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) _ ?_
    have hpU : (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) =
        unblk (fromBlocks (uA : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) *
          (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ * (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) 0
          (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) *
        ((gEl (uA⁻¹ * mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
          (uD⁻¹ * mkGL (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
          (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) : GA E (m + r + 1 + 1)) :
            Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) := by
      rw [coe_gEl, unblk_mul]
      conv_lhs => rw [← unblk_blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))]
      congr 1
      rw [← Matrix.fromBlocks_toBlocks (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))]
      refine (fromBlocks_decomp _ _ _ _ _ _ _ _ hD ?_ ?_).symm
      · rw [← Units.val_mul, mul_inv_cancel_left, coe_mkGL hdet]; try rfl
      · rw [← Units.val_mul, mul_inv_cancel_left, coe_mkGL hD]
    rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul]
    exact hpU
  · rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
    rfl
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionCompactSupportModuloUnipotent =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionWhittakerEquivariant =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionWhittakerEquivariant", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurEquiv

open Matrix

section Alg

variable {R : Type} [CommRing R]

def IsUT {n : ℕ} (U : Matrix (Fin n) (Fin n) R) : Prop := (∀ i j : Fin n, j < i → U i j = 0) ∧ ∀ i, U i i = 1

def sd {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : R := ∑ i : Fin n, ∑ j : Fin n, if j.val = i.val + 1 then M i j else 0

theorem superDiag_eq_sd {n : ℕ} (g : GL (Fin n) R) : GlobalTheory.Whittaker.superDiag g = sd (g : Matrix (Fin n) (Fin n) R) := by
  simp [GlobalTheory.Whittaker.superDiag, sd, Finset.sum_filter]

theorem det_of_isUT {n : ℕ} {U : Matrix (Fin n) (Fin n) R} (hU : IsUT U) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => hU.1 i j h)]
  simp [hU.2]

variable {m r : ℕ}

theorem eqv_symm_inl (i : Fin (m + 1)) : ((eqv m r).symm (Sum.inl i)).val = i.val := by simp [eqv]
theorem eqv_symm_inr (j : Fin (r + 1)) : ((eqv m r).symm (Sum.inr j)).val = m + 1 + j.val := by simp [eqv]

theorem blk_mul (M N : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : blk (M * N) = blk M * blk N :=
  (Matrix.submatrix_mul_equiv M N _ (eqv m r).symm _).symm

theorem blk_eq (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    blk M = fromBlocks (Aof M) (Bof M) (Cof M) (Dof M) := (fromBlocks_toBlocks _).symm

variable {U : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R}

theorem Cof_of_isUT (hU : IsUT U) : Cof U = 0 := by
  ext i j
  apply hU.1
  rw [Fin.lt_def, eqv_symm_inl, eqv_symm_inr]
  omega

theorem Aof_isUT (hU : IsUT U) : IsUT (Aof U) :=
  ⟨fun i j h => hU.1 _ _ (by rw [Fin.lt_def, eqv_symm_inl, eqv_symm_inl]; exact h), fun i => hU.2 _⟩

theorem Dof_isUT (hU : IsUT U) : IsUT (Dof U) :=
  ⟨fun i j h => hU.1 _ _ (by rw [Fin.lt_def, eqv_symm_inr, eqv_symm_inr]; rw [Fin.lt_def] at h; omega), fun i => hU.2 _⟩

variable (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R)

theorem blk_UM (hU : IsUT U) : blk (U * M) = fromBlocks (Aof U * Aof M + Bof U * Cof M) (Aof U * Bof M + Bof U * Dof M)
    (Dof U * Cof M) (Dof U * Dof M) := by
  rw [blk_mul, blk_eq U, blk_eq M, Cof_of_isUT hU, fromBlocks_multiply]
  simp

theorem Aof_mul (hU : IsUT U) : Aof (U * M) = Aof U * Aof M + Bof U * Cof M := by
  rw [Aof, blk_UM M hU, toBlocks_fromBlocks₁₁]
theorem Bof_mul (hU : IsUT U) : Bof (U * M) = Aof U * Bof M + Bof U * Dof M := by
  rw [Bof, blk_UM M hU, toBlocks_fromBlocks₁₂]
theorem Cof_mul (hU : IsUT U) : Cof (U * M) = Dof U * Cof M := by
  rw [Cof, blk_UM M hU, toBlocks_fromBlocks₂₁]
theorem Dof_mul (hU : IsUT U) : Dof (U * M) = Dof U * Dof M := by
  rw [Dof, blk_UM M hU, toBlocks_fromBlocks₂₂]

theorem isUnit_Dof_mul_iff (hU : IsUT U) : IsUnit (Dof (U * M)).det ↔ IsUnit (Dof M).det := by
  rw [Dof_mul M hU, det_mul, det_of_isUT (Dof_isUT hU), one_mul]

theorem Yof_mul (hU : IsUT U) : Yof (U * M) = Yof M := by
  have hu : IsUnit (Dof U).det := by rw [det_of_isUT (Dof_isUT hU)]; exact isUnit_one
  rw [Yof, Yof, Dof_mul M hU, Cof_mul M hU, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (Dof U)⁻¹,
    nonsing_inv_mul _ hu, Matrix.one_mul]

theorem Scof_mul (hU : IsUT U) (hD : IsUnit (Dof M).det) : Scof (U * M) = Aof U * Scof M := by
  have hu : IsUnit (Dof U).det := by rw [det_of_isUT (Dof_isUT hU)]; exact isUnit_one
  have h1 : (Dof M)⁻¹ * (Dof U)⁻¹ * (Dof U * Cof M) = (Dof M)⁻¹ * Cof M := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Dof U)⁻¹, nonsing_inv_mul _ hu, Matrix.one_mul]
  rw [Scof, Scof, Aof_mul M hU, Bof_mul M hU, Dof_mul M hU, Cof_mul M hU, Matrix.mul_inv_rev, Matrix.mul_assoc _ _ (Dof U * Cof M), h1]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Dof M) (Dof M)⁻¹ (Cof M), mul_nonsing_inv _ hD, Matrix.one_mul]
  abel

theorem Xof_mul (hU : IsUT U) (hD : IsUnit (Dof M).det) :
    Xof (U * M) = Aof U * Xof M * (Dof U)⁻¹ + Bof U * (Dof U)⁻¹ := by
  rw [Xof, Xof, Bof_mul M hU, Dof_mul M hU, Matrix.mul_inv_rev]
  simp only [Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Dof M) (Dof M)⁻¹ (Dof U)⁻¹, mul_nonsing_inv _ hD, Matrix.one_mul]

theorem inv_first_column_of_upper_triangular {n : ℕ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hV : IsUT V) (l : Fin (n + 1)) :
    V⁻¹ l 0 = if l = 0 then 1 else 0 := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  have h := congrFun (congrFun (nonsing_inv_mul V hu) l) 0
  rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (n + 1)), hV.2, mul_one, Matrix.one_apply] at h
  · exact h
  · intro k _ hk; rw [hV.1 k 0 (Fin.pos_iff_ne_zero.2 hk), mul_zero]
  · simp

theorem mul_first_column_of_unit_column {n k : ℕ} (N : Matrix (Fin k) (Fin (n + 1)) R) {P : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hP : ∀ l, P l 0 = if l = 0 then 1 else 0) (i : Fin k) : (N * P) i 0 = N i 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [hP]
  · intro l _ hl; simp [hP, hl]
  · simp

theorem lastRow_mul {n k : ℕ} {Q : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hQ : IsUT Q) (N : Matrix (Fin (n + 1)) (Fin k) R)
    (j : Fin k) : (Q * N) (Fin.last n) j = N (Fin.last n) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n), hQ.2, one_mul]
  · intro l _ hl; rw [hQ.1 _ _ (Fin.lt_last_iff_ne_last.2 hl), zero_mul]
  · simp

theorem Xof_mul_entry (hU : IsUT U) (hD : IsUnit (Dof M).det) :
    Xof (U * M) (Fin.last m) 0 = Xof M (Fin.last m) 0 + Bof U (Fin.last m) 0 := by
  rw [Xof_mul M hU hD, Matrix.add_apply, mul_first_column_of_unit_column _ (inv_first_column_of_upper_triangular (Dof_isUT hU)), mul_first_column_of_unit_column _ (inv_first_column_of_upper_triangular (Dof_isUT hU)),
    lastRow_mul (Aof_isUT hU)]

theorem sd_blocks (U : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    sd U = sd (Aof U) + Bof U (Fin.last m) 0 + sd (Dof U) := by
  have e : ∀ f : Fin (m + r + 1 + 1) → R, ∑ i, f i = ∑ a, f ((eqv m r).symm a) := fun f =>
    (Equiv.sum_comp (eqv m r).symm f).symm
  rw [sd, e]
  simp only [Fintype.sum_sum_type]
  simp_rw [e, Fintype.sum_sum_type, eqv_symm_inl, eqv_symm_inr]
  have h2 : ∑ i : Fin (m + 1), ∑ j : Fin (r + 1),
      (if m + 1 + j.val = i.val + 1 then U ((eqv m r).symm (Sum.inl i)) ((eqv m r).symm (Sum.inr j)) else 0) =
      Bof U (Fin.last m) 0 := by
    rw [Finset.sum_eq_single (Fin.last m), Finset.sum_eq_single (0 : Fin (r + 1))]
    · rw [if_pos (by simp)]; rfl
    · intro j _ hj; rw [if_neg]; intro h; apply hj; ext; simp at h ⊢; omega
    · simp
    · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; rw [if_neg]; intro h; apply hi; ext; simp; omega
    · simp
  have h3 : ∑ i : Fin (r + 1), ∑ j : Fin (m + 1),
      (if j.val = m + 1 + i.val + 1 then U ((eqv m r).symm (Sum.inr i)) ((eqv m r).symm (Sum.inl j)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; omega
  have h4 : ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
      (if m + 1 + j.val = m + 1 + i.val + 1 then U ((eqv m r).symm (Sum.inr i)) ((eqv m r).symm (Sum.inr j)) else 0) =
      sd (Dof U) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val = i.val + 1
    · rw [if_pos (by omega), if_pos h]; rfl
    · rw [if_neg (by omega), if_neg h]
  simp only [Finset.sum_add_distrib]
  rw [h2, h3, h4, zero_add]
  rfl

end Alg

end GlobalTheory.SchurEquiv

namespace GlobalTheory.SchurEquiv

open Matrix

section Adelic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem mkGL_mem_NA {V : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) : mkGL V ∈ GlobalTheory.JSW.NA (E := E) (a := k) := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  refine ⟨fun i j h => ?_, fun i => ?_⟩ <;> rw [coe_mkGL hu]
  · exact hV.1 i j h
  · exact hV.2 i

theorem mkGL_mul {V S : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) (hS : IsUnit S.det) :
    mkGL (V * S) = mkGL V * mkGL S := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  have hVS : IsUnit (V * S).det := by rw [det_mul]; exact hu.mul hS
  apply Units.ext
  rw [Units.val_mul, coe_mkGL hVS, coe_mkGL hu, coe_mkGL hS]

theorem psi_add (a b : Ad E) : psi (a + b) = psi a * psi b := by
  simp [psi, AddChar.map_add_eq_mul]

theorem psiN_mkGL {V : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) : GlobalTheory.JSW.psiN (mkGL V) = psi (sd V) := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  rw [GlobalTheory.JSW.psiN, superDiag_eq_sd, coe_mkGL hu]; rfl

theorem isUnit_Scof {m r : ℕ} (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (hM : IsUnit M.det)
    (hD : IsUnit (Dof M).det) : IsUnit (Scof M).det := by
  letI := (Dof M).invertibleOfIsUnitDet hD
  have h1 : M.det = (Dof M).det * (Scof M).det := by
    have e : (blk M).det = M.det := Matrix.det_submatrix_equiv_self _ _
    rw [← e, blk_eq, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]; rfl
  rw [h1] at hM
  exact isUnit_of_mul_isUnit_right hM

end Adelic

theorem schurF_equivariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), ∀ g, b₁ (u * g) = GlobalTheory.JSW.psiN u * b₁ g) → ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, schurF β b₁ χ (u * g) = GlobalTheory.JSW.psiN u * schurF β b₁ χ g := by
  intro E _ _ _ m r β b₁ χ hβ hb u hu g
  have hU : IsUT (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) := hu
  have hM : IsUnit (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  set M := (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hMdef
  set U := (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hUdef
  unfold schurF
  rw [Units.val_mul]
  by_cases hD : IsUnit (Dof M).det
  · rw [if_pos ((isUnit_Dof_mul_iff M hU).2 hD), if_pos hD, Xof_mul_entry M hU hD, Scof_mul M hU hD, Dof_mul M hU,
      Yof_mul M hU, mkGL_mul (Aof_isUT hU) (isUnit_Scof M hM hD), mkGL_mul (Dof_isUT hU) hD,
      hβ _ (mkGL_mem_NA (Aof_isUT hU)), hb _ (mkGL_mem_NA (Dof_isUT hU)), psiN_mkGL (Aof_isUT hU),
      psiN_mkGL (Dof_isUT hU)]
    have h : GlobalTheory.JSW.psiN u = psi (sd (Aof U)) * psi (Bof U (Fin.last m) 0) * psi (sd (Dof U)) := by
      rw [GlobalTheory.JSW.psiN, superDiag_eq_sd, sd_blocks, ← psi_add, ← psi_add]; rfl
    rw [h, psi_add]; ring
  · rw [if_neg (mt (isUnit_Dof_mul_iff M hU).1 hD), if_neg hD, mul_zero]

end GlobalTheory.SchurEquiv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionWhittakerEquivariant =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolic\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGLStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlacesStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericCharStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlacesStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtensionStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOneStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGLStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApplyStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionCompactSupportModuloUnipotent\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionSmoothRightInvariant\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionWhittakerEquivariant\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.SchurExt
open scoped Topology

namespace GlobalTheory.SchurExt.Parts

alias L_glob := _root_.GlobalTheory.WhitBump.exists_bump_glob

alias L_equiv := _root_.GlobalTheory.SchurEquiv.schurF_equivariant

alias L_cpt := _root_.GlobalTheory.SchurExtCpt.exists_compact_support

alias L_inv := _root_.GlobalTheory.SchurExt.schurF_mul_finGL_eq

alias L_smooth := _root_.GlobalTheory.SchurExt.contDiffOn_chart_schurF

theorem L_block : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), ∀ h : GA E (m + 1), schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h * b₁ 1 * (χ 0 : ℂ) := GlobalTheory.T.schurComplementExtensionFunction_blockDiag_apply

alias L_projNA := _root_.GlobalTheory.SchurExt.prS_prO_NA_psiN

alias L_projSupS := _root_.GlobalTheory.SchurExt.prS_prO_supS

alias L_projInf := _root_.GlobalTheory.SchurExt.prS_prO_mul_infGL

alias L_projFin := _root_.GlobalTheory.SchurExt.eventually_prS_prO_finGL

theorem L_blockSupS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S := GlobalTheory.T.blockDiagGL_mem_adelicGLSupportedAtFinitePlaces

end GlobalTheory.SchurExt.Parts
open GlobalTheory.SchurExt.Parts

theorem GlobalTheory.SchurExt.exists_ext : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (β : GA E (m + 1) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
    (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) →
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) →
    ∃ b : GA E (m + r + 1 + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧
      (∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), b p ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, b (g * finGL E (m + r + 1 + 1) u) = b g) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + r + 1 + 1))) ∧
      ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, b (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h := by
  intro E _ _ _ m r S β hβN hβC hβU hβS
  obtain ⟨b₁, h1one, h1N, h1C, h1U, h1S⟩ := L_glob E r
  obtain ⟨Φ, hΦ1, hΦN, -, ⟨UΦ, hUΦo, hUΦ⟩, -⟩ := GlobalTheory.WhitBump.exists_bump E (m + r + 1) S
  let f : ContDiffBump (0 : Fin (r + 1) → Fin (m + 1) → Cinf E) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨C, hC, hCp⟩ := L_cpt E m r S β b₁ f hβC h1C f.hasCompactSupport
  obtain ⟨W, hW, hWk⟩ := L_inv E m r S β b₁ f hβU hβC h1U h1C
  refine ⟨extB S β b₁ f Φ, ?_, ⟨C, hC, ?_⟩, ?_, ?_, ?_⟩
  · intro u hu g
    obtain ⟨h1, h2, h3⟩ := L_projNA E (m + r + 1 + 1) S u hu
    simp only [extB, map_mul]
    rw [L_equiv E m r β b₁ f hβN h1N _ h1, hΦN _ h2, ← h3]
    ring
  · intro p hp hne
    obtain ⟨e1, e2⟩ := (L_projSupS E _ S).1 p hp.1
    refine hCp p hp fun h0 => hne ?_
    simp only [extB, e1, e2, h0, zero_mul]
  · let U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)) :=
      { carrier := {k | ∀ g, extB S β b₁ f Φ (g * finGL E _ k) = extB S β b₁ f Φ g}
        mul_mem' := fun {a b} ha hb g => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, ← mul_assoc, hb, ha]
        one_mem' := fun g => by simp only [map_one, mul_one]
        inv_mem' := fun {a} ha g => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          have := ha (g * finGL E _ a⁻¹)
          rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
          exact this.symm }
    refine ⟨U, Subgroup.isOpen_of_mem_nhds U (g := 1) ?_, fun u hu g => hu g⟩
    have hV' : (UΦ : Set _) ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)) := hUΦo.mem_nhds UΦ.one_mem
    filter_upwards [L_projFin E _ S W _ hW hV'] with k hk
    obtain ⟨⟨k', hk'W, hk'⟩, ⟨k'', hk''V, hk''⟩⟩ := hk
    intro g
    simp only [extB, map_mul, hk', hk'']
    rw [hWk k' hk'W (hk' ▸ (L_projSupS E _ S).2 _) _ ((L_projSupS E _ S).2 g), hUΦ k'' hk''V]
  · intro g
    have hs := (L_smooth E m r β b₁ f hβS h1S h1C f.contDiff (prS S _ g)).mul
      (contDiffOn_const (c := Φ (prO S _ g)))
    refine hs.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    obtain ⟨e1, e2⟩ := L_projInf E _ S g hx'.unit
    simp only [chart, dif_pos hx', extB, e1, e2]
  · intro h hh
    obtain ⟨e1, e2⟩ := (L_projSupS E _ S).1 _ (L_blockSupS E m r S h hh)
    have hf0 : f 0 = 1 := f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)
    simp only [extB, e1, e2, hΦ1, mul_one, L_block, h1one, hf0, Complex.ofReal_one]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplementStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplementStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.exists_whittaker_bump_extension_schur_complement : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (β : GA E (m + 1) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
    (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) →
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) →
    ∃ b : GA E (m + r + 1 + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧
      (∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), b p ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, b (g * finGL E (m + r + 1 + 1) u) = b g) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + r + 1 + 1))) ∧
      ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, b (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h := by
  first | (exact @GlobalTheory.SchurExt.exists_ext)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplementStatement =====
