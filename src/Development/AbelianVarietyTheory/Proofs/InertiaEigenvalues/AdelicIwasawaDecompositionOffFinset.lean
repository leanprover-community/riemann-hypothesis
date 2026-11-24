module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipMulMemCell
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDivZpowOrd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaCellDecomposition, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaCellDecomposition =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaCellDecomposition", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipMulMemCell\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDivZpowOrd\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow\nimport Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups\nimport Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff\nimport Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo\nimport Formalism.ConjugateSelfDual.Statement\nimport ReciprocityTheory.GaloisValuations.GlobalA\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwaCell

theorem exists_mem_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ g : GL (Fin m) k, ∃ a : Fin m → ℤ, g ∈ GlobalTheory.IwaCell.cell ϖ a := by
  intro k _ _ _ _ m ϖ hϖ g
  obtain ⟨k₀, b, hb, hg⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k m g⁻¹
  have hg' : g = b⁻¹ * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹ := by
    rw [← _root_.mul_inv_rev, ← hg, inv_inv]
  set c := b⁻¹ with hc
  have hcT : c.val.BlockTriangular id := by
    have : c.val = b.val⁻¹ := by rw [hc, Matrix.coe_units_inv]
    rw [this]; exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hdet : c.val.det = ∏ i, c.val i i := Matrix.det_of_upperTriangular hcT
  have hd : ∀ i, c.val i i ≠ 0 := fun i h => by
    have := Matrix.GeneralLinearGroup.det_ne_zero c
    rw [hdet] at this
    exact this (Finset.prod_eq_zero (Finset.mem_univ i) h)
  let d : Fin m → kˣ := fun i => Units.mk0 _ (hd i)
  let a : Fin m → ℤ := fun i => ord k (d i)
  let e : Fin m → kˣ := fun i => d i / ϖ ^ a i
  have he : ∀ i, valuation k (e i : k) = 1 := fun i => by
    apply ord_eq_zero_iff.1
    simp only [e, div_eq_mul_inv, ← _root_.zpow_neg, ord_mul, ord_zpow, hϖ, a]
    ring
  have hde : d = (fun i => ϖ ^ a i) * e := by
    funext i; simp [e]
  let u := c * (diagT k (Fin m) d)⁻¹
  have hu : u ∈ unipB k (Fin m) := by
    rw [mem_unipB]
    have hval : u.val = c.val * diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) := by
      simp only [u, ← map_inv, Units.val_mul, val_diagT, Pi.inv_apply]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hval, mul_diagonal, hcT hij, zero_mul]
    · rw [hval, mul_diagonal]; simp [d, mul_inv_cancel₀ (hd i)]
  refine ⟨a, u, hu, diagT k (Fin m) e * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹,
    mul_mem (GlobalTheory.LocalCartan.diagT_mem_KO he) (inv_mem ⟨k₀, rfl⟩), ?_⟩
  rw [hg', tD, ← mul_assoc, mul_assoc u, ← map_mul, ← hde]
  simp [u]

end GlobalTheory.IwaCell
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaCellDecomposition =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipMulMemCell\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaCellDecomposition\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CellDec

open Filter

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_finGL (v : HeightOneSpectrum (𝓞 E)) (h : GL (Fin n) (Af E)) :
    compV E n v (finGL E n h) = GeneralLinearGroup.map (pLoc E v) h :=
  map_cornerGL_of_hom _ _ _ (fun _ => rfl) h

theorem compV_finGL_locGL_same (v : HeightOneSpectrum (𝓞 E)) (y : GL (Fin n) (v.adicCompletion E)) :
    compV E n v (finGL E n (locGL E n v y)) = y := by
  rw [compV_finGL, pLoc_locGL]

theorem compV_finGL_locGL_ne {v w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v) (y : GL (Fin n) (v.adicCompletion E)) :
    compV E n w (finGL E n (locGL E n v y)) = 1 := by
  rw [compV_finGL, pLoc_locGL_of_ne h]

theorem cornerGL_mem_unipB {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S) {g : GL (Fin a) R}
    (hg : g ∈ GlobalTheory.SmGL.unipB R (Fin a)) : cornerGL a s g ∈ GlobalTheory.SmGL.unipB S (Fin a) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hg
  refine (GlobalTheory.SmGL.mem_unipB S).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s ((g : Matrix _ _ R) i j) = 0
    rw [h1 i j hij, Matrix.one_apply_ne hij.ne', Matrix.one_apply_ne hij.ne', map_zero]
    simp
  · change (1 : Matrix (Fin a) (Fin a) S) i i - s ((1 : Matrix (Fin a) (Fin a) R) i i) + s ((g : Matrix _ _ R) i i) = 1
    rw [h2 i, Matrix.one_apply_eq, Matrix.one_apply_eq]
    simp

theorem finGL_locGL_mem_NA (v : HeightOneSpectrum (𝓞 E)) {y : GL (Fin n) (v.adicCompletion E)}
    (hy : y ∈ GlobalTheory.SmGL.unipB (v.adicCompletion E) (Fin n)) : finGL E n (locGL E n v y) ∈ NA E n :=
  cornerGL_mem_unipB _ (cornerGL_mem_unipB _ hy)

theorem mem_US {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E n} :
    g ∈ US E n S ↔ ∀ v, v ∉ S → compV E n v g ∈ GlobalTheory.LFun.KGL v (n := n) := by
  simp [US, Subgroup.mem_iInf]

theorem eventually_compV_mem (g : GA E n) : ∀ᶠ w in cofinite, compV E n w g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h : ∀ x : GA E n, ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ i j,
      (compV E n w x).val i j ∈ w.adicCompletionIntegers E := fun x => by
    simp only [Filter.eventually_all]
    intro i j
    exact (pFin E ((x : Matrix (Fin n) (Fin n) (Ad E)) i j)).2
  filter_upwards [h g, h g⁻¹] with w a b
  exact GlobalTheory.BCT.GoodInt.mem_GLint _ _ a (by rw [← map_inv]; exact b)

end GlobalTheory.CellDec

noncomputable section
namespace GlobalTheory.CellDec
open Filter
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem adl_add (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m₁ m₂ : HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    adl ϖ (m₁ + m₂) = adl ϖ m₁ * adl ϖ m₂ := by
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro v
  change ((ϖ v ^ (m₁ + m₂) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
    ((ϖ v ^ m₁ v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m₂ v : (v.adicCompletion E)ˣ) : _)
  rw [Finsupp.add_apply, _root_.zpow_add, Units.val_mul]

theorem adl_zero (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) : adl ϖ 0 = 1 := by
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro v
  change ((ϖ v ^ (0 : HeightOneSpectrum (𝓞 E) →₀ ℤ) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1
  simp

theorem tl_add (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l₁ l₂ : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    tl n ϖ (l₁ + l₂) = tl n ϖ l₁ * tl n ϖ l₂ := by
  unfold tl
  rw [← map_mul, ← map_mul]
  congr 2
  funext i
  rw [Pi.mul_apply, ← adl_add]
  congr 1
  ext v
  simp

theorem tl_zero (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) : tl n ϖ 0 = 1 := by
  unfold tl
  have : (fun i : Fin n => adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (0 : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)))) = 1 := by
    funext i
    rw [Finsupp.mapRange_zero, adl_zero]
    rfl
  rw [this, map_one, map_one]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem tl_single (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (v : HeightOneSpectrum (𝓞 E)) (a : Fin n → ℤ) :
    tl n ϖ (Finsupp.single v a) = finGL E n (locGL E n v (GlobalTheory.IwaCell.tD (ϖ v) a)) := by
  unfold tl
  congr 1
  apply _root_.GlobalTheory.CuspRep.LocUniq.gl_ext
  intro w
  by_cases hw : w = v
  · subst hw
    rw [pLoc_locGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [GlobalTheory.IwaCell.val_tD]
    change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (Finsupp.single w a)) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  · rw [pLoc_locGL_of_ne hw]
    refine Units.ext (Matrix.ext fun i j => ?_)
    change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (Finsupp.single v a)) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      simp [Ne.symm hw]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem ord_eq_one_of_isUnifV {v : HeightOneSpectrum (𝓞 E)} {π : (v.adicCompletion E)ˣ} (h : IsUnifV E v (π : v.adicCompletion E)) :
    GlobalTheory.SmGL.ord (v.adicCompletion E) π = 1 := by
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, h]
  change -WithZero.log (WithZero.exp (-1 : ℤ)) = 1
  simp

end
end GlobalTheory.CellDec

noncomputable section
namespace GlobalTheory.CellDec
open Filter
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem tl_inv_conj_mem (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    {u : GA E n} (hu : u ∈ NA E n) : (tl n ϖ l)⁻¹ * u * tl n ϖ l ∈ NA E n := by
  have h : tl n ϖ (-l) = (tl n ϖ l)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← tl_add, neg_add_cancel, tl_zero])
  have := tl_conj_mem ϖ (-l) hu
  rwa [h, inv_inv] at this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem exists_of_finset (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ g : GA E n, (∀ w, w ∉ S → w ∉ T → compV E n w g ∈ GlobalTheory.LFun.KGL w (n := n)) →
      ∃ l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ), (∀ v ∈ S, l v = 0) ∧ (tl n ϖ l)⁻¹ * g ∈ C0 E n S := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    refine ⟨0, fun _ _ => rfl, 1, one_mem _, g, mem_US.2 fun w hw => hg w hw (Finset.notMem_empty w), ?_⟩
    rw [tl_zero, inv_one, one_mul]
  | insert v T hvT ih =>
    intro g hg
    by_cases hvS : v ∈ S
    · refine ih g fun w hwS hwT => hg w hwS ?_
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hwS (h ▸ hvS), hwT⟩
    · obtain ⟨a, u, hu, κ, hκ, e⟩ := GlobalTheory.IwaCell.exists_mem_cell (v.adicCompletion E) n (ϖ v) (ord_eq_one_of_isUnifV (hϖ v))
        (compV E n v g)
      rw [GlobalTheory.HeckeEigConj.KO_eq_KGL] at hκ
      set x := finGL E n (locGL E n v u) with hx
      set t := tl n ϖ (Finsupp.single v a) with ht
      have hg' : ∀ w, w ∉ S → w ∉ T → compV E n w ((x * t)⁻¹ * g) ∈ GlobalTheory.LFun.KGL w (n := n) := by
        intro w hwS hwT
        rw [map_mul, map_inv, map_mul, hx, ht, tl_single]
        by_cases hw : w = v
        · subst hw
          rw [compV_finGL_locGL_same, compV_finGL_locGL_same, e]
          convert hκ using 1
          group
        · rw [compV_finGL_locGL_ne hw, compV_finGL_locGL_ne hw, one_mul, inv_one, one_mul]
          refine hg w hwS ?_
          rw [Finset.mem_insert, not_or]
          exact ⟨hw, hwT⟩
      obtain ⟨l', hl'S, u', hu', k, hk, e'⟩ := ih _ hg'
      refine ⟨Finsupp.single v a + l', fun w hw => ?_, (tl n ϖ (Finsupp.single v a + l'))⁻¹ * x *
        tl n ϖ (Finsupp.single v a + l') * u', mul_mem (tl_inv_conj_mem ϖ _ (finGL_locGL_mem_NA v hu)) hu', k, hk, ?_⟩
      · rw [Finsupp.add_apply, hl'S w hw, Finsupp.single_apply, if_neg (fun (h : v = w) => hvS (h ▸ hw)), add_zero]
      · have hg2 : g = x * t * (tl n ϖ l' * (u' * k)) := by
          rw [← e', mul_inv_cancel_left, mul_inv_cancel_left]
        rw [hg2, tl_add, ← ht]
        group

theorem adelic_iwasawa_decomposition_off_finset : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ g : GA E n, ∃ l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ), (∀ v ∈ S, l v = 0) ∧
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S := by
  intro E _ _ n S ϖ hϖ g
  have hfin : {w | compV E n w g ∉ GlobalTheory.LFun.KGL w (n := n)}.Finite :=
    Filter.eventually_cofinite.1 (eventually_compV_mem g)
  refine exists_of_finset S ϖ hϖ hfin.toFinset g fun w _ hw => ?_
  by_contra h
  exact hw (hfin.mem_toFinset.2 h)

end GlobalTheory.CellDec
end -- clump:auto
end -- clump:auto
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset =====
