module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.ContinuousLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Spf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FrameArchimedeanPairing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IntegralJnp, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmul, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmulAlt

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IntegralJnp =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IntegralJnp", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.ContinuousLoc\nimport Development.WeilBound.ThetaLifts.SmallCones.IdeleTop\nimport GroundTheory.GlobalFields.TateThesis.AdeleMeasure\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFPB

open PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem map_isHaar (R : RD d) (νf : Measure (Yf d)) [νf.IsAddHaarMeasure] :
    (Measure.map (fun p : Vw d × Yf d => jn R p.1 p.2) ((volume : Measure (Vw d)).prod νf)).IsAddHaarMeasure := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : BorelSpace (Yf d) := Pi.borelSpace
  haveI : MeasurableAdd (Yf d) := inferInstance
  haveI : SigmaFinite νf := inferInstance
  haveI : ((volume : Measure (Vw d)).prod νf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact ContinuousAddEquiv.isAddHaarMeasure_map ((volume : Measure (Vw d)).prod νf) (jnpE R)

theorem exists_nuf' (R : RD d) : ∃ νf : Measure (Yf d), νf.IsAddHaarMeasure ∧
    (Measure.map (fun p : Vw d × Yf d => jn R p.1 p.2) ((volume : Measure (Vw d)).prod νf)).IsAddHaarMeasure := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  exact ⟨Measure.addHaar, inferInstance, map_isHaar R _⟩

theorem integral_jnp' (R : RD d) {νf : Measure (Yf d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) {g : Yf d → ℂ} (hg' : g ∈ SB (Yf d)) {b : Vw d → ℂ} (hb : Continuous b) (hb1 : ∀ u, ‖b u‖ ≤ 1) :
    ∫ X, f X * star (b (arc R X) * g (fin d X))
        ∂(Measure.map (fun p : Vw d × Yf d => jn R p.1 p.2) ((volume : Measure (Vw d)).prod νf)) =
      ∫ u, star (b u) * hg R νf f g u := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : BorelSpace (Yf d) := Pi.borelSpace
  haveI : SigmaFinite νf := inferInstance
  set μ := (volume : Measure (Vw d)).prod νf with hμ
  let e : Vw d × Yf d ≃ᵐ Mx F E d.m d.n := (jnpE R).toHomeomorph.toMeasurableEquiv
  have hmap : Measure.map (fun p : Vw d × Yf d => jn R p.1 p.2) μ = Measure.map e μ := rfl
  have hH : (Measure.map e μ).IsAddHaarMeasure := map_isHaar R νf
  have hfi : Integrable (fun p : Vw d × Yf d => f (jn R p.1 p.2)) μ :=
    (integrable_map_equiv e f).1 (KFock.int_schM d _ hH hf)
  obtain ⟨C, hC⟩ := hg'.1.continuous.bounded_above_of_compact_support hg'.2
  have hint : Integrable (fun p : Vw d × Yf d => f (jn R p.1 p.2) * star (b p.1 * g p.2)) μ := by
    refine hfi.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (continuous_star.comp ((hb.comp continuous_fst).mul (hg'.1.continuous.comp continuous_snd))).aestronglyMeasurable
    · rw [norm_star, norm_mul]
      calc ‖b p.1‖ * ‖g p.2‖ ≤ 1 * C := mul_le_mul (hb1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
  rw [hmap, integral_map_equiv]
  have he : ∀ p, e p = jn R p.1 p.2 := fun p => rfl
  simp only [he, arc_jn, fin_jn]
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [hg, star_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

end PositivityTheory.SiegelWeilFormula.KFPB

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IntegralJnp =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmul =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmul", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem cwA_add (w : InfinitePlace F) (X Y : Mx F E d.m d.n) : d.cw w (X + Y) = d.cw w X + d.cw w Y := by
  ext i j
  simp [SD.cw]

theorem cwA_realAd (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    d.cw w (realAd F t • X) = (t : ℂ) • d.cw w X := by
  ext i j
  simp [SD.cw, GlobalTheory.RealScalar.piInf_realAd_smul]

theorem locA_add (R : RD d) (w : InfinitePlace F) (X Y : Mx F E d.m d.n) :
    R.loc w (X + Y) = R.loc w X + R.loc w Y := by
  simp only [RD.loc, cwA_add, Matrix.mul_add]
  exact Matrix.map_add _ (fun a b => star_add a b) _ _

theorem locA_realAd (R : RD d) (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    R.loc w (realAd F t • X) = (t : ℂ) • R.loc w X := by
  simp only [RD.loc, cwA_realAd, Matrix.mul_smul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  rfl

def arcAF (R : RD d) (X : Mx F E d.m d.n) : Iw d → ℝ :=
  fun i => if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im

theorem arcA_eq (R : RD d) (X : Mx F E d.m d.n) : arc R X = (EuclideanSpace.equiv (Iw d) ℝ).symm (arcAF R X) := rfl

theorem arc_add' (R : RD d) (X Y : Mx F E d.m d.n) : arc R (X + Y) = arc R X + arc R Y := by
  have : arcAF R (X + Y) = arcAF R X + arcAF R Y := by
    funext i
    simp only [arcAF, locA_add, Pi.add_apply]
    split_ifs <;> simp
  rw [arcA_eq, arcA_eq, arcA_eq, this, map_add (f := _)]

theorem arc_realAd' (R : RD d) (t : ℝ) (X : Mx F E d.m d.n) : arc R (realAd F t • X) = t • arc R X := by
  have : arcAF R (realAd F t • X) = t • arcAF R X := by
    funext i
    simp only [arcAF, locA_realAd, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [arcA_eq, arcA_eq, this, map_smul]

theorem crdA_add (X Y : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : d.crd (X + Y) k = d.crd X k + d.crd Y k := by
  simp [SD.crd]

theorem sndA_crd_of (Z : Mx F E d.m d.n) (hZ : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd Z k).2 = 0 := by
  have h1 : finOne F • Z k.1 k.2.1 = 0 := by
    have := congrFun (congrFun hZ k.1) k.2.1
    simpa using this
  have h2 : finOne F * (Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2 = 0 := by
    have := congrArg (fun z => (Algebra.TensorProduct.basis (AF F) d.bs).repr z k.2.2) h1
    simpa only [map_smul, Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul] using this
  have h3 : (1 : FiniteAdeleRing (𝓞 F) F) * ((Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2).2 = 0 :=
    congrArg Prod.snd h2
  rw [one_mul] at h3
  exact h3

theorem fin_add_of' (R : RD d) {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (X : Mx F E d.m d.n) :
    fin d (X + Z) = fin d X := by
  funext k
  show (d.crd (X + Z) k).2 = (d.crd X k).2
  rw [crdA_add]
  show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
  rw [sndA_crd_of Z hZ k, add_zero]

theorem fin_realAd_smul' {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (t : ℝ) : finOne F • (realAd F t • Z) = 0 := by
  rw [smul_comm, hZ, smul_zero]

theorem gau_eq' (R : RD d) (X : Mx F E d.m d.n) : gau R X = (Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℂ) := by
  have hn : ‖arc R X‖ ^ 2 = ∑ w, ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, arc, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [EuclideanSpace.equiv]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  simp only [gau, fP, evX, map_one, one_mul, gs]
  rw [hn, ← Complex.exp_sum, Complex.ofReal_exp]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

end PositivityTheory.SiegelWeilFormula.KFP

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmul =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmulAlt =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmulAlt", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Spf\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IntegralJnp\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmul\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FrameArchimedeanPairing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

def jnp (R : RD d) (p : Vw d × Yf d) : Mx F E d.m d.n := jn R p.1 p.2

theorem exists_nuf (R : RD d) : ∃ νf : Measure (Yf d), νf.IsAddHaarMeasure ∧
    (Measure.map (jnp R) ((volume : Measure (Vw d)).prod νf)).IsAddHaarMeasure := by
  exact KFPB.exists_nuf' R

theorem integral_jnp (R : RD d) {νf : Measure (Yf d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) {g : Yf d → ℂ} (hg' : g ∈ SB (Yf d)) {b : Vw d → ℂ} (hb : Continuous b) (hb1 : ∀ u, ‖b u‖ ≤ 1) :
    ∫ X, f X * star (b (arc R X) * g (fin d X)) ∂(Measure.map (jnp R) ((volume : Measure (Vw d)).prod νf)) =
      ∫ u, star (b u) * hg R νf f g u := by
  exact KFPB.integral_jnp' R hνf hf hg' hb hb1

end PositivityTheory.SiegelWeilFormula.KFP

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmulAlt =====
