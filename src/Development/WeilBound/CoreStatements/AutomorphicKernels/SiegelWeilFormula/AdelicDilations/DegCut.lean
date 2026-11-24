module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.BlockTriangularFrames.SiegelParabolicEqStabiliserCols
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FourierZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DerivInv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FcCont
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DilExPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.WeightFactorDilation
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.AesmOfContinuous
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.COneLawPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CntFalse
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionEqThetaZero
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.UnitsBorelSpace.BorelSpaceDoubledGroup
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.RatVCocompact, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.AvgHolPf, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CharacterW1TraceExp, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.HolCoefPf, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DegCut

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.RatVCocompact =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.RatVCocompact", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.BlockTriangularFrames.SiegelParabolicEqStabiliserCols\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace COneB

variable {d : SD σ} (L : LD d)

def Nu (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := ∑ j, Matrix.single L.i₀ (L.em j) (u j)

theorem em_ne (j : Fin L.n) : L.em j ≠ L.i₀ := (L.rng (L.em j)).2 ⟨j, rfl⟩

theorem Nu_mul (u v : Fin L.n → AE F E) : Nu L u * Nu L v = 0 := by
  simp only [Nu, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  apply Matrix.single_mul_single_of_ne
  exact em_ne L _

theorem Nu_add (u v : Fin L.n → AE F E) : Nu L (u + v) = Nu L u + Nu L v := by
  simp only [Nu, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]

theorem Nu_cont : Continuous (Nu L) := by
  have e : Nu L = fun u => ∑ j, u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext u; simp only [Nu, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const


omit L in
theorem unit_frame (d : SD σ) (x : d.G) : ∃ e : AE F E,
    (inFrame d.b x)ᵀ * Matrix.fromBlocks 0 1 (e • 1) 0 * (inFrame d.b x).map (cA σ) = Matrix.fromBlocks 0 1 (e • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨((ε : ℤ) : AE F E), ?_⟩
  have hF := kfour.frameEq_adelic (F := F) (Y := d.Y) hε
  have hU : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b x] at hU
  have h1 : (incM F d.b.1)ᵀ * (incM F (d.b⁻¹).1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.transpose_one]
  have h2 : (incM F (d.b⁻¹).1).map (cA σ) * (incM F d.b.1).map (cA σ) = 1 := by
    rw [← SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← hF]
  conv_rhs => rw [← hU]
  rw [SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one, ← Matrix.mul_assoc (incM F d.b.1)ᵀ (incM F (d.b⁻¹).1)ᵀ, h1, Matrix.one_mul]

omit L in
theorem blk_unit (d : SD σ) (x : d.G) (a a' : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a 0 0 a') : aᵀ * a'.map (cA σ) = 1 := by
  obtain ⟨e, he⟩ := unit_frame d x
  rw [hx] at he
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero _), Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one] at he
  have := (Matrix.fromBlocks_inj.1 he).2.1
  exact this

omit L in
theorem cA_cA_mat (d : SD σ) {p q : Type} (M : Matrix p q (AE F E)) : (M.map (cA σ)).map (cA σ) = M := by
  have hσ : ∀ a, σ (σ a) = a := kfour.sigma_sigma_of_good d.ok.good
  ext i j; simp [kfour.cA_cA' σ hσ]

theorem uM_frame {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (1 + Nu L u) 0 0 (((1 - Nu L u)ᵀ).map (cA σ)) := by
  obtain ⟨a', ha'⟩ := hu.1 u
  have ha : inFrame d.b (uM u) = Matrix.fromBlocks (1 + Nu L u) 0 0 a' := ha'
  rw [ha]
  have h1 := blk_unit d _ _ _ ha
  have h2 : (1 - Nu L u)ᵀ * (1 + Nu L u)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Nu_mul, sub_zero,
      sub_add_cancel, Matrix.transpose_one]
  have h3 : a'.map (cA σ) = (1 - Nu L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - Nu L u)ᵀ * (1 + Nu L u)ᵀ) * a'.map (cA σ) := by rw [h2, Matrix.one_mul]
      _ = (1 - Nu L u)ᵀ * ((1 + Nu L u)ᵀ * a'.map (cA σ)) := by rw [Matrix.mul_assoc]
      _ = (1 - Nu L u)ᵀ := by rw [h1, Matrix.mul_one]
  have h4 : a' = ((1 - Nu L u)ᵀ).map (cA σ) := by rw [← h3, cA_cA_mat d]
  rw [h4]

theorem uM_add {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  apply kfour.inFrame_injective d.b
  rw [SiegelEisensteinSeries.Grp.inFrame_mul, uM_frame L hu, uM_frame L hu, uM_frame L hu, Matrix.fromBlocks_multiply]
  have e1 : (1 + Nu L u) * (1 + Nu L v) = 1 + Nu L (u + v) := by
    rw [Nu_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Nu_mul, add_zero]
    abel
  have e2 : ((1 - Nu L u)ᵀ).map (cA σ) * ((1 - Nu L v)ᵀ).map (cA σ) = ((1 - Nu L (u + v))ᵀ).map (cA σ) := by
    have hm := Matrix.map_mul (L := (1 - Nu L u)ᵀ) (M := (1 - Nu L v)ᵀ) (f := (cA σ).toRingHom)
    erw [← hm]
    rw [← Matrix.transpose_mul, Nu_add, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Nu_mul,
      sub_zero]
    congr 2
    abel
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e2]

theorem uM_zero {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : uM 0 = 1 := by
  have h := uM_add L hu 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem uM_neg {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (uM u)⁻¹ = uM (-u) := by
  have h := uM_add L hu (-u) u
  rw [neg_add_cancel, uM_zero L hu] at h
  exact (eq_inv_of_mul_eq_one_left h.symm).symm

theorem uM_cont {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : Continuous uM := by
  have hcA : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  have hmat : Continuous fun u => mat2 (uM u) := by
    have e : (fun u => mat2 (uM u)) = fun u => incM F d.b.1 * Matrix.fromBlocks (1 + Nu L u) 0 0
        (((1 - Nu L u)ᵀ).map (cA σ)) * incM F (d.b⁻¹).1 := by
      funext u; rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b, uM_frame L hu]
    rw [e]
    refine (continuous_const.matrix_mul (Continuous.matrix_fromBlocks (continuous_const.add (Nu_cont L))
      continuous_const continuous_const ?_)).matrix_mul continuous_const
    exact ((continuous_const.sub (Nu_cont L)).matrix_transpose).matrix_map hcA
  have hinv : Continuous fun u => mat2 (uM u)⁻¹ := by
    simp only [uM_neg L hu]
    exact hmat.comp continuous_neg
  refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
  exact Units.continuous_iff.2 ⟨hmat, hinv⟩

theorem ratV_cocompact : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ u, ∃ r ∈ L.ratV, r + u ∈ K := by
  obtain ⟨C, hC, hCx⟩ := kfour.exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi (fun _ => C), isCompact_univ_pi (fun _ => hC), fun u => ?_⟩
  choose x hx using fun j => hCx (u j)
  refine ⟨GlobalTheory.ThK.incV F x, AddSubgroup.subset_closure ⟨x, rfl⟩, fun j _ => ?_⟩
  simpa [GlobalTheory.ThK.incV] using hx j

end COneB

end PositivityTheory.SiegelWeilFormula.AStep

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.RatVCocompact =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.AvgHolPf =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.AvgHolPf", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FourierZero\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.UnitsBorelSpace.BorelSpaceDoubledGroup\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DerivInv\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FcCont\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.RatVCocompact\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace COneB

theorem fcBd' (d : SD σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) :
    ∃ K : Set (nA σ d.Y d.b), IsCompact K ∧ ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      ∀ y : d.G, (∀ β ∈ K, ‖f (nb β * y)‖ ≤ M) → ‖fc d.B.ψ d.b nb lam 𝓖 f T y‖ ≤ M := by
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hc
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := kfour.sigma_sigma_of_good hB
  have hb := d.ok.frame
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ hb
  refine ⟨K, hK, fun f M hf y hM => ?_⟩
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hbd : ∀ β, ‖f (nb β * y) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))‖ ≤ M := by
    intro β
    obtain ⟨γ, hγ, hk⟩ := hKc β
    rw [norm_mul, hψ.2.1 _, mul_one]
    have e : f (nb β * y) = f (nb (γ + β) * y) := by
      rw [kfour.nb_add hnb, mul_assoc, hf _ (kfour.nb_rat hnb γ hγ)]
    rw [e]
    exact hM _ hk
  have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd β)
  have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
  rw [hr, mul_one] at h1
  exact h1

end COneB

section Deg

variable (H : Hyps) {d : SD σ} (R : RD d) (L : LD d) (R' : RD L.sd) (hmn : d.m < d.n) (hIH : MainV 2 R') {Φ : d.Fn}
  (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
  (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t)


include H hE in
theorem avgHol_pf {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (x : d.G) :
    DifferentiableOn ℂ (fun z => avg d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) U ∧ ∀ i : ℕ,
      iteratedDeriv i (fun z => avg d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) (s0 d.m d.n) =
        avg d L uM ν 𝓤 nb lam 𝓖 (fun g => iteratedDeriv i (Ê · g) (s0 d.m d.n)) T x := by
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  have hb := d.ok.frame
  have hnbc := kfour.nb_continuous hσ hb hc.1
  obtain ⟨iTG, -, -, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  obtain ⟨KN, hKN, hKNb⟩ := COneB.fcBd' d hc T
  obtain ⟨KU, hKU, hKUc⟩ := COneB.ratV_cocompact L
  have huc := COneB.uM_cont L hu
  let C : Set d.G := (fun q : nA σ d.Y d.b × (Fin L.n → AE F E) => nb q.1 * uM q.2 * x) '' (KN ×ˢ KU)
  have hCc : IsCompact C :=
    (hKN.prod hKU).image (((hnbc.comp continuous_fst).mul (huc.comp continuous_snd)).mul continuous_const)
  have hper : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) → ∀ u, ∃ k ∈ KU,
      fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T (uM k * x) := by
    intro φ hφ hi u
    obtain ⟨r, hr, hk⟩ := hKUc u
    refine ⟨r + u, hk, ?_⟩
    rw [COneB.uM_add L hu, mul_assoc, (H.fcConj F E σ d L nb lam 𝓖 hc).2 uM ν 𝓤 hu T T' hT φ hφ hi r hr]
  have hbound : ∀ (φ : d.G → ℂ) (M : ℝ), Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      (∀ y ∈ C, ‖φ y‖ ≤ M) → ∀ u, ‖fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)‖ ≤ M := by
    intro φ M hφ hi hM u
    obtain ⟨k, hk, e⟩ := hper φ hφ hi u
    rw [e]
    refine hKNb φ M hi _ fun β hβ => hM _ ⟨(β, k), ⟨hβ, hk⟩, ?_⟩
    simp only [mul_assoc]
  have hmeas : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      AEStronglyMeasurable (fun u => fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)) ν := by
    intro φ hφ hi
    exact ((fcCont d hc T φ hφ hi).comp (huc.mul continuous_const)).aestronglyMeasurable
  have hfin : ν 𝓤 < ⊤ := by rw [hu.2.2.2]; exact ENNReal.one_lt_top
  have hint : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      IntegrableOn (fun u => fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)) 𝓤 ν := by
    intro φ hφ hi
    obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn hφ.continuousOn
    exact Measure.integrableOn_of_bounded (M := M) hfin.ne (hmeas φ hφ hi)
      (Filter.Eventually.of_forall fun u => hbound φ M hφ hi hM u)
  have hadd : ∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ γ ∈ rat2 σ d.Y, ∀ g, f' (γ * g) = f' g) → avg d L uM ν 𝓤 nb lam 𝓖 (a • f + f') T x =
        a * avg d L uM ν 𝓤 nb lam 𝓖 f T x + avg d L uM ν 𝓤 nb lam 𝓖 f' T x := by
    intro a f f' hf hf' hi hi'
    simp only [avg]
    have e : (fun u => fc d.B.ψ d.b nb lam 𝓖 (a • f + f') T (uM u * x)) =
        fun u => a * fc d.B.ψ d.b nb lam 𝓖 f T (uM u * x) + fc d.B.ψ d.b nb lam 𝓖 f' T (uM u * x) :=
      funext fun u => (fcAll d hc T (uM u * x)).1 a f f' hf hf' hi hi'
    rw [e, integral_add ((hint f hf hi).const_mul a) (hint f' hf' hi'), integral_const_mul]
  have hbd : ∃ C : Set d.G, IsCompact C ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f →
      (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → (∀ y ∈ C, ‖f y‖ ≤ M) → ‖avg d L uM ν 𝓤 nb lam 𝓖 f T x‖ ≤ M := by
    refine ⟨C, hCc, fun f M hf hi hM => ?_⟩
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun u _ => hbound f M hf hi hM u)
    have hr : ν.real 𝓤 = 1 := by simp [Measure.real, hu.2.2.2]
    rw [hr, mul_one] at h1
    exact h1
  obtain ⟨hDiff, hComm⟩ := _root_.GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv (rat2 σ d.Y) (fun φ => avg d L uM ν 𝓤 nb lam 𝓖 φ T x) hadd hbd U Ê hUo hd hcont hinv
  exact ⟨hDiff, fun i => hComm _ hs i⟩

end Deg

end PositivityTheory.SiegelWeilFormula.AStep

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.AvgHolPf =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CharacterW1TraceExp =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CharacterW1TraceExp", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem nbw1 (d : SD σ) (R : RD d) (w : InfinitePlace F) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb)
    (xN : GR d.n) (h : Matrix (Fin d.n) (Fin d.n) ℂ) (hxN : mR xN = nU h) :
    ∃ β₁ : nA σ d.Y d.b, R.ι w xN = nb β₁ ∧ d.cw w β₁.1 = R.ζ • h ∧ (∀ u, u ≠ w → d.cw u β₁.1 = 0) ∧
      finOne F • β₁.1 = 0 := by
  have hP : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w xN)).toBlocks₁₂ 0 1 := by
    apply Place.cw_ext d
    · intro u
      rw [KSing.UnitaryGroupBasics.cw_fromBlocks, KSing.UnitaryGroupBasics.cw_toBlocks₁₂]
      by_cases hu : u = w
      · subst hu
        rw [KSing.UnitaryGroupBasics.cw_unip d R u xN _ hxN, Matrix.toBlocks_fromBlocks₁₂]
      · rw [R.off_w w u xN hu, KSing.UnitaryGroupBasics.toBlocks₁₂_one, Matrix.fromBlocks_one]
    · rw [Matrix.fromBlocks_smul, KSing.UnitaryGroupBasics.fin_toBlocks₁₂, R.off_f w xN, ← KSing.UnitaryGroupBasics.fin_toBlocks₁₂, KSing.UnitaryGroupBasics.toBlocks₁₂_one,
        smul_zero]
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
  let β₁ : nA σ d.Y d.b := ⟨(inFrame d.b (R.ι w xN)).toBlocks₁₂, AddSubgroup.subset_closure ⟨R.ι w xN, hP⟩⟩
  have hB : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 β₁.1 0 1 := hP
  refine ⟨β₁, KSing.UnitaryGroupBasics.inFrame_inj d (by rw [hN]; exact hB), ?_, fun u hu => ?_, ?_⟩
  · have e := KSing.UnitaryGroupBasics.cw_unip d R w xN _ hxN
    rw [hB, KSing.UnitaryGroupBasics.cw_fromBlocks] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  · have e := R.off_w w u xN hu
    rw [hB, KSing.UnitaryGroupBasics.cw_fromBlocks, ← Matrix.fromBlocks_one] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  · have e := R.off_f w xN
    rw [hB, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1.trans (smul_zero _)

def betaW (d : SD σ) (R : RD d) (w : InfinitePlace F) (T : nF σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) • (-(2 : ℂ) • (R.ζ • d.cw w T.1.1))

theorem character_w1_trace_exp (d : SD σ) (R : RD d) (w : InfinitePlace F) (T : nF σ d.Y d.b) (β₁ : nA σ d.Y d.b)
    (h : Matrix (Fin d.n) (Fin d.n) ℂ) (hh : h.IsHermitian) (hBw : d.cw w β₁.1 = R.ζ • h)
    (hBu : ∀ u, u ≠ w → d.cw u β₁.1 = 0) (hBf : finOne F • β₁.1 = 0) :
    d.B.ψ (d.tt (T.1.1 * β₁.1)) = Complex.exp (Complex.I * (betaW d R w T * h).trace) := by
  have hT : (d.cw w T.1.1)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w T.1.1).map star = 0 := by
    refine AddSubgroup.closure_induction
      (p := fun β _ => (d.cw w β)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w β).map star = 0) ?_ ?_ ?_ ?_ T.1.2
    · rintro β ⟨x, hx⟩
      have e := KSing.UnitaryGroupBasics.form_w d R w x
      rw [hx, KSing.UnitaryGroupBasics.cw_fromBlocks] at e
      simp [Krd.Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply] at e
      rw [add_comm]
      exact e
    · ext i j; simp [SD.cw]
    · intro a b _ _ ha hb
      ext i j
      have ea := congrFun (congrFun ha i) j
      have eb := congrFun (congrFun hb i) j
      simp [SD.cw] at ea eb ⊢
      linear_combination ea + eb
    · intro a _ ha
      ext i j
      have ea := congrFun (congrFun ha i) j
      simp [SD.cw] at ea ⊢
      linear_combination -ea
  unfold betaW
  obtain ⟨Tw, hTw⟩ : ∃ Tw, Tw = d.cw w T.1.1 := ⟨_, rfl⟩
  rw [← hTw] at hT ⊢
  have hAh : (R.ζ • Tw)ᴴ = R.ζ • Tw := by
    ext i j
    have e := congrFun (congrFun hT j) i
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply,
      smul_eq_mul] at e
    rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul']
    rcases R.hζ with ⟨hε, hζ⟩ | ⟨hε, hζ⟩
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination -e
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination (-Complex.I) * e
  have hf : finOne F • (T.1.1 * β₁.1).trace = 0 := by
    rw [← Matrix.trace_smul, ← Matrix.mul_smul, hBf, Matrix.mul_zero, Matrix.trace_zero]
  have hw : ∀ u, u ≠ w → piInf (d.B.emb u) (T.1.1 * β₁.1).trace = 0 := fun u hu => by
    rw [KSing.UnitaryGroupBasics.piInf_trace, KSing.UnitaryGroupBasics.cw_mul, hBu u hu, Matrix.mul_zero, Matrix.trace_zero]
  have hz := Place.psi_trace_at d.std d.cm d.B.emb w (T.1.1 * β₁.1).trace hf hw
  have hw' : piInf (d.B.emb w) (T.1.1 * β₁.1).trace = ((R.ζ • Tw) * h).trace := by
    rw [KSing.UnitaryGroupBasics.piInf_trace, KSing.UnitaryGroupBasics.cw_mul, hBw, ← hTw, Matrix.mul_smul, Matrix.smul_mul]
  have hreal : ((((R.ζ • Tw) * h).trace).re : ℂ) = ((R.ζ • Tw) * h).trace := by
    have hs : star (((R.ζ • Tw) * h).trace) = ((R.ζ • Tw) * h).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hAh, hh.eq, Matrix.trace_mul_comm]
    exact Complex.conj_eq_iff_re.1 hs
  have eR : ((((2 * Real.pi : ℝ) : ℂ) • (-(2 : ℂ) • (R.ζ • Tw))) * h).trace =
      ((2 * Real.pi : ℝ) : ℂ) * (-2 * (R.ζ • Tw * h).trace) := by
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  unfold SD.tt
  rw [hz, hw', eR]
  generalize (R.ζ • Tw * h).trace = c at hreal ⊢
  congr 1
  push_cast
  rw [hreal]
  ring

end PositivityTheory.SiegelWeilFormula.AStep

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CharacterW1TraceExp =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.HolCoefPf =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.HolCoefPf", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CharacterW1TraceExp\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FourierZero\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DilExPf\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FcCont\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.WeightFactorDilation\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.AesmOfContinuous\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem holPhi (H : Hyps) {d : SD σ} (R : RD d) (w : InfinitePlace F) {nb lam 𝓖}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (A : d.G → ℂ) (hAc : Continuous A)
    (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g) (pp qq : ℕ) (e : ℤ)
    (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) (x' : d.G) :
    IsHolW pp qq e fun y => fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) := by
  have hc' := hc
  obtain ⟨hN, -, -, h1⟩ := hc'
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ d.ok.frame
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ d.ok.frame
  obtain ⟨-, -, hTG, -, -, -⟩ := H.auxEx F E σ d
  have := hTG
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std
  have hnbc := kfour.nb_continuous hσ d.ok.frame hN
  let u : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have huc : Continuous u := kfour.continuous_chr hψ.1 T.1.1
  let γf : nA σ d.Y d.b → nA σ d.Y d.b := fun β => Classical.choose (hKc β)
  have hγ : ∀ β, γf β ∈ nF σ d.Y d.b ∧ γf β + β ∈ K := fun β => Classical.choose_spec (hKc β)
  let c : nA σ d.Y d.b → d.G := fun β => nb (γf β + β) * x'
  have key : ∀ β (g : d.G), A (c β * g) = A (nb β * (x' * g)) := by
    intro β g
    show A (nb (γf β + β) * x' * g) = _
    rw [KSing.nb_add d hN, mul_assoc, mul_assoc, hAi _ (KSing.nb_rat d hN (hγ β).1)]
  have : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hC : IsCompact ((fun k => nb k * x') '' K) := hK.image (hnbc.mul continuous_const)
  have hmeas : ∀ y, AEStronglyMeasurable (fun β => A (c β * R.ι w y) * u β) (lam.restrict 𝓖) := by
    intro y
    have e : (fun β => A (c β * R.ι w y) * u β) = fun β => A (nb β * (x' * R.ι w y)) * u β :=
      funext fun β => by rw [key]
    rw [e]
    exact ((hAc.comp (hnbc.mul continuous_const)).mul huc).aestronglyMeasurable
  have := H.holT.2 d.n pp qq e d.G (R.ι w) (R.cont w) A hAc hA (nA σ d.Y d.b) (lam.restrict 𝓖) c u _ hC
    (fun β => ⟨_, (hγ β).2, rfl⟩) (fun β => (hψ.2.1 _).le) hmeas
  convert this using 2 with y
  simp only [fc]
  congr 1
  funext β
  rw [key]

theorem holCoef_pf (H : Hyps) {d : SD σ} (R : RD d) (L : LD d) (w : InfinitePlace F) {nb lam 𝓖}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b}
    {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (A : d.G → ℂ) (hAc : Continuous A) (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g)
    (pp qq : ℕ) (e : ℤ) (hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) :
    (∀ τ (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w y * x) = Complex.exp (τ * d.m) * fc d.B.ψ d.b nb lam 𝓖 A T x) ∧
    ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ u x, fc d.B.ψ d.b nb lam 𝓖 A T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 A T x := by
  have hc' := hc
  obtain ⟨hN, -, -, -⟩ := hc'
  have hr : ∀ l, betaW d R w T L.i₀ l = 0 := fun l => by
    simp [betaW, SD.cw, Matrix.map_apply, (hT.1 l).1]
  have hcol : ∀ k, betaW d R w T k L.i₀ = 0 := fun k => by
    simp [betaW, SD.cw, Matrix.map_apply, (hT.1 k).2]
  have hchar : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (h : Matrix (Fin d.n) (Fin d.n) ℂ) (xN y : GR d.n),
      h.IsHermitian → mR xN = nU h → fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w (xN * y)) =
        Complex.exp (Complex.I * (betaW d R w T * h).trace) * fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) := by
    intro x' hx' h xN y hh hxN
    obtain ⟨β₁, hι, hBw, hBu, hBf⟩ := nbw1 d R w hN xN h hxN
    rw [map_mul, ← mul_assoc, hx' xN, hι, mul_assoc, KSing.fc_shift d hc A hAi T β₁,
      character_w1_trace_exp d R w T β₁ h hh hBw hBu hBf]
  have hright : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ)
      (xx y : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' → aᴴ * betaW d R w T * a = betaW d R w T →
      fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w (xx * y)) = F0 pp qq e xx * fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) :=
    fun x' hx' => H.holT.1 d.n pp qq e _ (holPhi H R w hc T A hAc hAi pp qq e hA x') (betaW d R w T) (hchar x' hx')
  have hleft : ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ) (xx : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' →
      aᴴ * betaW d R w T * a = betaW d R w T →
      ∀ x, fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w xx * x) = F0 pp qq e xx * fc d.B.ψ d.b nb lam 𝓖 A T x := by
    intro a a' xx hxx hs x
    obtain ⟨x', y₀, rfl, hx'⟩ := decW_pf R w x
    rw [← mul_assoc, ← hx' xx, mul_assoc, ← map_mul, hright x' hx' a a' xx y₀ hxx hs]
  refine ⟨fun τ y hy x => ?_, fun uM ν 𝓤 hu u x => ?_⟩
  · rw [hleft _ _ y hy (stab_diag L.i₀ _ (fun k hk => by simp [Pi.single_eq_of_ne hk]) _ hr hcol) x,
      weight_factor_dilation L.i₀ τ y hy]
    congr 2
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · have h0 := Krd.zeta_ne R.hζ
    refine (H.uEx F E σ d R L).2 uM ν 𝓤 hu w _ (fcCont d hc T A hAc hAi)
      (fun u hu' x => (H.fcConj F E σ d L nb lam 𝓖 hc).2 uM ν 𝓤 hu T T' hT A hAc hAi u hu' x) ?_ u x
    intro u y huy x
    rw [huy]
    obtain ⟨a', ha'⟩ := hu.1 u
    set S := ∑ j, Matrix.single L.i₀ (L.em j) (u j) with hS
    have hne : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
    set M := d.cw w S with hMdef
    have hM : ∀ k l, k ≠ L.i₀ → M k l = 0 := by
      intro k l hk
      simp [hMdef, hS, SD.cw, Matrix.map_apply, Matrix.sum_apply, Ne.symm hk]
    have hM0 : M L.i₀ L.i₀ = 0 := by
      simp [hMdef, hS, SD.cw, Matrix.map_apply, Matrix.sum_apply, hne]
    have hmy : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y)) * dZ d.n R.ζ⁻¹ := by
      rw [KSplitW.cw_iota]
      simp only [← Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.one_mul]
      rw [Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.mul_one]
    rw [← huy, ha'] at hmy
    have hy : mR y = Matrix.fromBlocks (1 + M) 0 0 ((R.ζ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ)) * d.cw w a' *
        (R.ζ⁻¹ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ))) := by
      rw [hmy, hMdef]
      simp [dZ, SD.cw, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_add (f := _)]
    rw [hleft _ _ y hy (stab_row L.i₀ M hM _ hr hcol) x, weight_factor_det_one pp qq e y _ _ hy (det_row L.i₀ M hM hM0), one_mul]

end PositivityTheory.SiegelWeilFormula.AStep

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.HolCoefPf =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DegCut =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DegCut", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FourierZero\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.AvgHolPf\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.COneLawPf\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CntFalse\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DilExPf\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.HolCoefPf\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionEqThetaZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.AStep

end PositivityTheory.SiegelWeilFormula.AStep

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DegCut =====
