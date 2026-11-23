module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

noncomputable section

namespace GlobalTheory.MixModel.HypDec

variable {D : D7}

theorem gram_mt {S : HSp D} (g : GA D S) {k l : ℕ} (x : Mx D S.rank k) (y : Mx D S.rank l) :
    adj (mt S g ⬝ x) ⬝ (gA S ⬝ (mt S g ⬝ y)) = adj x ⬝ (gA S ⬝ y) := by
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)),
    mt_unitary]

theorem exists_emb0_eq_of_fix_jX_jY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S)
    (hX : mt S g ⬝ d.jX = d.jX) (hY : mt S g ⬝ d.jY = d.jY) : ∃ b : GA D S₀, d.emb0 b = g := by
  set M := mt S g with hM
  set B := d.p0 ⬝ M ⬝ d.j0 with hB
  have h1 : d.pX ⬝ M ⬝ d.j0 = 0 := by
    rw [pX_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hY, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) M,
      ← Matrix.mul_assoc (adj M), mt_unitary, gramR_Y0_eq_TI]
  have h2 : d.pY ⬝ M ⬝ d.j0 = 0 := by
    rw [pY_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hX, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) M,
      ← Matrix.mul_assoc (adj M), mt_unitary, wittDecomp_gram_X_anisotropic]
  have h3 : M ⬝ d.j0 = d.j0 ⬝ B := by
    rw [Matrix.mul_assoc] at h1 h2
    rw [← Matrix.one_mul (M ⬝ d.j0), ← d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, add_zero, zero_add, hB]
  have h4 : adj B * (gA S₀ * B) = gA S₀ := by
    have e1 := gram_mt g d.j0 d.j0
    rw [← hM, h3, d.gram_00, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj d.j0),
      ← Matrix.mul_assoc (adj d.j0), Matrix.mul_assoc (adj d.j0), d.gram_00] at e1
    exact e1
  refine ⟨ofMat S₀ B h4, d.ga_ext ?_ ?_ ?_⟩
  · rw [wittDecomp_anisotropicEmbedding_inclX, ← hM, hX]
  · rw [wittDecomp_anisotropicEmbedding_inclAnisotropic, mt_ofMat, ← hM, h3]
  · rw [wittDecomp_anisotropicEmbedding_inclY, ← hM, hY]

end GlobalTheory.MixModel.HypDec

end
