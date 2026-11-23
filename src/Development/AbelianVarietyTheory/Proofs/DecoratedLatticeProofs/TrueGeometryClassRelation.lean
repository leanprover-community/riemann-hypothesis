module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.FamTraceChiCol

theorem colLam_ne_zero {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : colLam T v g ≠ 0 := by
  unfold colLam
  split_ifs with h
  · simp only [Formalism.L2.Forms.lamJ, Finset.range_zero, Finset.prod_empty, mul_one]
    intro h0
    have e := (T.gl.psi0 h.choose v h.choose_spec).map_add_eq_mul
      (∑ x : Fin (D.R.N 0), ∑ y : Fin (D.R.N 0), if (x : ℕ) + 1 = y ∧ (y : ℕ) < D.R.k ∧ (y : ℕ) ≠ D.R.k then
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
          (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) x y else 0)
      (-(∑ x : Fin (D.R.N 0), ∑ y : Fin (D.R.N 0), if (x : ℕ) + 1 = y ∧ (y : ℕ) < D.R.k ∧ (y : ℕ) ≠ D.R.k then
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
          (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) x y else 0))
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at e
    exact one_ne_zero e
  · exact one_ne_zero

theorem mem_type_prod_iff {D : D7} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ↔ ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal := by
  rw [Nat.cast_mul, v.isPrime.mul_mem_iff_mem_or_mem, Fin.exists_fin_two]

end GlobalTheory.FamTraceChiCol

end
