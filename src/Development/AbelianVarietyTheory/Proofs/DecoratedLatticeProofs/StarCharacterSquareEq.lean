module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChrMatch

variable {D : D7}

theorem suppAt_conj (e : AE D) (V : HSp D) (a n : GA D V) (hn : Formalism.L2.Theta.SuppAt e V n) :
    Formalism.L2.Theta.SuppAt e V (a * n * a⁻¹) := by
  have h1 : Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 =
      Formalism.L2.Theta.mt V a * (Formalism.L2.Theta.mt V n - 1) * Formalism.L2.Theta.mt V a⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have h2 : (e + cA D e) • (Formalism.L2.Theta.mt V n - 1) = Formalism.L2.Theta.mt V n - 1 := by
    ext i j; exact hn i j
  intro i j
  have h3 : (e + cA D e) • (Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1) = Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 := by
    rw [h1, ← Matrix.smul_mul, ← Matrix.mul_smul, h2]
  exact congrFun (congrFun h3 i) j

theorem levChi_mul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ levS V β L) (hk' : k' ∈ levS V β L) : levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have := (levChar D.sp.cm V.gram β L).map_mul ⟨finE V k, hk.2⟩ ⟨finE V k', hk'.2⟩
  unfold levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg Units.val this

theorem levChi_of_red_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (hs : L.s = 0)
    (hQ : L.Q = ∅) {k : GA D V} (hk : ∀ PP ∈ L.Pg, redFn β PP (finE V k) = 1) : levChi V β L k = 1 := by
  have h1 : rTup β L (finE V k) = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1
    rw [hk PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, hs, hQ]
  simp

end GlobalTheory.ChrMatch

end
