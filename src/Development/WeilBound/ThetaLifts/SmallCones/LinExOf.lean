module

public import Development.WeilBound.ThetaLifts.SmallCones.SoDefs
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsUnitDetOfCartan
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KdMulRight
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LmOfLinBar
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictMod
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictSec
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.EqZeroOfLocW

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKCT

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo

theorem linEx_of : LinEx := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW v t
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm v t
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have uu : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E}, IsUnit J.det → IsUnit ((incM F J).map (piW t)) := fun {m J} hJ => by
    rw [incM_map h]
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).map (t : E →+* Fv F v).mapMatrix
  have hG : Grams σ t (incM F X.J) (incM F W.J) := by
    refine ⟨uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) X.J (B.emb w).1 1 (X.θ w) (by rw [one_smul]; exact hX.cartan w)),
      uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) W.J (B.emb w).1 Complex.I (W.θ w) (hW.cartan w)), 1, one_mul _,
      Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · rw [incM_map' h, incM_map h, one_smul, hX.herm]; rfl
    · rw [incM_map' h, incM_map h, neg_smul, one_smul, hW.skew, map_neg]; rfl
  obtain ⟨ι₀, hι₀⟩ := exists_lm model_existence adjoint_statement hB.std h hG M.co
  refine ⟨⟨_, linBar_of_lm adjoint_statement action_uniqueness h hG hι₀⟩, fun x u hx h0 => ?_⟩
  rw [sy, symp_eq h hG hx, ev_sgl, coord_snd.2 h0, dotProduct_zero, sub_zero]
  simp only [coord, dot_ofM, incM_map h, Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

end PositivityTheory.ThKCT

end
