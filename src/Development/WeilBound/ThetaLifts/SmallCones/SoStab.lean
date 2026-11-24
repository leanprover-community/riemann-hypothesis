module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement
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

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKCT.So

open NumberField GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_of_map (B : Base F E) (w : InfinitePlace F) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (hJ : (J.map (B.emb w).1).det ≠ 0) : J.det ≠ 0 := fun h0 =>
  hJ (((RingHom.map_det _ J).symm.trans (congrArg _ h0)).trans (map_zero _))

theorem det_herm {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_ne_of_map B w _ (GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w))

theorem det_skew {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_ne_of_map B w _ fun h0 =>
    GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w) (by rw [Matrix.det_smul, h0, mul_zero])

theorem _root_.PositivityTheory.ThKCT.soStab_of : SoStab := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP x
  exact PositivityTheory.KCo.so_stable M hP.base.cm hP.base.std (det_herm hP.herm) (det_skew hP.skew) hP.good
    (IsUWeilPair.isUSplitting hP.weil).toIsSplitting B.τ₁ x

end PositivityTheory.ThKCT.So

end
