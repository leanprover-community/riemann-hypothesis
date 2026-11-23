module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut

namespace Formalism.L2.SG.Pf

theorem foldOKC_holds_of (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u)
    (hU : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), IUnfold X u hK) :
    Formalism.L2.SG.Full.FoldOKC := by
  intro D X Y u hKL hW
  exact foldOK_of_steps X u Y.hK hKL (foldReadyX_holds X) (hS D X u) (hN D X u) (hL D X u) (hP D X u) hW
    (sratFund_holds X u) (Formalism.L2.SG.Closed.MultPoly_holds X) (hU D X u Y.hK)

theorem inHHC_holds_of (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u)
    (hFB : ∀ (D : D7) (X : HidaSetting D), FundBridge X)
    (hPM : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), PserMeas X u hK)
    (hRph : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), PserRph X u hK)
    (hRF : ∀ (D : D7) (X : HidaSetting D), ArchimedeanConvolutionFixesInvariantL2 X) (hEF : ∀ (D : D7) (X : HidaSetting D), IdempotentFixesInvariantL2 X) :
    Formalism.L2.SG.Full.InHHC := by
  intro D X Y u hI hOK
  have hR := foldReadyX_holds X
  have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
  exact inHH_of X u Y.hK hR
    (@Formalism.L2.SG.Closed.fold_L2_first X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    (@Formalism.L2.SG.Closed.fold_L2_second X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    (hFB D X) hOK (phProps_closed X u Y.hK (hS D X u) (hN D X u) (hL D X u) (hP D X u))
    (poincare_well_defined X u Y.hK (hS D X u) (hN D X u)) (hPM D X u Y.hK) (hRph D X u Y.hK) hI (hRF D X) (hEF D X)
    hKL (level_subgroup_measurable X Y.hK hKL)

theorem inHHC_holds_of' (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u)
    (hRph : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), PserRph X u hK) :
    Formalism.L2.SG.Full.InHHC :=
  inHHC_holds_of hS hN hL hP (fun _ X => fundBridge_holds X) (fun _ X u hK => pserMeas_holds X u hK) hRph
    (fun _ X => regular_fixes_invariant_L2 X) (fun _ X => idempotent_fixes_invariant_L2 X)

theorem inHHC_holds_of'' (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u) :
    Formalism.L2.SG.Full.InHHC :=
  inHHC_holds_of' hS hN hL hP fun _ X u hK => pserRph_holds X u hK

theorem inHHC_holds : Formalism.L2.SG.Full.InHHC :=
  inHHC_holds_of'' (fun _ X u => ksetSplit_holds X u) (fun _ X u => unipotent_in_level X u)
    (fun _ X u => ratLevi_holds X u) (fun _ X u => psiProd_holds X u)

end Formalism.L2.SG.Pf
