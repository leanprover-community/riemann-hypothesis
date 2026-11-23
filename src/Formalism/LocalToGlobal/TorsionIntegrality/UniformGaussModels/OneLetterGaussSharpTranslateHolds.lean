module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthShapeOne
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.PairsK
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KappaIntegralOfCalculation
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NeZeroOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormLeOneOfQuad
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaKappaShapeOfTransferIntegrality
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.Th1.Top

theorem calcC : CalcC := CalcC_proof
theorem cmDatum : CMDatum := CMDatum_proof
theorem jetsCM : JetsCM := JetsCM_of cmDatum
theorem calcP : CalcP := CalcP_of cmDatum
theorem kappa_integral : uniformGaussModelConditionReformulated := kappa_integral_of_calculation calcC
theorem hypShape : HypShape := HypShape_of calcC



variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem modelInert (dK : ℕ) (L : PeriodPair) (hsq : Squarefree dK) (hmod : dK % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) (hd : ¬ l ∣ dK)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (ι : ℂ ≃+* ℂ_[l]) :
    ∃ g2 g3 ε : Formalism.L2.Th1.CM.MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 ∧ ‖ε‖ = 1 ∧
      ∀ n, ‖PowerSeries.coeff n (Formalism.L2.Th1.D.thetaS l g2 g3 ε)‖ ≤ 1 :=
  Formalism.L2.Th1.D.FAux.model l Formalism.L2.Th1.CM.cm2 Formalism.L2.Th1.CM.cm3 dK L hsq hmod hcm h5 hd hin ι



theorem ltNormExists : LTNormExists := lubin_tate_norm_exists
theorem transIntLT : TransIntLT := lubin_tate_transfer_integral
theorem local_kappa_shape_holds : uniformGaussModelConditionReformulated₂ := local_kappa_shape_of_transfer_integrality transIntLT
theorem theta_kappa_shape_holds : uniformGaussModelConditionEquivalent := theta_kappa_shape_of_transfer_integrality transIntLT

end Formalism.L2.Th1.Top
