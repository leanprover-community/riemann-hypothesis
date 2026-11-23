module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundOfHyp
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSubsingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open GlobalTheory.RowClaim GlobalTheory.ArchTens ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
namespace GlobalTheory.ArchTens.VolSize
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
theorem archimedean_tensor_volume_coefficient : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => CoefAt ch C := by
  intro _
  refine ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ => by
      have hL := s.core.lev
      have hde := Test.pde_ne_q s
      rintro Φ β hβ ⟨P, hl⟩
      have hP : P ∈ ch.G.pl.W0 := by
        classical
        rcases Finset.mem_union.1 hl with h | h
        · exact h
        · exact absurd h (fun hP => (hL.Q_ram A.μ0 P).2 (Or.inl hP) (by rw [hL.xi_base]; exact fun _ _ => rfl))
      exact (coef_le_of_chosen hL ch.S.toGridChoice A.μ0 Φ hde (GlobalTheory.RowTest.guard_of_qGuard s.guard A.μ0) hP hl hβ).trans
        (Real.exp_le_exp.2 (exponent_le P hC))⟩⟩⟩

end GlobalTheory.ArchTens.VolSize
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens

theorem _root_.GlobalTheory.T.archimedean_tensor_volume_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => CoefAt ch C := by
  exact @_root_.GlobalTheory.ArchTens.VolSize.archimedean_tensor_volume_coefficient
end
