module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationSplitUnitarySchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryWeilRepresentationIsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationIntertwinesHeisenbergStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesL2SpaceStatement
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem kudlaSplittingSplitUnitary : GlobalTheory.Published.KudlaSplittingSplitUnitary := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α ν _ _ _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres
  letI : MeasurableSpace (Matrix α ν E) := borel _
  haveI : BorelSpace (Matrix α ν E) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨-, hG⟩ := hmat α ν
  haveI := hG.grp
  haveI := hG.t2
  haveI := hG.lc
  haveI := hG.sc
  obtain ⟨κ, ω, hKW⟩ := GlobalTheory.T.exists_weil_representation_split_unitary_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres (Measure.addHaar)
  refine ⟨ω, GlobalTheory.T.splitUnitaryWeilRepresentation_isSmooth F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW, ?_,
    GlobalTheory.T.weilRepresentation_intertwines_heisenberg F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW, ?_⟩
  · intro μ' hμ' g φ
    exact GlobalTheory.T.weil_representation_preserves_L2_space F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW μ' g φ
  · intro a φ x
    have hp : levi c hE.invol a ∈ sieg c ν := by
      rw [mem_sieg, mat, levi_val, toBlocks_fromBlocks₂₁]
    rw [hKW.par _ hp φ]
    have h0 : ∀ y : Matrix α ν E, pr c Q y 0 = 0 := fun y => by
      simp [pr, form, GlobalTheory.WeilM.hTens]
    obtain ⟨-, -, hsc, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
    have hd := hsc (Matrix.GeneralLinearGroup.det a)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hd
    simp only [parFun, mat, levi_val, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.mul_zero, h0,
      mul_zero, AddChar.map_zero_eq_one, one_mul, hd]

end GlobalTheory
