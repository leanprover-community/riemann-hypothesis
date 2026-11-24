module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SplitPrimeIdeals
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSplitExactSequence
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroup, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PadZeroMemNilradical

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroup =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroup", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.SiegelWeilFormula

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelRadTop

theorem nA_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
    (∀ β : Matrix (Fin n) (Fin n) (AE F E), β ∈ nA σ Y b ↔ βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0) →
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) ∧ IsTopologicalAddGroup (nA σ Y b) ∧
    LocallyCompactSpace (nA σ Y b) ∧ SecondCountableTopology (nA σ Y b) ∧ T2Space (nA σ Y b) ∧ BorelSpace (nA σ Y b) := by
  intro F E _ _ _ _ _ σ n Y b ε h
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  have hc : Continuous (cA σ) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  have hS : (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) =
      {β | βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0} := Set.ext h
  have hC : IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) := by
    rw [hS]
    have h1 : Continuous fun β : Matrix (Fin n) (Fin n) (AE F E) => β.map (cA σ) := continuous_id.matrix_map hc
    have h2 : Continuous fun β : Matrix (Fin n) (Fin n) (AE F E) => ((ε : ℤ) : AE F E) • β.map (cA σ) :=
      (continuous_const_smul (((ε : ℤ) : AE F E))).comp h1
    exact isClosed_eq (continuous_id.matrix_transpose.add h2) continuous_const
  haveI : LocallyCompactSpace (nA σ Y b) := hC.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (nA σ Y b) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact ⟨hC, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.CompanionTheory.SiegelRadTop
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroup =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PadZeroMemNilradical =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PadZeroMemNilradical", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SplitPrimeIdeals\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroup\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Analysis.InnerProductSpace.Basic\npublic import Mathlib.MeasureTheory.Group.FundamentalDomain\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSplitExactSequence\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

def pad0 (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then β h.1.choose h.2.choose else 0

theorem pad_zero_embedding_alt (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (a c : Fin L.n) : pad0 L β (L.em a) (L.em c) = β a c := by
  have h : (∃ a', L.em a' = L.em a) ∧ ∃ c', L.em c' = L.em c := ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩
  simp only [pad0, dif_pos h]
  rw [L.inj h.1.choose_spec, L.inj h.2.choose_spec]

theorem pad_zero_outside_range (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i k : Fin d.n)
    (h : ¬ ((∃ a, L.em a = i) ∧ ∃ c, L.em c = k)) : pad0 L β i k = 0 := by
  simp only [pad0, dif_neg h]

theorem pad_zero_symm_cases (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (P : AE F E → AE F E → Prop) (h0 : P 0 0)
    (h1 : ∀ a c, P (β a c) (β c a)) (i k : Fin d.n) : P (pad0 L β i k) (pad0 L β k i) := by
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    rw [pad_zero_embedding_alt, pad_zero_embedding_alt]
    exact h1 a c
  · rw [pad_zero_outside_range L β i k h, pad_zero_outside_range L β k i (fun h' => h ⟨h'.2, h'.1⟩)]
    exact h0

theorem eps_common : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := Afc.eps_eq L hε hε'
  subst hee
  exact ⟨ε, hε, hε'⟩

theorem pad_zero_mem_nilradical (β : nA σ L.Y L.b) : pad0 L β.1 ∈ nA σ d.Y d.b := by
  obtain ⟨ε, hε, hε'⟩ := eps_common L
  rw [kunf.mem_nA_iff hε]
  have hβ := (kunf.mem_nA_iff hε' β.1).1 β.2
  ext i k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply]
  refine pad_zero_symm_cases L β.1 (fun u v => v = -((((ε : ℤ) : AE F E)) • cA σ u)) (by simp) (fun a c => ?_) i k
  have := congrFun (congrFun hβ a) c
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] using this

def padN : nA σ L.Y L.b →+ nA σ d.Y d.b where
  toFun β := ⟨pad0 L β.1, pad_zero_mem_nilradical L β⟩
  map_zero' := by
    apply Subtype.ext
    ext i k
    refine pad_zero_symm_cases L (0 : nA σ L.Y L.b).1 (fun u _ => u = (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k) rfl
      (fun a c => rfl) i k
  map_add' β β' := by
    apply Subtype.ext
    ext i k
    by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
    · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
      simp only [AddSubgroup.coe_add, Matrix.add_apply, pad_zero_embedding_alt]
    · simp only [AddSubgroup.coe_add, Matrix.add_apply, pad_zero_outside_range L _ i k h, add_zero]

theorem prj_padN (β : nA σ L.Y L.b) : prj L (padN L β) = β := by
  apply Subtype.ext
  ext a c
  simp only [prj_val, Matrix.submatrix_apply]
  exact pad_zero_embedding_alt L β.1 a c

theorem continuous_padN : Continuous (padN L) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun k => ?_
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    simp only [pad_zero_embedding_alt]
    exact (continuous_apply c).comp ((continuous_apply a).comp continuous_subtype_val)
  · simp only [pad_zero_outside_range L _ i k h]
    exact continuous_const

theorem countable_nF (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) : Countable (nF σ Y b) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  refine Function.Injective.countable (f := fun ν : nF σ Y b => Classical.choose (kunf.mem_nF_iff.1 ν.2)) ?_
  intro ν ν' h
  have h1 := Classical.choose_spec (kunf.mem_nF_iff.1 ν.2)
  have h2 := Classical.choose_spec (kunf.mem_nF_iff.1 ν'.2)
  apply Subtype.ext; apply Subtype.ext
  rw [h1, h2]
  exact congrArg _ h

theorem prj_nF {β : nA σ d.Y d.b} (h : β ∈ nF σ d.Y d.b) : prj L β ∈ nF σ L.Y L.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩
  rw [prj_val, hT]
  rfl

theorem padN_nF {β : nA σ L.Y L.b} (h : β ∈ nF σ L.Y L.b) : padN L β ∈ nF σ d.Y d.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨Matrix.of fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then
    T h.1.choose h.2.choose else 0, ?_⟩
  ext i k
  show pad0 L β.1 i k = _
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · rw [pad0, dif_pos h, hT]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_pos h]
  · rw [pad0, dif_neg h]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_neg h, map_zero]

theorem nA_inst (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (hε : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    LocallyCompactSpace (nA σ Y b) ∧ T2Space (nA σ Y b) := by
  have h := _root_.GlobalTheory.CompanionTheory.SiegelRadTop.nA_top F E σ n Y b ε (fun β => by
    rw [kunf.mem_nA_iff hε, ← sub_eq_zero, sub_neg_eq_add])
  exact ⟨h.2.2.1, h.2.2.2.2.1⟩

theorem fiber {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)}
    {𝓖' : Set (nA σ L.Y L.b)} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (G : nA σ L.Y L.b → ℂ) (hG : Continuous G) (hper : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β') :
    ∫ β in 𝓖, G (prj L β) ∂lam = ∫ β' in 𝓖', G β' ∂lam' := by
  obtain ⟨ε, hε, hε'⟩ := eps_common L
  obtain ⟨h1, h2⟩ := nA_inst d.n d.Y d.b ε hε
  obtain ⟨h3, h4⟩ := nA_inst L.n L.Y L.b ε hε'
  exact _root_.GlobalTheory.CompanionTheory.FiberInt.integral_comp_eq (prj L) (padN L) (continuous_prj L) (continuous_padN L) (prj_padN L)
    (nF σ d.Y d.b) (nF σ L.Y L.b) (countable_nF _ _ _) (countable_nF _ _ _) (fun γ hγ => prj_nF L hγ)
    (fun γ hγ => padN_nF L hγ) lam lam' hc.2.1 hc'.2.1 𝓖 𝓖' hc.2.2.1 hc.2.2.2 hc'.2.2.1 hc'.2.2.2 G hG
    (fun γ hγ x => hper γ hγ x)

end PositivityTheory.SiegelWeilFormula.Act.C4

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PadZeroMemNilradical =====
