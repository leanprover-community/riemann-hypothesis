module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateBlockUpperOfEigenfunctionUnipotentType
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

theorem _root_.GlobalTheory.T.conjugate_blockUpper_of_eigenfunction_unipotentType : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {n r t : ℕ}, n = r + t → 2 ≤ r →
    ∀ (s : ReciprocityTheory.Aut.SplitPlace E) {k : Type} [Field k] (φ : GlobalTheory.CenFrame.Os s →+* k), GlobalTheory.CenFrame.IsResidue s φ →
    (∃ c : k, c ≠ 0 ∧ c ≠ 1) → ∀ (f : Formalism.AUTREP.GAf E n → ℂ), f ≠ 0 →
    ∀ (J : Subgroup (Formalism.AUTREP.GAf E n)) (χ : J →* ℂˣ)
    (ψ₀ : AddChar (s.v.adicCompletion (NumberField.maximalRealSubfield E)) ℂ)
    (ξ : (s.v.adicCompletion (NumberField.maximalRealSubfield E))ˣ →* ℂˣ),
    Formalism.L2.NG.IsPsi0 s ψ₀ → Formalism.L2.NG.LevelUni J χ s r ψ₀ ξ →
    (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) →
    ∀ (b : GL (Fin n) k),
    (∀ κ ∈ ReciprocityTheory.Aut.Umax E n, ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ y : GL (Fin n) (GlobalTheory.CenFrame.Os s),
        GlobalTheory.CenFrame.IsCompOf s κ y →
      ((∀ i j : Fin n, (r ≤ i.val → j.val < r → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < r → j.val < i.val → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < r → i = j → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 1)) →
        ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
      (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g)) →
    b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  first | exact @GlobalTheory.CenFrameGen.block_upper_of_eigen | exact GlobalTheory.CenFrameGen.block_upper_of_eigen | (intros; apply GlobalTheory.CenFrameGen.block_upper_of_eigen <;> assumption)
