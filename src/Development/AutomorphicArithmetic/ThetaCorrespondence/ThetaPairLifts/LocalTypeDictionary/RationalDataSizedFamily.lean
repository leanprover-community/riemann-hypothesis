module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Params
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormNormEqAtConjugateEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealDataWeightVectorFamilyCore
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

@[expose] public section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
theorem GlobalTheory.PrimIn.holds_of_ties_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (X : GlobalTheory.Mem.Stages) (px : GlobalTheory.Mem.PreX X.B.toPre) (I : GlobalTheory.Mem.Col2.ColIn X.B px) (hX : X.B.fields.Ok) (Tw : GlobalTheory.Mem.Top.TwDat X.B) (Wt : Set X.B.places.Pl) (z : GlobalTheory.Mem.R3.Dat X I hX Tw Wt) (L : SizeData₂ X.toD7), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → TiesB z.R z.F → TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O → GlobalTheory.CuspMult.MultEq z.R.toRealDat → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) → z.R.toRealDat.LIntegral → GlobalTheory.Mem.R3.Holds z.R z.F := by
  intro hP hHL eps heps
  obtain ⟨x₀, hx⟩ := _root_.GlobalTheory.T.real_data_weight_vector_family_core_alt hP hHL eps heps
  refine ⟨x₀, ?_⟩
  intro X px I hX Tw Wt z L hLe hx0 hS hPar hB hG hM hRT hI
  have h := hx z.core z.R z.F z.geo.κ z.geo.v₀ z.geo.O L hLe hx0 hS hPar hB hG hM hRT
  obtain ⟨hcore, -, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak z.R z.F hB.char hB.ex
  have hschur := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP.q2 z.R.toRealDat
  obtain ⟨fw, hbar⟩ := hG.fw
  have hconj := GlobalTheory.T.algebraicForm_norm_eq_at_conjugateEmbedding z.core z.R.toRealDat z.F.lv2 z.geo.κ z.geo.v₀ hcore hschur fw hbar hG.unif
  have hlev : z.R.toRealDat.LLevelW z.F.lv2 :=
    GlobalTheory.LevelForms.levelW_of_irr _ _ hB.ok.ok2.irr hG.unif hB.char.base.models.HW
  exact ⟨h.1, ⟨hB.ex, hconj, hlev, hI⟩, hB.ok, h.2.1⟩
end

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_data_sized_family_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (X : GlobalTheory.Mem.Stages) (px : GlobalTheory.Mem.PreX X.B.toPre) (I : GlobalTheory.Mem.Col2.ColIn X.B px) (hX : X.B.fields.Ok) (Tw : GlobalTheory.Mem.Top.TwDat X.B) (Wt : Set X.B.places.Pl) (z : GlobalTheory.Mem.R3.Dat X I hX Tw Wt) (L : SizeData₂ X.toD7), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → TiesB z.R z.F → TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O → GlobalTheory.CuspMult.MultEq z.R.toRealDat → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) → z.R.toRealDat.LIntegral → GlobalTheory.Mem.R3.Holds z.R z.F := by
  first | exact @_root_.GlobalTheory.PrimIn.holds_of_ties_alt | exact _root_.GlobalTheory.PrimIn.holds_of_ties_alt | (intros; apply _root_.GlobalTheory.PrimIn.holds_of_ties_alt <;> assumption)
end
